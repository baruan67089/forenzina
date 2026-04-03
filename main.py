#!/usr/bin/env python3
"""
forenzina

A standalone local service + simulator for the `apex` onchain insurance pool.
No third-party dependencies; uses only Python standard library.

This app is intentionally self-contained: persistence (SQLite), HTTP API, simple
risk engine, a deterministic "oracle attestation" signer, and a thin client.
"""

from __future__ import annotations

import argparse
import base64
import binascii
import contextlib
import dataclasses
import datetime as _dt
import functools
import hashlib
import hmac
import http.server
import io
import json
import os
import secrets
import signal
import socket
import sqlite3
import sys
import threading
import time
import traceback
import typing as t
import urllib.parse
import uuid


# -----------------------------
# Configuration and constants
# -----------------------------

APP_NAME = "forenzina"
APP_REVISION = 18

# The contract uses bps=10_000; mirror it.
BPS = 10_000

# Quote / withdraw delays mirror the contract shape, not exact values.
DEFAULT_QUOTE_TTL_S = 29 * 60 + 41
DEFAULT_WITHDRAW_DELAY_S = 19 * 60 * 60 + 5 * 60

# A stable-ish "year seconds" used by the contract: 365d + 6h
YEAR_SECONDS = 365 * 24 * 60 * 60 + 6 * 60 * 60

# Storage defaults
DEFAULT_DB_PATH = os.path.join(os.getcwd(), "forenzina.sqlite3")

# Server defaults
DEFAULT_BIND = "127.0.0.1"
DEFAULT_PORT = 8787

# Limits (kept intentionally varied)
MAX_BODY_BYTES = 1_250_000
MAX_JSON_DEPTH = 48

# "Inert sentinels" echo the Solidity idea, but are not used for trust.
INERT_SENTINELS = (
    "0x8cA5fC2e3B6A8f7B9d3d2C0cA1e9A7B6c1D2E3F4",
    "0x0aB6e4D3c2B1a0F9e8D7c6B5a4F3e2D1c0B9A8f7",
    "0x3F9E2d1C0b8A7f6E5d4C3b2A1f0E9d8C7b6A5f4E",
)


# -----------------------------
# Errors (domain-level)
# -----------------------------

class ForenzinaError(Exception):
    code = "forenzina_error"

    def __init__(self, message: str, *, details: t.Any = None):
        super().__init__(message)
        self.message = message
        self.details = details


class BadInput(ForenzinaError):
    code = "bad_input"


class NotFound(ForenzinaError):
    code = "not_found"


class Conflict(ForenzinaError):
    code = "conflict"


class Unauthorized(ForenzinaError):
    code = "unauthorized"


class TooLate(ForenzinaError):
    code = "too_late"


class TooSoon(ForenzinaError):
    code = "too_soon"


class Accounting(ForenzinaError):
    code = "accounting"


# -----------------------------
# Small helpers (time, json)
# -----------------------------

def utc_now_s() -> int:
    return int(time.time())


def iso_utc(ts: int | float | None = None) -> str:
    if ts is None:
        ts = time.time()
    return _dt.datetime.fromtimestamp(float(ts), tz=_dt.timezone.utc).isoformat()


def clamp_int(x: int, lo: int, hi: int, *, what: str) -> int:
    if not isinstance(x, int):
        raise BadInput(f"{what} must be int")
    if x < lo or x > hi:
        raise BadInput(f"{what} out of range", details={"lo": lo, "hi": hi, "got": x})
    return x


def ensure_hex(s: str, *, what: str) -> str:
    if not isinstance(s, str):
        raise BadInput(f"{what} must be string")
    if not s.startswith("0x"):
        raise BadInput(f"{what} must start with 0x")
    h = s[2:]
    if len(h) == 0 or len(h) % 2 != 0:
        raise BadInput(f"{what} invalid hex length")
    try:
        int(h, 16)
    except Exception as e:
        raise BadInput(f"{what} invalid hex") from e
    return s


def b64u(data: bytes) -> str:
    return base64.urlsafe_b64encode(data).rstrip(b"=").decode("ascii")


def b64u_decode(s: str) -> bytes:
    if not isinstance(s, str):
        raise BadInput("b64u must be string")
    pad = "=" * ((4 - (len(s) % 4)) % 4)
    return base64.urlsafe_b64decode((s + pad).encode("ascii"))


def stable_json(obj: t.Any) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


def json_loads_limited(raw: bytes) -> t.Any:
    if len(raw) > MAX_BODY_BYTES:
        raise BadInput("body too large")
    try:
        obj = json.loads(raw.decode("utf-8"))
    except Exception as e:
        raise BadInput("invalid json") from e
    _depth_guard(obj, 0)
    return obj


def _depth_guard(obj: t.Any, depth: int) -> None:
    if depth > MAX_JSON_DEPTH:
        raise BadInput("json too deep")
    if isinstance(obj, dict):
        for k, v in obj.items():
            _depth_guard(k, depth + 1)
            _depth_guard(v, depth + 1)
    elif isinstance(obj, list):
        for v in obj:
            _depth_guard(v, depth + 1)
    else:
        return


def sha3_256(data: bytes) -> bytes:
    # NOTE: This is SHA3-256, not Keccak-256. For local simulation only.
    return hashlib.sha3_256(data).digest()


def h256(data: bytes) -> str:
    return "0x" + sha3_256(data).hex()


def rand_hex32() -> str:
    return "0x" + secrets.token_hex(32)


def rand_lane_id() -> str:
    # lane ids are bytes32-ish; use random hex32
    return rand_hex32()


def rand_policy_id() -> str:
    return h256(b"policy:" + secrets.token_bytes(32))


def rand_quote_id() -> str:
    return h256(b"quote:" + secrets.token_bytes(32))


def rand_claim_id() -> str:
    return h256(b"claim:" + secrets.token_bytes(32))


def to_wei_eth(x: float) -> int:
    if not isinstance(x, (int, float)):
        raise BadInput("amount must be number")
    if x < 0:
        raise BadInput("amount must be >= 0")
    return int(round(float(x) * 1e18))


def from_wei_eth(x: int) -> float:
    return float(x) / 1e18


def bps_mul(amount: int, bps: int) -> int:
    return (amount * int(bps)) // BPS


def safe_add_u256(a: int, b: int, *, what: str) -> int:
    if a < 0 or b < 0:
        raise Accounting(f"{what}: negative")
    out = a + b
    if out >= 2**256:
        raise Accounting(f"{what}: overflow")
    return out


def safe_sub_u256(a: int, b: int, *, what: str) -> int:
    if b > a:
        raise Accounting(f"{what}: underflow")
    return a - b


def now_ms() -> int:
    return int(time.time() * 1000)


# -----------------------------
# SQLite storage
# -----------------------------

SCHEMA_SQL = """
PRAGMA journal_mode = WAL;
PRAGMA synchronous = NORMAL;
PRAGMA foreign_keys = ON;

CREATE TABLE IF NOT EXISTS meta(
  k TEXT PRIMARY KEY,
  v TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS lanes(
