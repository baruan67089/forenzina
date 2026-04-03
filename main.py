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
