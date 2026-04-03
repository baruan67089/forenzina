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
  lane_id TEXT PRIMARY KEY,
  enabled INTEGER NOT NULL,
  capacity_wad INTEGER NOT NULL,
  used_wad INTEGER NOT NULL,
  min_premium_wad INTEGER NOT NULL,
  max_duration_s INTEGER NOT NULL,
  deductible_bps INTEGER NOT NULL,
  grace_bps INTEGER NOT NULL,
  created_at_s INTEGER NOT NULL,
  updated_at_s INTEGER NOT NULL
);

CREATE TABLE IF NOT EXISTS quotes(
  quote_id TEXT PRIMARY KEY,
  buyer TEXT NOT NULL,
  lane_id TEXT NOT NULL,
  cover_wei INTEGER NOT NULL,
  start_at_s INTEGER NOT NULL,
  end_at_s INTEGER NOT NULL,
  created_at_s INTEGER NOT NULL,
  expires_at_s INTEGER NOT NULL,
  salt INTEGER NOT NULL,
  consumed INTEGER NOT NULL,
  FOREIGN KEY(lane_id) REFERENCES lanes(lane_id)
);

CREATE TABLE IF NOT EXISTS policies(
  policy_id TEXT PRIMARY KEY,
  quote_id TEXT NOT NULL,
  holder TEXT NOT NULL,
  lane_id TEXT NOT NULL,
  cover_wei INTEGER NOT NULL,
  premium_wei INTEGER NOT NULL,
  fee_wei INTEGER NOT NULL,
  start_at_s INTEGER NOT NULL,
  end_at_s INTEGER NOT NULL,
  bound_at_s INTEGER NOT NULL,
  state TEXT NOT NULL,
  nonce INTEGER NOT NULL,
  FOREIGN KEY(quote_id) REFERENCES quotes(quote_id),
  FOREIGN KEY(lane_id) REFERENCES lanes(lane_id)
);

CREATE TABLE IF NOT EXISTS claims(
  claim_id TEXT PRIMARY KEY,
  policy_id TEXT NOT NULL,
  holder TEXT NOT NULL,
  loss_ref TEXT NOT NULL,
  filed_at_s INTEGER NOT NULL,
  state TEXT NOT NULL,
  payout_wei INTEGER NOT NULL,
  verdict_hash TEXT NOT NULL,
  attested_at_s INTEGER NOT NULL,
  paid_at_s INTEGER NOT NULL,
  void_reason TEXT NOT NULL,
  FOREIGN KEY(policy_id) REFERENCES policies(policy_id)
);

CREATE TABLE IF NOT EXISTS ledger(
  entry_id TEXT PRIMARY KEY,
  kind TEXT NOT NULL,
  at_s INTEGER NOT NULL,
  ref TEXT NOT NULL,
  amount_wei INTEGER NOT NULL,
  memo TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS credits(
  who TEXT PRIMARY KEY,
  amount_wei INTEGER NOT NULL,
  updated_at_s INTEGER NOT NULL
);

CREATE TABLE IF NOT EXISTS oracle_state(
  k TEXT PRIMARY KEY,
  v TEXT NOT NULL
);
"""


class Store:
    def __init__(self, path: str):
        self.path = path
        self._lock = threading.RLock()
        self._conn = sqlite3.connect(self.path, check_same_thread=False, isolation_level=None)
        self._conn.row_factory = sqlite3.Row
        with self._conn:
            self._conn.executescript(SCHEMA_SQL)
        self._boot_meta()

    def close(self) -> None:
        with self._lock:
            self._conn.close()

    @contextlib.contextmanager
    def tx(self) -> t.Iterator[sqlite3.Connection]:
        with self._lock:
            cur = self._conn.cursor()
            cur.execute("BEGIN IMMEDIATE")
            try:
                yield self._conn
                cur.execute("COMMIT")
            except Exception:
                cur.execute("ROLLBACK")
                raise

    def _boot_meta(self) -> None:
        with self.tx() as db:
            db.execute("INSERT OR IGNORE INTO meta(k, v) VALUES(?,?)", ("app_name", APP_NAME))
            db.execute("INSERT OR IGNORE INTO meta(k, v) VALUES(?,?)", ("app_revision", str(APP_REVISION)))
            db.execute("INSERT OR IGNORE INTO meta(k, v) VALUES(?,?)", ("created_at", iso_utc()))
            db.execute("INSERT OR IGNORE INTO meta(k, v) VALUES(?,?)", ("genesis_tag", rand_hex32()))
            db.execute("INSERT OR IGNORE INTO meta(k, v) VALUES(?,?)", ("quote_ttl_s", str(DEFAULT_QUOTE_TTL_S)))
            db.execute("INSERT OR IGNORE INTO meta(k, v) VALUES(?,?)", ("withdraw_delay_s", str(DEFAULT_WITHDRAW_DELAY_S)))
            # pool accounting
            for k, v in (
                ("available_capital_wei", "0"),
                ("reserved_capital_wei", "0"),
                ("total_premiums_wei", "0"),
                ("total_claims_paid_wei", "0"),
                ("protocol_fee_bps", "219"),
                ("reserve_factor_bps", "6431"),
                ("max_slippage_bps", "71"),
                ("treasury", "0x" + secrets.token_hex(20)),
                ("oracle", "0x" + secrets.token_hex(20)),
            ):
                db.execute("INSERT OR IGNORE INTO meta(k, v) VALUES(?,?)", (k, v))
            db.execute("INSERT OR IGNORE INTO oracle_state(k, v) VALUES(?,?)", ("nonce", "0"))
            # a signing key for local attestation (HMAC secret)
            db.execute("INSERT OR IGNORE INTO oracle_state(k, v) VALUES(?,?)", ("hmac_key_b64u", b64u(secrets.token_bytes(32))))

    def meta_get(self, k: str) -> str:
        row = self._conn.execute("SELECT v FROM meta WHERE k=?", (k,)).fetchone()
        if not row:
            raise NotFound("meta key not found", details={"k": k})
        return str(row["v"])

    def meta_set(self, k: str, v: str) -> None:
        with self.tx() as db:
            db.execute("INSERT INTO meta(k, v) VALUES(?,?) ON CONFLICT(k) DO UPDATE SET v=excluded.v", (k, v))

    def oracle_get(self, k: str) -> str:
        row = self._conn.execute("SELECT v FROM oracle_state WHERE k=?", (k,)).fetchone()
        if not row:
            raise NotFound("oracle key not found", details={"k": k})
        return str(row["v"])

    def oracle_set(self, k: str, v: str) -> None:
        with self.tx() as db:
            db.execute("INSERT INTO oracle_state(k, v) VALUES(?,?) ON CONFLICT(k) DO UPDATE SET v=excluded.v", (k, v))

    def lane_upsert(self, lane_id: str, *, enabled: bool, capacity_wad: int, min_premium_wad: int, max_duration_s: int, deductible_bps: int, grace_bps: int) -> None:
        ts = utc_now_s()
        with self.tx() as db:
            row = db.execute("SELECT used_wad, created_at_s FROM lanes WHERE lane_id=?", (lane_id,)).fetchone()
            used_wad = int(row["used_wad"]) if row else 0
            created_at = int(row["created_at_s"]) if row else ts
            db.execute(
                """
                INSERT INTO lanes(lane_id, enabled, capacity_wad, used_wad, min_premium_wad, max_duration_s, deductible_bps, grace_bps, created_at_s, updated_at_s)
                VALUES(?,?,?,?,?,?,?,?,?,?)
                ON CONFLICT(lane_id) DO UPDATE SET
                  enabled=excluded.enabled,
                  capacity_wad=excluded.capacity_wad,
                  min_premium_wad=excluded.min_premium_wad,
                  max_duration_s=excluded.max_duration_s,
                  deductible_bps=excluded.deductible_bps,
                  grace_bps=excluded.grace_bps,
                  updated_at_s=excluded.updated_at_s
                """,
                (lane_id, 1 if enabled else 0, int(capacity_wad), int(used_wad), int(min_premium_wad), int(max_duration_s), int(deductible_bps), int(grace_bps), created_at, ts),
            )

    def lane_get(self, lane_id: str) -> sqlite3.Row:
        row = self._conn.execute("SELECT * FROM lanes WHERE lane_id=?", (lane_id,)).fetchone()
        if not row:
            raise NotFound("lane not found", details={"lane_id": lane_id})
        return row

    def lane_list(self, *, enabled_only: bool = False) -> list[dict]:
        q = "SELECT * FROM lanes"
        params: tuple[t.Any, ...] = ()
        if enabled_only:
            q += " WHERE enabled=1"
        q += " ORDER BY updated_at_s DESC"
        rows = self._conn.execute(q, params).fetchall()
        return [dict(r) for r in rows]

    def quote_put(self, q: dict) -> None:
        with self.tx() as db:
            db.execute(
                """
                INSERT INTO quotes(quote_id,buyer,lane_id,cover_wei,start_at_s,end_at_s,created_at_s,expires_at_s,salt,consumed)
                VALUES(?,?,?,?,?,?,?,?,?,?)
                """,
                (
                    q["quote_id"],
                    q["buyer"],
                    q["lane_id"],
                    int(q["cover_wei"]),
                    int(q["start_at_s"]),
                    int(q["end_at_s"]),
                    int(q["created_at_s"]),
                    int(q["expires_at_s"]),
                    int(q["salt"]),
                    1 if q.get("consumed") else 0,
                ),
            )

    def quote_get(self, quote_id: str) -> sqlite3.Row:
        row = self._conn.execute("SELECT * FROM quotes WHERE quote_id=?", (quote_id,)).fetchone()
        if not row:
            raise NotFound("quote not found", details={"quote_id": quote_id})
        return row

    def quote_mark_consumed(self, quote_id: str) -> None:
        with self.tx() as db:
            row = db.execute("SELECT consumed FROM quotes WHERE quote_id=?", (quote_id,)).fetchone()
            if not row:
                raise NotFound("quote not found", details={"quote_id": quote_id})
            if int(row["consumed"]) == 1:
                raise Conflict("quote already consumed")
            db.execute("UPDATE quotes SET consumed=1 WHERE quote_id=?", (quote_id,))

    def policy_put(self, p: dict) -> None:
        with self.tx() as db:
            db.execute(
                """
                INSERT INTO policies(policy_id,quote_id,holder,lane_id,cover_wei,premium_wei,fee_wei,start_at_s,end_at_s,bound_at_s,state,nonce)
                VALUES(?,?,?,?,?,?,?,?,?,?,?,?)
                """,
                (
                    p["policy_id"],
                    p["quote_id"],
                    p["holder"],
                    p["lane_id"],
                    int(p["cover_wei"]),
                    int(p["premium_wei"]),
                    int(p["fee_wei"]),
                    int(p["start_at_s"]),
                    int(p["end_at_s"]),
                    int(p["bound_at_s"]),
                    p["state"],
                    int(p["nonce"]),
                ),
            )

    def policy_get(self, policy_id: str) -> sqlite3.Row:
        row = self._conn.execute("SELECT * FROM policies WHERE policy_id=?", (policy_id,)).fetchone()
        if not row:
            raise NotFound("policy not found", details={"policy_id": policy_id})
        return row

    def policy_update_state(self, policy_id: str, state: str, *, bump_nonce: bool = True) -> None:
        with self.tx() as db:
            row = db.execute("SELECT nonce FROM policies WHERE policy_id=?", (policy_id,)).fetchone()
            if not row:
                raise NotFound("policy not found", details={"policy_id": policy_id})
            nonce = int(row["nonce"]) + (1 if bump_nonce else 0)
            db.execute("UPDATE policies SET state=?, nonce=? WHERE policy_id=?", (state, nonce, policy_id))

    def claim_put(self, c: dict) -> None:
        with self.tx() as db:
            db.execute(
                """
                INSERT INTO claims(claim_id,policy_id,holder,loss_ref,filed_at_s,state,payout_wei,verdict_hash,attested_at_s,paid_at_s,void_reason)
                VALUES(?,?,?,?,?,?,?,?,?,?,?)
                """,
                (
                    c["claim_id"],
                    c["policy_id"],
                    c["holder"],
                    c["loss_ref"],
