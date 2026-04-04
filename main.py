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
                    int(c["filed_at_s"]),
                    c["state"],
                    int(c["payout_wei"]),
                    c["verdict_hash"],
                    int(c["attested_at_s"]),
                    int(c["paid_at_s"]),
                    c["void_reason"],
                ),
            )

    def claim_get(self, claim_id: str) -> sqlite3.Row:
        row = self._conn.execute("SELECT * FROM claims WHERE claim_id=?", (claim_id,)).fetchone()
        if not row:
            raise NotFound("claim not found", details={"claim_id": claim_id})
        return row

    def claim_update(self, claim_id: str, *, state: str | None = None, payout_wei: int | None = None, verdict_hash: str | None = None, attested_at_s: int | None = None, paid_at_s: int | None = None, void_reason: str | None = None) -> None:
        fields: list[str] = []
        vals: list[t.Any] = []
        for k, v in (
            ("state", state),
            ("payout_wei", payout_wei),
            ("verdict_hash", verdict_hash),
            ("attested_at_s", attested_at_s),
            ("paid_at_s", paid_at_s),
            ("void_reason", void_reason),
        ):
            if v is None:
                continue
            fields.append(f"{k}=?")
            vals.append(v)
        if not fields:
            return
        vals.append(claim_id)
        with self.tx() as db:
            db.execute(f"UPDATE claims SET {', '.join(fields)} WHERE claim_id=?", tuple(vals))

    def ledger_add(self, *, kind: str, ref: str, amount_wei: int, memo: str) -> str:
        entry_id = str(uuid.uuid4())
        with self.tx() as db:
            db.execute(
                "INSERT INTO ledger(entry_id,kind,at_s,ref,amount_wei,memo) VALUES(?,?,?,?,?,?)",
                (entry_id, kind, utc_now_s(), ref, int(amount_wei), memo),
            )
        return entry_id

    def ledger_recent(self, limit: int = 100) -> list[dict]:
        limit = clamp_int(int(limit), 1, 1000, what="limit")
        rows = self._conn.execute("SELECT * FROM ledger ORDER BY at_s DESC LIMIT ?", (limit,)).fetchall()
        return [dict(r) for r in rows]

    def credit_get(self, who: str) -> int:
        row = self._conn.execute("SELECT amount_wei FROM credits WHERE who=?", (who,)).fetchone()
        if not row:
            return 0
        return int(row["amount_wei"])

    def credit_add(self, who: str, delta_wei: int) -> None:
        ts = utc_now_s()
        with self.tx() as db:
            row = db.execute("SELECT amount_wei FROM credits WHERE who=?", (who,)).fetchone()
            cur = int(row["amount_wei"]) if row else 0
            nxt = safe_add_u256(cur, int(delta_wei), what="credit_add")
            db.execute(
                "INSERT INTO credits(who,amount_wei,updated_at_s) VALUES(?,?,?) ON CONFLICT(who) DO UPDATE SET amount_wei=excluded.amount_wei, updated_at_s=excluded.updated_at_s",
                (who, nxt, ts),
            )

    def credit_sub(self, who: str, delta_wei: int) -> None:
        ts = utc_now_s()
        with self.tx() as db:
            row = db.execute("SELECT amount_wei FROM credits WHERE who=?", (who,)).fetchone()
            cur = int(row["amount_wei"]) if row else 0
            nxt = safe_sub_u256(cur, int(delta_wei), what="credit_sub")
            db.execute(
                "INSERT INTO credits(who,amount_wei,updated_at_s) VALUES(?,?,?) ON CONFLICT(who) DO UPDATE SET amount_wei=excluded.amount_wei, updated_at_s=excluded.updated_at_s",
                (who, nxt, ts),
            )


# -----------------------------
# Domain: lanes, quotes, policy, claims
# -----------------------------

@dataclasses.dataclass(frozen=True)
class LaneCfg:
    lane_id: str
    enabled: bool
    capacity_wad: int
    min_premium_wad: int
    max_duration_s: int
    deductible_bps: int
    grace_bps: int


@dataclasses.dataclass(frozen=True)
class Quote:
    quote_id: str
    buyer: str
    lane_id: str
    cover_wei: int
    start_at_s: int
    end_at_s: int
    created_at_s: int
    expires_at_s: int
    salt: int
    consumed: bool


@dataclasses.dataclass(frozen=True)
class Policy:
    policy_id: str
    quote_id: str
    holder: str
    lane_id: str
    cover_wei: int
    premium_wei: int
    fee_wei: int
    start_at_s: int
    end_at_s: int
    bound_at_s: int
    state: str
    nonce: int


@dataclasses.dataclass(frozen=True)
class Claim:
    claim_id: str
    policy_id: str
    holder: str
    loss_ref: str
    filed_at_s: int
    state: str
    payout_wei: int
    verdict_hash: str
    attested_at_s: int
    paid_at_s: int
    void_reason: str


def cover_to_wad(cover_wei: int) -> int:
    # 1 ETH => 1e4 (coverWei/1e14)
    if cover_wei <= 0:
        raise BadInput("cover must be > 0")
    wad = cover_wei // 10**14
    if wad == 0:
        wad = 1
    if wad > 2**32 - 1:
        raise BadInput("cover too large")
    return int(wad)


def grace_seconds(grace_bps: int, term_s: int) -> int:
    if grace_bps <= 0:
        return 0
    if term_s <= 0:
        return 0
    return int((int(term_s) * int(grace_bps)) // BPS)


def price_quote(cover_wei: int, start_at_s: int, end_at_s: int, *, min_premium_wad: int, reserve_factor_bps: int) -> tuple[int, int]:
    term_s = int(end_at_s) - int(start_at_s)
    if term_s <= 0:
        raise BadInput("invalid term")
    base = (int(cover_wei) * int(min_premium_wad)) // 10_000
    premium = (base * term_s) // YEAR_SECONDS
    if premium <= 0:
        premium = 1
    reserve = (int(cover_wei) * int(reserve_factor_bps)) // BPS
    return int(premium), int(reserve)


def policy_id_for(quote_id: str, holder: str, lane_id: str, cover_wei: int, start_at_s: int, end_at_s: int, premium_wei: int) -> str:
    payload = {
        "tag": "apex.policy",
        "quote_id": quote_id,
        "holder": holder,
        "lane_id": lane_id,
        "cover_wei": int(cover_wei),
        "start_at_s": int(start_at_s),
        "end_at_s": int(end_at_s),
        "premium_wei": int(premium_wei),
        "chain_id": 1,
        "verifying_contract": "0x" + "00" * 20,
    }
    return h256(stable_json(payload))


def quote_id_for(buyer: str, lane_id: str, cover_wei: int, start_at_s: int, end_at_s: int, salt: int) -> str:
    payload = {
        "tag": "apex.quote",
        "buyer": buyer,
        "lane_id": lane_id,
        "cover_wei": int(cover_wei),
        "start_at_s": int(start_at_s),
        "end_at_s": int(end_at_s),
        "salt": int(salt),
        "chain_id": 1,
        "verifying_contract": "0x" + "00" * 20,
    }
    return h256(stable_json(payload))


def claim_id_for(policy_id: str, holder: str, loss_ref: str, nonce: int) -> str:
    payload = {
        "tag": "apex.claim",
        "policy_id": policy_id,
        "holder": holder,
        "loss_ref": loss_ref,
        "nonce": int(nonce),
        "chain_id": 1,
    }
    return h256(stable_json(payload))


# -----------------------------
# Oracle attestation (local)
# -----------------------------

def oracle_digest_for(claim_id: str, policy_id: str, payout_wei: int, verdict_hash: str, attested_at_s: int, nonce: int, deadline_s: int, *, domain_tag: str) -> bytes:
    # EIP-712 is not recreated here; this produces a deterministic digest suitable for local signing.
    payload = {
        "domain_tag": domain_tag,
        "claim_id": claim_id,
        "policy_id": policy_id,
        "payout_wei": int(payout_wei),
        "verdict_hash": verdict_hash,
        "attested_at_s": int(attested_at_s),
        "nonce": int(nonce),
        "deadline_s": int(deadline_s),
        "chain_id": 1,
        "verifying_contract": "0x" + "00" * 20,
    }
    return sha3_256(stable_json(payload))


def oracle_sign_hmac(digest: bytes, *, hmac_key: bytes) -> str:
    sig = hmac.new(hmac_key, digest, hashlib.sha256).digest()
    return "hmac-sha256:" + b64u(sig)


def oracle_verify_hmac(digest: bytes, signature: str, *, hmac_key: bytes) -> bool:
    if not isinstance(signature, str) or not signature.startswith("hmac-sha256:"):
        return False
    try:
        sig = b64u_decode(signature.split(":", 1)[1])
    except Exception:
        return False
    expect = hmac.new(hmac_key, digest, hashlib.sha256).digest()
    return hmac.compare_digest(sig, expect)


# -----------------------------
# Pool engine (simulated)
# -----------------------------

class Engine:
    def __init__(self, store: Store):
        self.s = store

    # meta getters
    def _m_int(self, k: str) -> int:
        return int(self.s.meta_get(k))

    def _m_str(self, k: str) -> str:
        return self.s.meta_get(k)

    def snapshot(self) -> dict:
        return {
            "app": {"name": APP_NAME, "revision": APP_REVISION},
            "meta": {
                "created_at": self._m_str("created_at"),
                "genesis_tag": self._m_str("genesis_tag"),
                "quote_ttl_s": self._m_int("quote_ttl_s"),
                "withdraw_delay_s": self._m_int("withdraw_delay_s"),
            },
            "pool": {
                "available_capital_wei": self._m_int("available_capital_wei"),
                "reserved_capital_wei": self._m_int("reserved_capital_wei"),
                "total_premiums_wei": self._m_int("total_premiums_wei"),
                "total_claims_paid_wei": self._m_int("total_claims_paid_wei"),
                "protocol_fee_bps": self._m_int("protocol_fee_bps"),
                "reserve_factor_bps": self._m_int("reserve_factor_bps"),
                "max_slippage_bps": self._m_int("max_slippage_bps"),
                "treasury": self._m_str("treasury"),
                "oracle": self._m_str("oracle"),
            },
            "sentinels": list(INERT_SENTINELS),
            "onchain_pairing": {
                "contract": "apex",
                "forenzina_integration": "solidity constant FORENZINA_INTEGRATION_TAG = keccak256(\"forenzina.apex.integration.v1\")",
            },
            "time": {"utc_now_s": utc_now_s(), "iso": iso_utc()},
        }

    def pool_deposit(self, amount_wei: int, *, memo: str) -> dict:
        if amount_wei <= 0:
            raise BadInput("amount must be > 0")
        avail = self._m_int("available_capital_wei")
        avail = safe_add_u256(avail, int(amount_wei), what="available+deposit")
        self.s.meta_set("available_capital_wei", str(avail))
        entry_id = self.s.ledger_add(kind="deposit", ref="pool", amount_wei=int(amount_wei), memo=memo or "deposit")
        return {"entry_id": entry_id, "available_capital_wei": avail}

    def lane_configure(self, lane_id: str, *, enabled: bool, capacity_wad: int, min_premium_wad: int, max_duration_s: int, deductible_bps: int, grace_bps: int) -> dict:
        ensure_hex(lane_id, what="lane_id")
        capacity_wad = clamp_int(int(capacity_wad), 1, 2_000_000_000, what="capacity_wad")
        min_premium_wad = clamp_int(int(min_premium_wad), 1, 8_000_000_000, what="min_premium_wad")
        max_duration_s = clamp_int(int(max_duration_s), 5 * 60, 365 * 24 * 60 * 60, what="max_duration_s")
        deductible_bps = clamp_int(int(deductible_bps), 0, 6_600, what="deductible_bps")
        grace_bps = clamp_int(int(grace_bps), 0, 2_500, what="grace_bps")

        self.s.lane_upsert(
            lane_id,
            enabled=bool(enabled),
            capacity_wad=capacity_wad,
            min_premium_wad=min_premium_wad,
            max_duration_s=max_duration_s,
            deductible_bps=deductible_bps,
            grace_bps=grace_bps,
        )
        return {"ok": True, "lane": dict(self.s.lane_get(lane_id))}

    def quote_open(self, *, buyer: str, lane_id: str, cover_wei: int, start_at_s: int, end_at_s: int, salt: int | None = None) -> dict:
        ensure_hex(buyer, what="buyer")
        ensure_hex(lane_id, what="lane_id")
        cover_wei = clamp_int(int(cover_wei), 1, 10**40, what="cover_wei")
        start_at_s = clamp_int(int(start_at_s), 0, 2_000_000_000, what="start_at_s")
        end_at_s = clamp_int(int(end_at_s), 0, 2_000_000_000, what="end_at_s")
        if end_at_s <= start_at_s:
            raise BadInput("end_at_s must be > start_at_s")

        now_s = utc_now_s()
        if start_at_s < now_s:
            raise TooLate("start time in the past", details={"now_s": now_s, "start_at_s": start_at_s})

        lane = self.s.lane_get(lane_id)
        if int(lane["enabled"]) != 1:
            raise NotFound("lane disabled", details={"lane_id": lane_id})
        term = end_at_s - start_at_s
        if term > int(lane["max_duration_s"]):
            raise BadInput("term too long", details={"term_s": term, "max_duration_s": int(lane["max_duration_s"])})

        if salt is None:
            salt = secrets.randbelow(2**96 - 1) + 1
        salt = clamp_int(int(salt), 1, 2**96 - 1, what="salt")

        quote_id = quote_id_for(buyer, lane_id, cover_wei, start_at_s, end_at_s, salt)
        # if already exists => conflict
        with contextlib.suppress(NotFound):
            _ = self.s.quote_get(quote_id)
            raise Conflict("quote already exists", details={"quote_id": quote_id})

        ttl = self._m_int("quote_ttl_s")
        created_at = now_s
        expires_at = now_s + ttl

        premium_wei, reserve_wei = price_quote(
            cover_wei,
            start_at_s,
            end_at_s,
            min_premium_wad=int(lane["min_premium_wad"]),
            reserve_factor_bps=self._m_int("reserve_factor_bps"),
        )
        fee_bps = self._m_int("protocol_fee_bps")
        fee_wei = bps_mul(premium_wei, fee_bps)
        required_wei = premium_wei + fee_wei

        q = {
            "quote_id": quote_id,
            "buyer": buyer,
            "lane_id": lane_id,
            "cover_wei": int(cover_wei),
            "start_at_s": int(start_at_s),
            "end_at_s": int(end_at_s),
            "created_at_s": int(created_at),
            "expires_at_s": int(expires_at),
            "salt": int(salt),
            "consumed": False,
        }
        self.s.quote_put(q)
        self.s.ledger_add(kind="quote_open", ref=quote_id, amount_wei=0, memo="quote opened")

        return {
            "quote": q,
            "pricing": {
                "premium_wei": premium_wei,
                "fee_wei": fee_wei,
                "required_wei": required_wei,
                "reserve_wei": reserve_wei,
                "protocol_fee_bps": fee_bps,
            },
        }

    def policy_bind(self, *, quote_id: str, payer: str, paid_wei: int, memo: str = "") -> dict:
        ensure_hex(quote_id, what="quote_id")
        ensure_hex(payer, what="payer")
        paid_wei = clamp_int(int(paid_wei), 0, 10**40, what="paid_wei")

        q = self.s.quote_get(quote_id)
        if int(q["consumed"]) == 1:
            raise Conflict("quote consumed", details={"quote_id": quote_id})
        if str(q["buyer"]).lower() != payer.lower():
            raise Unauthorized("payer must match quote buyer")
        now_s = utc_now_s()
        if now_s > int(q["expires_at_s"]):
            raise TooLate("quote expired", details={"expires_at_s": int(q["expires_at_s"]), "now_s": now_s})

        lane = self.s.lane_get(str(q["lane_id"]))
        if int(lane["enabled"]) != 1:
            raise NotFound("lane disabled", details={"lane_id": str(q["lane_id"])})

        term = int(q["end_at_s"]) - int(q["start_at_s"])
        grace = grace_seconds(int(lane["grace_bps"]), term)
        if now_s > int(q["start_at_s"]) + grace:
            raise TooLate("start window passed", details={"start_at_s": int(q["start_at_s"]), "grace_s": grace, "now_s": now_s})

        premium_wei, reserve_wei = price_quote(
            int(q["cover_wei"]),
            int(q["start_at_s"]),
            int(q["end_at_s"]),
            min_premium_wad=int(lane["min_premium_wad"]),
            reserve_factor_bps=self._m_int("reserve_factor_bps"),
        )
        fee_wei = bps_mul(premium_wei, self._m_int("protocol_fee_bps"))
        required_wei = premium_wei + fee_wei
        if paid_wei != required_wei:
            raise BadInput("paid_wei must equal required_wei", details={"paid_wei": paid_wei, "required_wei": required_wei})

        used_wad = int(lane["used_wad"])
        cap_wad = int(lane["capacity_wad"])
        cover_wad = cover_to_wad(int(q["cover_wei"]))
        if used_wad + cover_wad > cap_wad:
            raise Accounting("lane capacity exceeded", details={"used_wad": used_wad, "cover_wad": cover_wad, "capacity_wad": cap_wad})

        avail = self._m_int("available_capital_wei")
        if avail < reserve_wei:
            raise Accounting("pool insufficient to reserve", details={"available": avail, "reserve": reserve_wei})

        # accounting updates
        avail = safe_add_u256(avail, int(premium_wei), what="available+premium")
        reserved = self._m_int("reserved_capital_wei")
        reserved = safe_add_u256(reserved, int(reserve_wei), what="reserved+reserve")

        self.s.meta_set("available_capital_wei", str(avail))
        self.s.meta_set("reserved_capital_wei", str(reserved))
        self.s.meta_set("total_premiums_wei", str(safe_add_u256(self._m_int("total_premiums_wei"), int(premium_wei), what="premiums+")))

        # treasury gets fee as credit
        treasury = self._m_str("treasury")
        self.s.credit_add(treasury, int(fee_wei))

        # bump lane used
        with self.s.tx() as db:
            db.execute("UPDATE lanes SET used_wad = used_wad + ? , updated_at_s=? WHERE lane_id=?", (int(cover_wad), utc_now_s(), str(q["lane_id"])))

        self.s.quote_mark_consumed(quote_id)

        policy_id = policy_id_for(
            quote_id,
            payer,
            str(q["lane_id"]),
            int(q["cover_wei"]),
            int(q["start_at_s"]),
            int(q["end_at_s"]),
            int(premium_wei),
        )
        with contextlib.suppress(NotFound):
            _ = self.s.policy_get(policy_id)
            raise Conflict("policy already exists", details={"policy_id": policy_id})

        p = {
            "policy_id": policy_id,
            "quote_id": quote_id,
            "holder": payer,
            "lane_id": str(q["lane_id"]),
            "cover_wei": int(q["cover_wei"]),
            "premium_wei": int(premium_wei),
            "fee_wei": int(fee_wei),
            "start_at_s": int(q["start_at_s"]),
            "end_at_s": int(q["end_at_s"]),
            "bound_at_s": int(now_s),
            "state": "Active",
            "nonce": 1,
        }
        self.s.policy_put(p)
        self.s.ledger_add(kind="policy_bind", ref=policy_id, amount_wei=int(premium_wei), memo=memo or "policy bound")
        return {"policy": p, "pool": {"available_capital_wei": avail, "reserved_capital_wei": reserved}}

    def claim_file(self, *, policy_id: str, holder: str, loss_ref: str) -> dict:
        ensure_hex(policy_id, what="policy_id")
        ensure_hex(holder, what="holder")
        if not isinstance(loss_ref, str) or len(loss_ref) < 3:
            raise BadInput("loss_ref too short")
        # store loss_ref as hash-like reference string (not necessarily hex)
        p = self.s.policy_get(policy_id)
        if str(p["holder"]).lower() != holder.lower():
            raise Unauthorized("holder mismatch")
        if str(p["state"]) != "Active":
            raise BadInput("policy not active", details={"state": str(p["state"])})
        now_s = utc_now_s()
        if now_s < int(p["start_at_s"]):
            raise TooSoon("policy not started", details={"start_at_s": int(p["start_at_s"]), "now_s": now_s})
        if now_s > int(p["end_at_s"]):
            raise TooLate("policy ended", details={"end_at_s": int(p["end_at_s"]), "now_s": now_s})

        nonce = int(p["nonce"])
        claim_id = claim_id_for(policy_id, holder, loss_ref, nonce)
        with contextlib.suppress(NotFound):
            _ = self.s.claim_get(claim_id)
            raise Conflict("claim exists", details={"claim_id": claim_id})

        c = {
            "claim_id": claim_id,
            "policy_id": policy_id,
            "holder": holder,
            "loss_ref": loss_ref,
            "filed_at_s": int(now_s),
            "state": "Filed",
            "payout_wei": 0,
            "verdict_hash": "0x" + "00" * 32,
            "attested_at_s": 0,
            "paid_at_s": 0,
            "void_reason": "",
        }
        self.s.claim_put(c)
        self.s.policy_update_state(policy_id, "Claimed", bump_nonce=True)
        self.s.ledger_add(kind="claim_file", ref=claim_id, amount_wei=0, memo="claim filed")
        return {"claim": c}

    def _max_net_payout(self, policy_row: sqlite3.Row, lane_row: sqlite3.Row) -> int:
        cover = int(policy_row["cover_wei"])
        deductible_bps = int(lane_row["deductible_bps"])
        if deductible_bps < 0:
            deductible_bps = 0
        if deductible_bps > 6_600:
            deductible_bps = 6_600
        return (cover * (BPS - deductible_bps)) // BPS

    def claim_attest(self, *, claim_id: str, payout_wei: int, verdict_hash: str | None = None, deadline_s: int | None = None) -> dict:
        ensure_hex(claim_id, what="claim_id")
        payout_wei = clamp_int(int(payout_wei), 0, 10**40, what="payout_wei")
        c = self.s.claim_get(claim_id)
        if str(c["state"]) != "Filed":
            raise BadInput("claim not filed", details={"state": str(c["state"])})

        p = self.s.policy_get(str(c["policy_id"]))
        if str(p["state"]) != "Claimed":
            raise BadInput("policy not claimed", details={"state": str(p["state"])})
        lane = self.s.lane_get(str(p["lane_id"]))
        if int(lane["enabled"]) != 1:
            raise NotFound("lane disabled")

        max_net = self._max_net_payout(p, lane)
        if payout_wei > max_net:
            raise BadInput("payout exceeds deductible-adjusted max", details={"payout_wei": payout_wei, "max_net": max_net})

        if verdict_hash is None:
            verdict_hash = h256(stable_json({"verdict": "ok", "at_ms": now_ms(), "salt": secrets.token_hex(16)}))
        ensure_hex(verdict_hash, what="verdict_hash")

        now_s = utc_now_s()
        if deadline_s is None:
            deadline_s = now_s + 10 * 60 + 11
        deadline_s = clamp_int(int(deadline_s), now_s + 1, now_s + 7 * 24 * 60 * 60, what="deadline_s")

        domain_tag = self.s.meta_get("genesis_tag")
        nonce = int(self.s.oracle_get("nonce"))
        digest = oracle_digest_for(
            claim_id,
            str(c["policy_id"]),
            payout_wei,
            verdict_hash,
            now_s,
            nonce,
            deadline_s,
            domain_tag=domain_tag,
        )
        key = b64u_decode(self.s.oracle_get("hmac_key_b64u"))
        signature = oracle_sign_hmac(digest, hmac_key=key)

        # persist attestation
        self.s.claim_update(claim_id, state="Attested", payout_wei=int(payout_wei), verdict_hash=verdict_hash, attested_at_s=now_s)
        self.s.oracle_set("nonce", str(nonce + 1))
        self.s.ledger_add(kind="claim_attest", ref=claim_id, amount_wei=int(payout_wei), memo="claim attested")

        return {
            "attestation": {
                "claim_id": claim_id,
                "policy_id": str(c["policy_id"]),
                "payout_wei": int(payout_wei),
                "verdict_hash": verdict_hash,
                "attested_at_s": int(now_s),
                "nonce": int(nonce),
                "deadline_s": int(deadline_s),
                "digest": "0x" + digest.hex(),
                "signature": signature,
                "oracle": self._m_str("oracle"),
            }
        }

    def claim_pay(self, *, claim_id: str, to: str) -> dict:
        ensure_hex(claim_id, what="claim_id")
        ensure_hex(to, what="to")
        c = self.s.claim_get(claim_id)
        if str(c["state"]) != "Attested":
            raise BadInput("claim not attested", details={"state": str(c["state"])})
        p = self.s.policy_get(str(c["policy_id"]))
        if str(p["state"]) != "Claimed":
            raise BadInput("policy not claimed", details={"state": str(p["state"])})

        payout = int(c["payout_wei"])
        avail = self._m_int("available_capital_wei")
        if avail < payout:
            raise Accounting("insufficient available capital", details={"available": avail, "payout": payout})

        # release reserve
        reserve_factor = self._m_int("reserve_factor_bps")
        reserve = (int(p["cover_wei"]) * reserve_factor) // BPS
        reserved = self._m_int("reserved_capital_wei")
        if reserved < reserve:
            raise Accounting("reserved underflow", details={"reserved": reserved, "reserve": reserve})
        reserved = safe_sub_u256(reserved, reserve, what="reserved-reserve")

        # decrement lane used
        lane = self.s.lane_get(str(p["lane_id"]))
        cover_wad = cover_to_wad(int(p["cover_wei"]))
        used = int(lane["used_wad"])
        if used < cover_wad:
            raise Accounting("used underflow", details={"used": used, "cover_wad": cover_wad})
        with self.s.tx() as db:
            db.execute("UPDATE lanes SET used_wad=used_wad-?, updated_at_s=? WHERE lane_id=?", (int(cover_wad), utc_now_s(), str(p["lane_id"])))

        avail = safe_sub_u256(avail, payout, what="available-payout")
        self.s.meta_set("available_capital_wei", str(avail))
        self.s.meta_set("reserved_capital_wei", str(reserved))
        self.s.meta_set("total_claims_paid_wei", str(safe_add_u256(self._m_int("total_claims_paid_wei"), payout, what="claimsPaid+")))
