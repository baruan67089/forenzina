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

