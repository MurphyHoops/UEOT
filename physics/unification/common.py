"""Shared deterministic outward-interval and provenance utilities for physics/unification."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
from mpmath import iv, mp

mp.dps = 50
iv.dps = 40


def require(ok: bool, msg: str) -> None:
    if not ok:
        raise AssertionError(msg)


def outward_str(x) -> list[str]:
    v = iv.mpf(x)
    lo = mp.mpf(v._mpi_[0])
    hi = mp.mpf(v._mpi_[1])
    return [mp.nstr(lo, 18), mp.nstr(hi, 18)]


def strictly_below(x, y) -> bool:
    return bool(iv.mpf(x).b < iv.mpf(y).a)


def strictly_above(x, y) -> bool:
    return bool(iv.mpf(x).a > iv.mpf(y).b)


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=False, sort_keys=True) + "\n")
