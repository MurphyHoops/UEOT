"""Shared deterministic outward-interval and provenance utilities for physics/unification."""
from __future__ import annotations

from decimal import Decimal, localcontext
from fractions import Fraction
import hashlib
import json
from pathlib import Path
from mpmath import iv, mp

mp.dps = 50
iv.dps = 40


def require(ok: bool, msg: str) -> None:
    if not ok:
        raise AssertionError(msg)


def _mpf_tuple_to_fraction(t: tuple) -> Fraction:
    sign, man, exp, _bc = t
    if man == 0:
        return Fraction(0, 1)
    signed_man = -int(man) if sign else int(man)
    if exp >= 0:
        return Fraction(signed_man << int(exp), 1)
    return Fraction(signed_man, 1 << (-int(exp)))


def _format_directed_decimal(q: Fraction, digits: int, *, ceiling: bool) -> str:
    if q == 0:
        return "0"
    abs_q = abs(q)
    k = len(str(abs_q.numerator)) - len(str(abs_q.denominator)) - digits
    low_target = Fraction(10 ** (digits - 1), 1)
    high_target = Fraction(10 ** digits, 1)

    def scaled(exp10: int) -> Fraction:
        if exp10 >= 0:
            return q / (10 ** exp10)
        return q * (10 ** (-exp10))

    while abs(scaled(k)) < low_target:
        k -= 1
    while abs(scaled(k)) >= high_target:
        k += 1

    s = scaled(k)
    num, den = s.numerator, s.denominator
    m = -((-num) // den) if ceiling else (num // den)
    with localcontext() as ctx:
        ctx.prec = max(60, digits + 16)
        dec = Decimal(m).scaleb(k).normalize()
        out = str(dec)

    out_q = Fraction(Decimal(out))
    if ceiling:
        require(out_q >= q, f"Directed decimal ceiling failed: {out_q} < {q}")
    else:
        require(out_q <= q, f"Directed decimal floor failed: {out_q} > {q}")
    return out


def outward_str(x, digits: int = 18) -> list[str]:
    v = iv.mpf(x)
    q_lo = _mpf_tuple_to_fraction(v._mpi_[0])
    q_hi = _mpf_tuple_to_fraction(v._mpi_[1])
    require(q_lo <= q_hi, "Inverted interval endpoints")
    return [
        _format_directed_decimal(q_lo, digits, ceiling=False),
        _format_directed_decimal(q_hi, digits, ceiling=True),
    ]


def strictly_below(x, y) -> bool:
    return bool(iv.mpf(x).b < iv.mpf(y).a)


def strictly_above(x, y) -> bool:
    return bool(iv.mpf(x).a > iv.mpf(y).b)


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=False, sort_keys=True) + "\n")
