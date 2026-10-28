#!/usr/bin/env python3
"""Exact candidate generator/checker for small finite same-source experiments.

Fractions only. Search is outside the Lean trust boundary; generated witnesses
must also pass the Lean checker. Exhausting the bounded search means UNKNOWN.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as Q
from hashlib import sha256
from itertools import combinations, product
import json
from pathlib import Path


def rational(x):
    if type(x) not in (int, str, Q):
        raise ValueError("exact integers or rational strings required")
    return Q(x)


def row(xs, size):
    xs = tuple(map(rational, xs))
    if len(xs) != size or any(x < 0 for x in xs) or sum(xs) != 1:
        raise ValueError("invalid probability row")
    return xs


def encoded(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), default=str)


@dataclass(frozen=True)
class Source:
    P: tuple
    q: tuple
    base: tuple
    p0: tuple
    deployed: tuple
    safe: tuple
    T: int

    @classmethod
    def read(cls, d):
        n, a, y = len(d["P"]), len(d["P"][0]), len(d["base"])
        if not n or not a or not y or type(d["T"]) is not int or d["T"] < 0:
            raise ValueError("nonempty alphabets and nonnegative integer horizon required")
        if len(d["q"]) != n or any(type(i) is not int or not 0 <= i < y for i in d["q"]):
            raise ValueError("invalid observation map")
        if len(d["safe"]) != n or any(type(b) is not bool for b in d["safe"]):
            raise ValueError("invalid safety event")
        P = tuple(tuple(row(r, n) for r in rs) for rs in d["P"])
        if any(len(rs) != a for rs in P):
            raise ValueError("action dimension mismatch")
        return cls(P, tuple(d["q"]), tuple(row(r, a) for r in d["base"]),
                   row(d["p0"], n), row(d["deployed"], n), tuple(d["safe"]), d["T"])

    @property
    def identity(self):
        return sha256(encoded(self.__dict__).encode()).hexdigest()


def derive(s):
    """h includes safety at both endpoints, matching the killed-source window."""
    n, T = len(s.P), s.T
    B = tuple(tuple(sum(s.base[s.q[x]][a] * s.P[x][a][z]
                        for a in range(len(s.P[x]))) for z in range(n)) for x in range(n))
    h = [None] * (T + 1)
    h[T] = tuple(Q(b) for b in s.safe)
    for t in reversed(range(T)):
        h[t] = tuple(sum(B[x][z] * h[t + 1][z] for z in range(n)) if s.safe[x]
                     else Q(0) for x in range(n))
    Z = sum(s.p0[x] * h[0][x] for x in range(n))
    if not Z:
        return {"Z": Z}
    mu = tuple(s.p0[x] * h[0][x] / Z for x in range(n))
    R = tuple(tuple(tuple(B[x][z] * h[t + 1][z] / h[t][x] if h[t][x]
                              else Q(x == z) for z in range(n)) for x in range(n)) for t in range(T))
    occ = [mu]
    for t in range(T):
        occ.append(tuple(sum(occ[-1][x] * R[t][x][z] for x in range(n)) for z in range(n)))
    return {"Z": Z, "mu": mu, "R": R, "occupancy": tuple(occ), "h": tuple(h), "baseline": B}


def check_positive(s, cert):
    target = derive(s)
    try:
        if cert["source"] != s.identity or s.deployed != target["mu"] or len(cert["weights"]) != s.T:
            return False
        weights = tuple(tuple(row(r, len(s.P[0])) for r in t) for t in cert["weights"])
        if any(len(t) != len(s.base) for t in weights):
            return False
        return all(sum(weights[t][s.q[x]][a] * s.P[x][a][z] for a in range(len(s.P[0])))
                   == target["R"][t][x][z] for t in range(s.T) for x in range(len(s.P))
                   if target["occupancy"][t][x] > 0 for z in range(len(s.P)))
    except (KeyError, ValueError, TypeError, IndexError, ZeroDivisionError):
        return False


def check_negative(s, cert):
    target = derive(s)
    try:
        t, y = cert["time"], cert["observation"]
        if cert["source"] != s.identity or type(t) is not int or not 0 <= t < s.T:
            return False
        if type(y) is not int or not 0 <= y < len(s.base):
            return False
        c = tuple(tuple(map(rational, r)) for r in cert["coefficient"])
        if len(c) != len(s.P) or any(len(r) != len(s.P) for r in c):
            return False
        b, gap = rational(cert["bound"]), rational(cert["gap"])
        fiber = [x for x in range(len(s.P)) if target["occupancy"][t][x] > 0 and s.q[x] == y]
        def score(v):
            return sum(c[x][z] * v[x][z] for x in fiber for z in range(len(s.P)))
        return gap > 0 and all(score([rs[a] for rs in s.P]) <= b for a in range(len(s.P[0]))) \
            and score(target["R"][t]) >= b + gap
    except (KeyError, ValueError, TypeError, IndexError, ZeroDivisionError):
        return False


def solve_columns(columns, rhs):
    """Small exact overdetermined elimination; no float reconstruction."""
    k = len(columns)
    matrix = [[columns[j][i] for j in range(k)] + [r] for i, r in enumerate(rhs)]
    pivot = 0
    for j in range(k):
        p = next((i for i in range(pivot, len(matrix)) if matrix[i][j]), None)
        if p is None:
            return None
        matrix[pivot], matrix[p] = matrix[p], matrix[pivot]
        scale = matrix[pivot][j]
        matrix[pivot] = [x / scale for x in matrix[pivot]]
        for i in range(len(matrix)):
            if i != pivot:
                scale = matrix[i][j]
                matrix[i] = [x - scale * z for x, z in zip(matrix[i], matrix[pivot])]
        pivot += 1
    if any(all(x == 0 for x in r[:-1]) and r[-1] != 0 for r in matrix):
        return None
    return tuple(matrix[j][-1] for j in range(k))


def candidate_weights(s, d, t, y):
    a, n = len(s.P[0]), len(s.P)
    coords = [(x, z) for x in range(n) if d["occupancy"][t][x] > 0 and s.q[x] == y
              for z in range(n)]
    rhs = [Q(1)] + [d["R"][t][x][z] for x, z in coords]
    columns = [[Q(1)] + [s.P[x][j][z] for x, z in coords] for j in range(a)]
    # ponytail: bounded small-action vertex search; external LP candidates can
    # replace search without changing either checker when larger inputs matter.
    if a > 8:
        return None
    for k in range(1, a + 1):
        for support in combinations(range(a), k):
            w = solve_columns([columns[j] for j in support], rhs)
            if w is not None and all(x >= 0 for x in w):
                result = [Q(0)] * a
                for j, x in zip(support, w):
                    result[j] = x
                return tuple(result)
    return None


def candidate_separator(s, d, t, y):
    n, a = len(s.P), len(s.P[0])
    coords = [(x, z) for x in range(n) if d["occupancy"][t][x] > 0 and s.q[x] == y
              for z in range(n)]
    if len(coords) > 8:
        return None
    for coeff in product((0, 1, -1), repeat=len(coords)):
        b = max(sum(Q(v) * s.P[x][j][z] for v, (x, z) in zip(coeff, coords)) for j in range(a))
        r = sum(Q(v) * d["R"][t][x][z] for v, (x, z) in zip(coeff, coords))
        if r > b:
            c = [[Q(0)] * n for _ in range(n)]
            for v, (x, z) in zip(coeff, coords):
                c[x][z] = Q(v)
            return {"source": s.identity, "time": t, "observation": y,
                    "coefficient": c, "bound": b, "gap": r - b}
    return None


def path_law(p, rows, T):
    n = len(p)
    result = {}
    for path in product(range(n), repeat=T + 1):
        mass = p[path[0]]
        for t in range(T):
            mass *= rows[t][path[t]][path[t + 1]]
        if mass:
            result[path] = mass
    return result


def verify_path_identity(s, d, cert):
    """Independent exhaustive check of the actual returned table, not search."""
    n = len(s.P)
    actual = tuple(tuple(tuple(sum(cert["weights"][t][s.q[x]][a] * s.P[x][a][z]
                                   for a in range(len(s.P[0]))) for z in range(n))
                         for x in range(n)) for t in range(s.T))
    baseline_paths = path_law(s.p0, (d["baseline"],) * s.T, s.T)
    conditioned = {h: mass / d["Z"] for h, mass in baseline_paths.items() if all(s.safe[x] for x in h)}
    return path_law(s.deployed, actual, s.T) == path_law(d["mu"], d["R"], s.T) == conditioned


def run(raw):
    try:
        s = Source.read(raw)
    except (KeyError, ValueError, TypeError, IndexError, ZeroDivisionError) as e:
        return {"status": "INVALID_INPUT", "reason": str(e)}
    d = derive(s)
    common = {"source": s.identity, "target": d}
    if not d["Z"]:
        return {**common, "status": "CONDITIONING_UNDEFINED"}
    if s.deployed != d["mu"]:
        tv = sum(abs(x - y) for x, y in zip(s.deployed, d["mu"])) / 2
        return {**common, "status": "CANDIDATE_UNREALIZABLE", "initial_TV_lower_bound": tv}
    weights = [[candidate_weights(s, d, t, y) for y in range(len(s.base))] for t in range(s.T)]
    if all(w is not None for t in weights for w in t):
        cert = {"source": s.identity, "weights": weights}
        if not check_positive(s, cert):
            raise RuntimeError("generated positive certificate failed exact verification")
        checked = len(s.P) ** (s.T + 1) <= 100000
        if checked and not verify_path_identity(s, d, cert):
            raise RuntimeError("independent full-path check failed")
        return {**common, "status": "CANDIDATE_REALIZABLE", "certificate": cert,
                "independent_full_path_checked": checked}
    for t in range(s.T):
        for y in range(len(s.base)):
            cert = candidate_separator(s, d, t, y)
            if cert is not None:
                if not check_negative(s, cert):
                    raise RuntimeError("generated negative certificate failed exact verification")
                return {**common, "status": "CANDIDATE_UNREALIZABLE", "certificate": cert}
    return {**common, "status": "UNKNOWN", "reason": "bounded search found no certificate"}


def registered_cases():
    risk0, risk1, dead = ["3/8", "3/8", "1/4"], ["1/8", "1/8", "3/4"], [0, 0, 1]
    source = dict(P=[[risk0], [risk1], [dead]], q=[0, 0, 0], base=[[1]],
                  p0=["1/2", "1/2", 0], deployed=["3/4", "1/4", 0], safe=[True, True, False], T=1)
    expanded = {**source, "P": [[r, [1, 0, 0], [0, 1, 0]] for r in [risk0, risk1, dead]],
                "base": [[1, 0, 0]], "T": 2}
    alias = dict(P=[[[1, 0, 0], dead], [dead, [0, 1, 0]], [dead, dead]], q=[0, 0, 0],
                 base=[["1/2", "1/2"]], p0=["1/2", "1/2", 0], deployed=["1/2", "1/2", 0],
                 safe=[True, True, False], T=1)
    unreachable = {**expanded, "P": expanded["P"][:2] + [[[1, 0, 0]] * 3]}
    variant = {**expanded, "base": [[0, "1/3", "2/3"]], "deployed": source["p0"]}
    return {"original_actions": source, "two_step_added_actions": expanded,
            "unprepared_initial": {**expanded, "deployed": source["p0"]},
            "same_source_alias": alias, "unreachable_fallback": unreachable,
            "independent_baseline_variant": variant,
            "zero_horizon": {**expanded, "T": 0, "deployed": source["p0"]},
            "zero_survival": {**source, "safe": [False, False, False]}}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", nargs="?", type=Path)
    parser.add_argument("--registered", action="store_true")
    args = parser.parse_args()
    if args.registered:
        result = {name: {"input": raw, "result": run(raw)} for name, raw in registered_cases().items()}
    elif args.input:
        result = run(json.loads(args.input.read_text()))
    else:
        parser.error("supply a JSON input or --registered")
    print(json.dumps(result, default=str, indent=2))
