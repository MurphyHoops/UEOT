#!/usr/bin/env python3
"""Data-only exact candidate selector. It never opens generator-private truth/seeds.

Candidate outputs acquire a statistical certificate only after the separate
Lean consumer and artifact-binding runner pass. Raw bit parsing is a stated
host-language trust boundary, not millions of native Lean sample proofs.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
from hashlib import sha256
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent.with_name("action_certificates_v1")))
from exact_certificates import Source, derive

N, DELTA, ALPHA, THRESHOLD = 262144, Q(1, 250), Q(1, 300), Q(1, 5)
PROBES = ("risk0_safe", "risk1_safe", "select0_failure", "select1_failure")
FORMAT = "BERNOULLI_BITS_LSB_FIRST_V1"


def encoded(value):
    return (json.dumps(value, sort_keys=True, indent=2, default=str) + "\n").encode()


def digest(data):
    return sha256(data).hexdigest()


def count_bits(data, n):
    if type(n) is not int or n < 0 or len(data) != (n + 7) // 8:
        raise ValueError("wrong packed Bernoulli length")
    if n % 8 and data[-1] >> (n % 8):
        raise ValueError("nonzero unused high bits")
    return sum(bin(x).count("1") for x in data)


def read_training(directory):
    directory = Path(directory).resolve(strict=True)
    path = directory / "training.json"
    original = path.read_bytes()
    meta = json.loads(original)
    expected = {"schema", "record_id", "format", "n", "probe_order", "probes", "freeze_sha256"}
    if set(meta) != expected or meta["schema"] != "UEOT/FINITE_DATA_TRAINING/V1":
        raise ValueError("wrong public training metadata")
    if type(meta["record_id"]) is not str or not meta["record_id"] or Path(meta["record_id"]).name != meta["record_id"] or meta["record_id"] in (".", ".."):
        raise ValueError("invalid public record identity")
    if type(meta["freeze_sha256"]) is not str or len(meta["freeze_sha256"]) != 64 or any(
            c not in "0123456789abcdef" for c in meta["freeze_sha256"]):
        raise ValueError("invalid frozen protocol hash")
    if meta["format"] != FORMAT or type(meta["n"]) is not int or meta["n"] != N:
        raise ValueError("wrong preregistered sample count or bit format")
    if meta["probe_order"] != list(PROBES) or len(meta["probes"]) != 4:
        raise ValueError("wrong four-probe order")
    counts, hashes = [], {}
    for name, row in zip(PROBES, meta["probes"]):
        if set(row) != {"name", "file", "sha256"} or row["name"] != name:
            raise ValueError("wrong probe identity")
        filename = row["file"]
        if type(filename) is not str or Path(filename).name != filename or filename != name + ".bin":
            raise ValueError("probe path is not the frozen local filename")
        probe = directory / filename
        if probe.is_symlink():
            raise ValueError("probe symlinks are not input snapshots")
        data = probe.read_bytes()
        if digest(data) != row["sha256"]:
            raise ValueError("raw probe hash mismatch")
        counts.append(count_bits(data, N))
        hashes[filename] = row["sha256"]
    if path.read_bytes() != original or any(digest((directory / p).read_bytes()) != h for p, h in hashes.items()):
        raise ValueError("training changed while being read")
    return counts, {"record_id": meta["record_id"], "training_sha256": digest(original),
                    "raw_probe_sha256": hashes, "freeze_sha256": meta["freeze_sha256"]}


def reference_source(estimate, T):
    r0, r1, e0, e1 = estimate
    dead = (0, 0, 1)
    rows = [((r / 2, r / 2, 1 - r), (1 - e0, 0, e0), (0, 1 - e1, e1)) for r in (r0, r1)]
    nu0, nu1 = r0 / (r0 + r1), r1 / (r0 + r1)
    prepared = [nu0 * (1 - e0), nu1 * (1 - e1), nu0 * e0 + nu1 * e1]
    return Source.read(dict(P=rows + [(dead, dead, dead)], q=[0, 0, 0], base=[[1, 0, 0]],
                            p0=[Q(1, 2), Q(1, 2), 0], deployed=prepared,
                            safe=[True, True, False], T=T))


def tv(p, q):
    return sum(abs(x - y) for x, y in zip(p, q)) / 2


def candidate(counts, T):
    if type(T) is not int or T < 0:
        raise ValueError("nonnegative integer horizon required")
    if len(counts) != 4 or any(type(x) is not int or not 0 <= x <= N for x in counts):
        raise ValueError("four valid probe counts required")
    estimate = tuple(Q(k, N) for k in counts)
    common = {"status": "UNKNOWN", "estimate": estimate, "counts": tuple(counts), "n": N,
              "delta": DELTA, "alpha": ALPHA, "threshold": THRESHOLD, "T": T,
              "actual_operation_count": T + 1, "information": "constant observation",
              "confidence_scope": "Conditional on the simultaneous four-probe calibration event; not observed by selector."}
    if T == 0:
        return {**common, "status": "CANDIDATE_EXACT_ZERO_HORIZON", "preparation": None,
                "weights": [], "actual_operation_count": 0, "beta_prep": Q(0), "decision": "INITIAL_ONLY"}
    r0, r1, e0, e1 = estimate
    total = r0 + r1
    if not r0 or not r1:
        return {**common, "reason": "REFERENCE_RISK_PARAMETER_ZERO", "decision": "UNKNOWN"}
    nu = (r0 / total, r1 / total)
    prep = (Q(0), *nu)
    weights = [(Q(0), *nu)] * (T - 1) + [(Q(0), Q(1, 2), Q(1, 2))]
    source = reference_source(estimate, T)
    target = derive(source)
    if not target["Z"]:
        return {**common, "reason": "REFERENCE_CONDITIONING_UNDEFINED_NOT_TRUE_SOURCE_UNDEFINED", "decision": "UNKNOWN"}
    prepared = tuple(sum(Q(1, 2) * sum(prep[a] * source.P[x][a][z] for a in range(3))
                         for x in range(2)) for z in range(3))
    residuals = [max(tv(tuple(sum(w[a] * source.P[x][a][z] for a in range(3)) for z in range(3)),
                        target["R"][t][x]) for x in range(2)) for t, w in enumerate(weights)]
    initial_error = tv(prepared, target["mu"])
    reference_bound = min(Q(1), initial_error + sum(residuals))
    noise = max(e0, e1)
    beta = min(Q(1), (T + 1) * noise + (T + 1) * DELTA + T * DELTA / total)
    lower = min(Q(1, 6), max(Q(0), e0 - DELTA), max(Q(0), e1 - DELTA))
    failure_lower = 1 - (1 - lower) ** T
    if beta <= THRESHOLD:
        status, decision = "CANDIDATE_STATISTICAL_APPROX", "ACCEPT"
    elif failure_lower > THRESHOLD:
        status, decision = "CANDIDATE_STATISTICAL_NO_GO", "REJECT_STATISTICAL_LOWER"
    else:
        status, decision = "UNKNOWN", "UNKNOWN"
    return {**common, "status": status, "decision": decision, "nu": nu, "preparation": prep,
            "weights": weights, "reference_source_identity": source.identity,
            "reference_Z": target["Z"], "reference_initial": target["mu"], "reference_rows": target["R"],
            "reference_prepared": prepared, "reference_initial_residual": initial_error,
            "reference_row_residuals": residuals, "reference_path_bound": reference_bound,
            "coarse_reference_path_bound": min(Q(1), (T + 1) * noise), "beta_prep": beta,
            "failure_floor_lower": lower, "failure_probability_lower": failure_lower,
            "accepted_joint_risk_upper": ALPHA + (1 - ALPHA) * THRESHOLD}


def select(directory, T):
    try:
        counts, identity = read_training(directory)
        return {**candidate(counts, T), "data_identity": identity,
                "selector_sha256": digest(Path(__file__).read_bytes())}
    except (OSError, ValueError, TypeError, KeyError, IndexError) as error:
        return {"status": "INVALID_INPUT", "reason": str(error)}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("record", type=Path)
    parser.add_argument("--horizon", required=True, type=int)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    result = select(args.record, args.horizon)
    with args.output.open("xb") as stream:
        stream.write(encoded(result))
    print(json.dumps({"status": result["status"], "output": str(args.output)}))
