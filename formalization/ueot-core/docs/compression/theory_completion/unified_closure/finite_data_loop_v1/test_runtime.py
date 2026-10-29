#!/usr/bin/env python3
"""Deterministic fixtures only: no registered data, seeds or sampling created."""
from fractions import Fraction as Q
import json
from pathlib import Path
from tempfile import TemporaryDirectory

from selector import N, DELTA, PROBES, FORMAT, candidate, count_bits, digest, encoded, select
from batch import evaluate_paths, realization


def fixture(root, counts):
    """Complete handcrafted unit bits, with no RNG, truth or registered record."""
    root = Path(root)
    directory = root / "records" / "unit"
    directory.mkdir(parents=True, exist_ok=False)
    numerical = encoded({"exit_code": 0, "scope": "unit fixture only, not a release"})
    (root / "NUMERICAL_PROOF.json").write_bytes(numerical)
    public = encoded({"numerical_receipt_sha256": digest(numerical), "scope": "synthetic unit fixture"})
    (root / "FREEZE.json").write_bytes(public)
    probes = []
    for probe, count in zip(PROBES, counts):
        raw = bytes([255]) * (count // 8) + (bytes([(1 << (count % 8)) - 1]) if count % 8 else b"")
        raw += bytes(N // 8 - len(raw))
        (directory / (probe + ".bin")).write_bytes(raw)
        probes.append({"name": probe, "file": probe + ".bin", "sha256": digest(raw)})
    meta = {"schema": "UEOT/FINITE_DATA_TRAINING/V1", "record_id": "deterministic-unit-fixture",
            "format": FORMAT, "n": N, "probe_order": list(PROBES), "probes": probes,
            "freeze_sha256": digest(public)}
    (directory / "training.json").write_bytes(encoded(meta))
    return directory, meta


def check():
    exact = candidate([3 * N // 4, N // 4, 0, 0], 2)
    assert exact["nu"] == (Q(3, 4), Q(1, 4))
    assert exact["preparation"] == (0, Q(3, 4), Q(1, 4))
    assert exact["weights"] == [(0, Q(3, 4), Q(1, 4)), (0, Q(1, 2), Q(1, 2))]
    assert exact["reference_initial_residual"] == exact["reference_path_bound"] == 0
    known_exact = evaluate_paths((Q(3, 4), Q(1, 4), 0, 0), exact)
    assert known_exact["true_Z"] == Q(1, 4) and known_exact["full_window_tv"] == 0
    assert known_exact["failure_including_preparation"] == 0
    low_counts = [3 * N // 4, N // 4, N // 200, N // 200]
    for T in (2, 10):
        proposal = candidate(low_counts, T)
        assert proposal["status"] == "CANDIDATE_STATISTICAL_APPROX"
        assert proposal["beta_prep"] <= Q(1, 5)
        assert proposal["reference_path_bound"] <= proposal["coarse_reference_path_bound"]
        evaluated = evaluate_paths((Q(3, 4), Q(1, 4), Q(1, 200), Q(1, 200)), proposal)
        assert evaluated["full_window_tv"] <= proposal["beta_prep"]
        assert evaluated["safe_paths_enumerated"] == 2 ** (T + 1)
        assert evaluated["failure_including_preparation"] == 1 - Q(199, 200) ** (T + 1)
        # Force preparation failure in a unit fixture, retain all T+1 operations.
        failed = realization((Q(3, 4), Q(1, 4), 1, 1), proposal, "00")
        assert failed["failure"] and len(failed["operations"]) == T + 1
        assert failed["post_preparation_window"] == [2] * (T + 1)
    negative = candidate([3 * N // 4, N // 4, N // 20, N // 20], 10)
    assert negative["status"] == "CANDIDATE_STATISTICAL_NO_GO"
    assert negative["failure_probability_lower"] > Q(1, 5)
    uncertain = candidate([3 * N // 4, N // 4, N // 40, N // 40], 10)
    assert uncertain["status"] == "UNKNOWN"
    assert candidate([0, 0, 0, 0], 2)["decision"] == "UNKNOWN"
    assert candidate([0, 0, 0, 0], 0)["actual_operation_count"] == 0
    assert count_bits(bytes([0b01010101, 0b00000011]), 10) == 6
    for data, n in [(b"", 8), (b"\xff", 1), (b"\x00\x00", 8)]:
        try:
            count_bits(data, n)
            raise AssertionError("malformed bytes accepted")
        except ValueError:
            pass
    with TemporaryDirectory() as temp:
        directory, meta = fixture(Path(temp), low_counts)
        probes = meta["probes"]
        selected = select(directory, 10)
        assert selected["status"] == "CANDIDATE_STATISTICAL_APPROX"
        assert selected["counts"] == tuple(low_counts)
        (directory / probes[0]["file"]).write_bytes(b"\x00")
        assert select(directory, 10)["status"] == "INVALID_INPUT"
        meta["probes"][0]["file"] = "../private.json"
        (directory / "training.json").write_bytes(encoded(meta))
        assert select(directory, 10)["status"] == "INVALID_INPUT"
    assert 1 - Q(199, 200) ** 45 > Q(1, 5)
    assert 1 - Q(19, 20) ** 10 > Q(1, 5)
    print("finite-data deterministic runtime, raw-byte rejection, independent exact path/preparation checks PASS; no registered sampling")


if __name__ == "__main__":
    check()
