#!/usr/bin/env python3
"""Explicit preregistration, then one three-record simulation batch; never retry.

Only this generator/evaluator opens private truth. The selector reads public
bitpacked training data. Exact rational RNG thresholds simulate the declared
source; linking the PRNG stream to the mathematical iid product law remains an
explicit sampling-interface assumption, not a claim about physical OS entropy.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
import json
from math import lcm
from pathlib import Path
import random
import secrets
import sys

from selector import ALPHA, DELTA, FORMAT, N, PROBES, THRESHOLD, digest, encoded, select

PARAMETERS = {"A": ("3/4", "1/4", "1/200", "1/200"),
              "B": ("4/5", "1/5", "1/300", "1/250"),
              "C": ("3/4", "1/4", "1/20", "1/20")}
HORIZONS = {"A": (2, 10), "B": (2, 10), "C": (10,)}
PROTOCOL = {"model": "RANK_ONE_RISK_NOISY_SELECTION_ABSORBING_CEMETERY_V1",
            "states": [0, 1, 2], "actions": ["risk", "select0", "select1"],
            "initial": ["1/2", "1/2", "0"], "safe": [0, 1], "observation": "constant",
            "baseline": "risk only", "training_permissions": "reset and state readout",
            "parameter_box": {"r0": ["2/3", "5/6"], "r1": ["1/6", "1/3"],
                              "e0": ["0", "1/20"], "e1": ["0", "1/20"]},
            "probe_order": list(PROBES), "probe_reset_states": [0, 1, 0, 0],
            "n_per_probe": N, "bit_format": FORMAT, "delta": str(DELTA),
            "alpha_per_record": str(ALPHA), "three_record_union_alpha": "1/100",
            "threshold": str(THRESHOLD), "accepted_joint_risk_bound": "76/375",
            "record_order": list(PARAMETERS), "horizons": HORIZONS,
            "preparation": "one selection mixture, no retry or success filtering",
            "record_rule": "all three complete raw records; rejected or unknown decisions do not deploy",
            "rng": "stdlib random.Random MT19937; independent OS-acquired 256-bit seeds frozen before sampling",
            "rng_interface_assumption": "Exact thresholding of the pseudorandom stream is simulation evidence. The formal product-probe law and source-faithfulness remain explicit assumptions."}


def write_new(path, value):
    path = Path(path)
    with path.open("xb") as stream:
        stream.write(value if isinstance(value, bytes) else encoded(value))


def code_identity():
    here = Path(__file__).resolve().parent
    paths = sorted(p for p in here.rglob("*.py") if "actual-execution" not in p.parts) + [here.with_name("action_certificates_v1") / "exact_certificates.py",
                                          Path(random.__file__).resolve(), Path(sys.executable).resolve()]
    return {str(p): digest(p.read_bytes()) for p in paths}


def freeze(directory, numerical_receipt):
    directory = Path(directory).resolve()
    receipt = Path(numerical_receipt).read_bytes()
    proof = json.loads(receipt)
    if type(proof.get("exit_code")) is not int or proof["exit_code"] != 0:
        raise ValueError("explicit successful numerical-proof receipt required before freezing")
    directory.mkdir(parents=True, exist_ok=False)
    private = {name: {"theta": theta, "training_seed": secrets.token_hex(32),
                       "deployment_seeds": {str(T): secrets.token_hex(32) for T in HORIZONS[name]}}
               for name, theta in PARAMETERS.items()}
    secret = encoded(private)
    write_new(directory / "generator-private.json", secret)
    (directory / "generator-private.json").chmod(0o600)
    write_new(directory / "NUMERICAL_PROOF.json", receipt)
    commitments = {name: {"training": digest(bytes.fromhex(row["training_seed"])),
                          "deployment": {T: digest(bytes.fromhex(seed)) for T, seed in row["deployment_seeds"].items()}}
                   for name, row in private.items()}
    public = {"schema": "UEOT/FINITE_DATA_BATCH_FREEZE/V1", "state": "FROZEN_NOT_SAMPLED",
              "protocol": PROTOCOL, "code_identity": code_identity(), "python_version": sys.version,
              "numerical_receipt_sha256": digest(receipt), "private_generator_sha256": digest(secret),
              "seed_commitments": commitments}
    write_new(directory / "FREEZE.json", public)
    return public


def verify_freeze(directory, *, check_code):
    directory = Path(directory).resolve(strict=True)
    data = (directory / "FREEZE.json").read_bytes()
    frozen = json.loads(data)
    if frozen["schema"] != "UEOT/FINITE_DATA_BATCH_FREEZE/V1" or frozen["protocol"] != json.loads(encoded(PROTOCOL)):
        raise ValueError("frozen protocol changed")
    if digest((directory / "generator-private.json").read_bytes()) != frozen["private_generator_sha256"]:
        raise ValueError("private generator identity changed")
    if digest((directory / "NUMERICAL_PROOF.json").read_bytes()) != frozen["numerical_receipt_sha256"]:
        raise ValueError("frozen numerical proof receipt changed")
    if check_code and (code_identity() != frozen["code_identity"] or sys.version != frozen["python_version"]):
        raise ValueError("code/runtime changed after freeze; no sampling permitted")
    return directory, frozen, digest(data)


def bernoulli_bits(p, rng, n):
    data = bytearray((n + 7) // 8)
    for i in range(n):
        if rng.randrange(p.denominator) < p.numerator:
            data[i // 8] |= 1 << (i % 8)
    return bytes(data)


def choose(weights, rng):
    weights = tuple(map(Q, weights))
    if any(x < 0 for x in weights) or sum(weights) != 1:
        raise ValueError("invalid sampling probability row")
    denominator = lcm(*(x.denominator for x in weights))
    value, cumulative = rng.randrange(denominator), 0
    for i, p in enumerate(weights):
        cumulative += p.numerator * (denominator // p.denominator)
        if value < cumulative:
            return i
    raise AssertionError("normalized exact row did not select an outcome")


def transition(theta, x, a):
    r0, r1, e0, e1 = map(Q, theta)
    if x == 2:
        return (Q(0), Q(0), Q(1))
    if a == 0:
        r = (r0, r1)[x]
        return (r / 2, r / 2, 1 - r)
    return (1 - e0, Q(0), e0) if a == 1 else (Q(0), 1 - e1, e1)


def realization(theta, proposal, seed):
    rng = random.Random(int(seed, 16))
    x = choose((Q(1, 2), Q(1, 2), Q(0)), rng)
    initial, operations = x, []
    rows = [proposal["preparation"], *proposal["weights"]]
    for k, weights in enumerate(rows):
        a = choose(weights, rng)
        z = choose(transition(theta, x, a), rng)
        operations.append({"phase": "prepare" if k == 0 else "deploy", "operation": k,
                           "before_state": x, "action": a, "after_state": z})
        x = z
    return {"status": "CANDIDATE_DEPLOYMENT_REALIZATION", "certificate_status": "CANDIDATE_ONLY",
            "initial_state_before_preparation": initial, "operations": operations,
            "post_preparation_window": [row["after_state"] for row in operations],
            "failure": any(row["after_state"] == 2 for row in operations),
            "operation_count": len(rows), "seed_commitment": digest(bytes.fromhex(seed))}


def sample(directory, numerical_receipt):
    directory, frozen, freeze_sha = verify_freeze(directory, check_code=True)
    if digest(Path(numerical_receipt).read_bytes()) != frozen["numerical_receipt_sha256"]:
        raise ValueError("explicit sampling release must name the frozen numerical receipt")
    # The exclusive marker forbids selecting a replacement seed or rerunning a
    # failed record. Repairs may re-read saved raw data without new sampling.
    write_new(directory / "SAMPLE_STARTED.json", {"freeze_sha256": freeze_sha, "rule": "one attempt, all records"})
    private = json.loads((directory / "generator-private.json").read_bytes())
    (directory / "decisions").mkdir()
    (directory / "deployments").mkdir()
    results = []
    for name in frozen["protocol"]["record_order"]:
        record = directory / "records" / name
        try:
            record.mkdir(parents=True, exist_ok=False)
            truth = private[name]
            rng = random.Random(int(truth["training_seed"], 16))
            probes = []
            for probe, probability in zip(PROBES, map(Q, truth["theta"])):
                raw = bernoulli_bits(probability, rng, N)
                write_new(record / (probe + ".bin"), raw)
                probes.append({"name": probe, "file": probe + ".bin", "sha256": digest(raw)})
            write_new(record / "training.json", {"schema": "UEOT/FINITE_DATA_TRAINING/V1", "record_id": name,
                      "format": FORMAT, "n": N, "probe_order": list(PROBES), "probes": probes,
                      "freeze_sha256": freeze_sha})
            decisions = []
            for T in frozen["protocol"]["horizons"][name]:
                proposal = select(record, T)
                decision_bytes = encoded(proposal)
                write_new(directory / "decisions" / f"{name}-T{T}.json", decision_bytes)
                if proposal.get("decision") == "ACCEPT":
                    deployment = realization(truth["theta"], proposal, truth["deployment_seeds"][str(T)])
                else:
                    deployment = {"status": "REJECTED_NO_DEPLOYMENT", "decision": proposal.get("decision"),
                                  "seed_commitment": frozen["seed_commitments"][name]["deployment"][str(T)]}
                deployment.update(decision_sha256=digest(decision_bytes),
                                  training_sha256=proposal.get("data_identity", {}).get("training_sha256"), T=T)
                deployment_bytes = encoded(deployment)
                write_new(directory / "deployments" / f"{name}-T{T}.json", deployment_bytes)
                decisions.append({"T": T, "status": proposal["status"], "decision": proposal.get("decision"),
                                  "decision_sha256": digest(decision_bytes), "deployment_sha256": digest(deployment_bytes)})
            results.append({"record": name, "state": "COMPLETE", "decisions": decisions})
        except (OSError, ValueError, KeyError, TypeError) as error:
            results.append({"record": name, "state": "ERROR_PRESERVED_NO_RETRY", "error": str(error)})
    result = {"schema": "UEOT/FINITE_DATA_SAMPLE_RESULT/V1", "freeze_sha256": freeze_sha,
              "state": "COMPLETE_ALL_RECORDS" if all(x["state"] == "COMPLETE" for x in results) else "PARTIAL",
              "records": results}
    write_new(directory / "SAMPLE_RESULT.json", result)
    return result


def evaluate_paths(theta, proposal):
    """Independent exact state/action marginal evaluation; never calls derive.

    Enumerate only 2^(T+1) safe histories. All cemetery histories have zero
    target mass, so their summed actual mass suffices for exact total variation.
    """
    from itertools import product
    T = proposal["T"]
    if not 1 <= T <= 10:
        raise ValueError("registered exhaustive evaluator supports T=1..10")
    weights = [tuple(map(Q, w)) for w in proposal["weights"]]
    prep = tuple(map(Q, proposal["preparation"]))
    initial = tuple(sum(Q(1, 2) * sum(prep[a] * transition(theta, x, a)[z] for a in range(3))
                        for x in range(2)) for z in range(3))
    rows = [tuple(tuple(sum(w[a] * transition(theta, x, a)[z] for a in range(3))
                              for z in range(3)) for x in range(3)) for w in weights]
    safe_actual, safe_baseline = {}, {}
    for path in product((0, 1), repeat=T + 1):
        actual, baseline = initial[path[0]], Q(1, 2)
        for t in range(T):
            actual *= rows[t][path[t]][path[t + 1]]
            baseline *= transition(theta, path[t], 0)[path[t + 1]]
        safe_actual[path], safe_baseline[path] = actual, baseline
    mass = sum(safe_baseline.values())
    if not mass:
        raise ValueError("true conditioning undefined in evaluator")
    failure = 1 - sum(safe_actual.values())
    variation = (sum(abs(safe_actual[p] - safe_baseline[p] / mass) for p in safe_actual) + failure) / 2
    # Independent dynamic recursion includes absorbing cemetery mass and is
    # checked against the compressed safe-history evaluation.
    marginal = initial
    for row in rows:
        marginal = tuple(sum(marginal[x] * row[x][z] for x in range(3)) for z in range(3))
    if failure != marginal[2]:
        raise AssertionError("path enumeration and absorbing-state recursion differ")
    return {"true_Z": mass, "actual_post_preparation_initial": initial,
            "full_window_tv": variation, "failure_including_preparation": failure,
            "safe_paths_enumerated": len(safe_actual), "dead_paths": "aggregated exactly, target mass zero",
            "operations": T + 1}


def evaluate(directory, output):
    directory, frozen, freeze_sha = verify_freeze(directory, check_code=False)
    private = json.loads((directory / "generator-private.json").read_bytes())
    rows = []
    for name in frozen["protocol"]["record_order"]:
        for T in frozen["protocol"]["horizons"][name]:
            proposal = select(directory / "records" / name, T)
            theta = tuple(map(Q, private[name]["theta"]))
            estimates = tuple(map(Q, proposal.get("estimate", ())))
            row = {"record": name, "T": T, "selector_status": proposal["status"],
                   "good_diagnostic_not_selector_input": len(estimates) == 4 and all(
                       abs(x - y) <= DELTA for x, y in zip(theta, estimates))}
            if "weights" in proposal and proposal["weights"]:
                row.update(evaluate_paths(theta, proposal))
                row["beta_holds_on_this_simulated_truth"] = row["full_window_tv"] <= proposal["beta_prep"]
            rows.append(row)
    result = {"schema": "UEOT/FINITE_DATA_INDEPENDENT_EVALUATION/V1", "freeze_sha256": freeze_sha,
              "original_code_identity": frozen["code_identity"], "evaluation_code_identity": code_identity(),
              "scope": "Evaluator alone reads true parameters. Retrospective Good is diagnostic, never fed to selection.",
              "records": rows,
              "known_parameter_obstacles": {"high_noise_T10": 1 - Q(19, 20) ** 10,
                                              "low_noise_T45": 1 - Q(199, 200) ** 45}}
    write_new(output, result)
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--freeze", type=Path)
    action.add_argument("--sample", type=Path)
    action.add_argument("--evaluate", type=Path)
    parser.add_argument("--numeric-proof", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.freeze or args.sample:
        if args.numeric_proof is None:
            parser.error("--numeric-proof is required for explicit freeze/sampling release")
        result = freeze(args.freeze, args.numeric_proof) if args.freeze else sample(args.sample, args.numeric_proof)
        print(json.dumps({"state": result["state"]}))
        if result["state"] == "PARTIAL":
            raise SystemExit(1)
    else:
        if args.output is None:
            parser.error("--output is required for evaluation")
        result = evaluate(args.evaluate, args.output)
        print(json.dumps({"evaluation_records": len(result["records"])}))
