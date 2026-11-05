#!/usr/bin/env python3
"""Independent exact reference for the decision-representation contract.

The optimizer is the PRE-EXISTING memoized PR441 Planner.  Its key still
contains the complete physical Store and normalized posterior, not the new
count summary.  New work here is an execution adapter and explicit timing /
identity / native-path evidence.  This file never substitutes a Python policy
for a Lean artifact and does not rerun the old Lean tree producer.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import platform
import resource
import signal
import sys
import time
from fractions import Fraction as Q

STARTED = time.perf_counter()
REFERENCE_SHA256 = "b81f62cbe65c3d01d32b2d74910db0e6999b144f249d79e93a8367a2fa9cad5f"
CONTRACT_SHA256 = "d4c7134344f81a885265863a013a846af6a53829864877b3686eb1f16306de80"
INPUTS_SHA256 = "43bbea5dac37be2036977e2dc1ef7f3976ee10fec3db5196eb2a9e72270f8847"

CASES = {
    "two": dict(name="persistent_theta_two_step", r=["1/4", "3/4"], prior=["1/2", "1/2"],
        H=2, B="1", c="1", price="13/10", d="1/2", prior_value="1/160"),
    "three": dict(name="population_backup_three_step", r=["1/4", "3/4"], prior=["1/2", "1/2"],
        H=3, B="1", c="1", price="7/4", d="3/4", prior_value="9/256"),
    "posterior": dict(name="posterior_changes_retry_three_step", r=["1/4", "3/4"], prior=["1/2", "1/2"],
        H=3, B="1", c="1", price="13/10", d="1/2", prior_value="27/320"),
    "four": dict(name="receipt_feedback_four_step", r=["3/4", "7/8"], prior=["1/2", "1/2"],
        H=4, B="1", c="1", price="37/16", d="3/4", prior_value="39525/524288"),
    "long": dict(name="registered_h8_two_write_wallet", r=["1/4", "3/4"], prior=["1/2", "1/2"],
        H=8, B="2", c="1", price="13/10", d="3/4", prior_value=None),
}


class TimeBudgetExceeded(Exception):
    pass


def timed_out(_signum, _frame):
    raise TimeBudgetExceeded("The registered single-solve wall-clock budget expired")


def load_reference(path: Path):
    raw = path.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    if digest != REFERENCE_SHA256:
        raise ValueError("PR441 reference bytes do not match the frozen executed source")
    spec = importlib.util.spec_from_file_location("ueot_pr441_reference", path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module, digest


def max_rss_bytes():
    # macOS reports bytes; Linux reports KiB. This is process peak RSS, including
    # interpreter and loaded source, not a claim about abstract DAG storage.
    rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return int(rss if sys.platform == "darwin" else rss * 1024)


def native_prefix(ref, requests, modes, labels, budget, tariff):
    """Original full-record replay of one declared legal diagnostic prefix."""
    founder = ref.Organism(False, True, (), ((0, False),), 0)
    store, balance, stopped = (founder,), budget, False
    records, history, paid_count = [], [], 0
    for action, mode, label in zip(requests, modes, labels):
        demand = tariff if action is not None and action[1] is not None else Q(0)
        if balance < demand:
            raise AssertionError("Diagnostic requests an unaffordable write before its outcome")
        effective = (0, None) if stopped or action is None else action
        stopped = stopped or action is None
        store, obs, fee, record = ref.native_step(store, effective, mode, label, tariff)
        balance -= fee
        if balance < 0:
            raise AssertionError("Native prefix has a negative balance")
        paid_count += int(obs[1])
        history.append([ref.action_json(action), list(obs)])
        record["balance"] = ref.rat(balance)
        record["requested_action"] = ref.action_json(action)
        record["stopped"] = stopped
        records.append(record)
    return {
        "requested_prefix": history, "modes": list(modes), "labels": list(labels),
        "records": records,
        "final_physical_store": [None if x is None else x.physical for x in store],
        "final_balance": ref.rat(balance), "paid_count": paid_count,
        "final_store_size": len(store), "final_stopped": stopped,
    }


def distinguishing_native_checks(ref):
    # No stochastic resampling: these exact fixed source words witness the
    # registered semantics. They are not a Monte Carlo optimality claim.
    wr, idle, child = (0, True), (0, None), (1, None)
    two_paid = native_prefix(ref, [wr, wr], [True, True], [False, False], Q(2), Q(1))
    assert two_paid["paid_count"] == 2 and two_paid["final_balance"] == "0"
    merge_a = native_prefix(ref, [wr, idle, child], [True, False, True], [False]*3, Q(1), Q(1))
    merge_b = native_prefix(ref, [wr, child, idle], [True, True, False], [False]*3, Q(1), Q(1))
    assert merge_a["final_physical_store"] == [False, True, None, True]
    assert merge_b["final_physical_store"] == [False, True, True, None]
    bad_idle_a = native_prefix(ref, [wr, idle, idle], [True, True, False], [False]*3, Q(1), Q(1))
    bad_idle_b = native_prefix(ref, [wr, idle, idle], [True, False, True], [False]*3, Q(1), Q(1))
    stop = native_prefix(ref, [wr, None, (1, None)], [True]*3, [False]*3, Q(1), Q(1))
    assert [r[1] for r in stop["requested_prefix"]] == [[True, True], [True, False], [True, False]]
    wrong = native_prefix(ref, [(0, False), wr, child], [True]*3, [False]*3, Q(2), Q(1))
    assert wrong["paid_count"] == 2 and wrong["requested_prefix"][0][1] == [False, True]
    assert wrong["final_physical_store"] == [True, None, True, None]
    absent = native_prefix(ref, [(1, True), wr, child], [True]*3, [False]*3, Q(2), Q(1))
    assert absent["paid_count"] == 1 and absent["final_physical_store"] == [True, None, True, None]
    return {
        "status": "PASS",
        "scope": "Fixed distinguishing original-Store prefixes; no new optimality claim",
        "two_actual_payments": {
            "role": "Independent feasible diagnostic strategy, not asserted to be optimal",
            "fixed_theta_mode_mass": "r^2",
            "registered_prior_mode_mass": "5/16",
            "specified_label_and_mode_mass": "5/64",
            "execution": two_paid,
        },
        "merge_with_different_tail_a": merge_a,
        "merge_with_different_tail_b": merge_b,
        "insufficient_body_a": bad_idle_a,
        "insufficient_body_b": bad_idle_b,
        "stop_preserves_world_ticks": stop,
        "wrong_write_charged_and_child1_remains_none": wrong,
        "absent_child_request_keeps_allocated_none": absent,
    }


def run_case(ref, case_key, out: Path, solve_budget: float):
    spec = CASES[case_key]
    rs, prior = tuple(map(Q, spec["r"])), tuple(map(Q, spec["prior"]))
    planner = ref.Planner(rs, prior, Q(spec["price"]), Q(spec["d"]), Q(spec["c"]))
    # This is the same existing lru_cache, cleared only to obtain a fair
    # independent per-process measurement, never a replacement naive baseline.
    planner.solve.cache_clear()
    result = {
        "schema": "UEOT/DECISION_REPRESENTATION_REFERENCE/V1", "case": spec["name"],
        "parameters": {**spec, "goal": True, "initial_damaged": True},
        "baseline": "PR441 existing normalized-posterior / full-PackedStore lru_cache Planner",
        "reference_source_sha256": REFERENCE_SHA256,
        "adapter_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "declared_frozen_contract_sha256": CONTRACT_SHA256,
        "declared_frozen_inputs_sha256": INPUTS_SHA256,
        "python": platform.python_version(), "platform": platform.platform(),
        "single_solve_budget_seconds": solve_budget,
    }
    signal.signal(signal.SIGALRM, timed_out)
    signal.setitimer(signal.ITIMER_REAL, solve_budget)
    solve_start = time.perf_counter()
    try:
        value, action = planner.solve(spec["H"], prior, (False,), Q(spec["B"]))
    except TimeBudgetExceeded as exc:
        result.update(status="UNKNOWN", reason=str(exc),
            solve_seconds=time.perf_counter()-solve_start,
            planner_cache=planner.solve.cache_info()._asdict(), peak_process_rss_bytes=max_rss_bytes())
        (out/"REFERENCE_RESULT.json").write_text(json.dumps(result, indent=2)+"\n")
        return result, 2
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
    result["solve_seconds"] = time.perf_counter()-solve_start
    result["cache_immediately_after_solve"] = planner.solve.cache_info()._asdict()
    result["value"] = ref.rat(value)
    result["initial_action"] = ref.action_json(action)
    if spec["prior_value"] is not None:
        assert value == Q(spec["prior_value"]), "Independent reference disagrees with the preserved PR441 value"
    export_start = time.perf_counter()
    policy = planner.make_table(spec["H"], Q(spec["B"]))
    policy_raw = json.dumps(policy, ensure_ascii=False, indent=2).encode()
    (out/"REFERENCE_POLICY.json").write_bytes(policy_raw)
    result.update(export_seconds=time.perf_counter()-export_start,
        reference_policy_nodes=len(policy),
        reference_policy_edges=sum(len(n["branches"]) for n in policy),
        reference_policy_bytes=len(policy_raw),
        reference_policy_sha256=hashlib.sha256(policy_raw).hexdigest())
    check_start = time.perf_counter()
    if spec["H"] <= 4:
        replay, traces = planner.replay_table(spec["H"], Q(spec["B"]), policy)
        raw = json.dumps(traces, ensure_ascii=False, indent=2).encode()
        (out/"REFERENCE_NATIVE_TRACES.json").write_bytes(raw)
        result["complete_native_replay"] = {**replay, "traces_sha256": hashlib.sha256(raw).hexdigest()}
    else:
        result["complete_native_replay"] = {
            "performed": False,
            "reason": "Long instance uses exact memo DP and the general source bridge; no exhaustive mode-label tape expansion is required.",
        }
    checks = distinguishing_native_checks(ref)
    (out/"DISTINGUISHING_NATIVE_PREFIXES.json").write_text(json.dumps(checks, ensure_ascii=False, indent=2)+"\n")
    result.update(status="PASS", checking_seconds=time.perf_counter()-check_start,
        planner_cache=planner.solve.cache_info()._asdict(),
        peak_process_rss_bytes=max_rss_bytes(),
        total_adapter_seconds=time.perf_counter()-STARTED,
        qualification="Reference policy is distinct from THIS Lean DAG. Independent value comparison does not substitute it for the Lean returned artifact.")
    (out/"REFERENCE_RESULT.json").write_text(json.dumps(result, ensure_ascii=False, indent=2)+"\n")
    return result, 0


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--reference-source", type=Path, required=True)
    parser.add_argument("--case", choices=CASES, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--solve-budget", type=float, default=300)
    args = parser.parse_args()
    if not 0 < args.solve_budget <= 300:
        parser.error("the frozen first-solve budget is at most 300 seconds")
    args.output.mkdir(parents=True, exist_ok=True)
    if (args.output/"REFERENCE_RESULT.json").exists():
        parser.error("use a fresh output directory; prior attempts must remain intact")
    loading = time.perf_counter()
    ref, _ = load_reference(args.reference_source)
    load_seconds = time.perf_counter()-loading
    result, code = run_case(ref, args.case, args.output, args.solve_budget)
    result["reference_loading_seconds"] = load_seconds
    (args.output/"REFERENCE_RESULT.json").write_text(json.dumps(result, ensure_ascii=False, indent=2)+"\n")
    print(json.dumps(result, ensure_ascii=False, indent=2))
    return code


if __name__ == "__main__":
    sys.exit(main())
