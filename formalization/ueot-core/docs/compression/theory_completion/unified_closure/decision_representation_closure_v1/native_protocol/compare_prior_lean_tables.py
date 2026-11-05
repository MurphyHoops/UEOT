#!/usr/bin/env python3
"""Compare actual PR441 tables to actual checked compact DAGs on positive support.

This adapter reads prior successful bytes and current successful certificates.
It calls neither optimizer, and never expands a long-horizon observation tree.
"""
from fractions import Fraction as Q
from pathlib import Path
import argparse
import hashlib
import json


NAMES = {
    "two": "persistent_theta_two_step",
    "three": "population_backup_three_step",
    "posterior": "posterior_changes_retry_three_step",
    "four": "receipt_feedback_four_step",
}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def compare(packet, prior_packet, case, old_report):
    name = NAMES[case]
    saved = next(x for x in old_report["results"] if x["case"] == name)
    assert saved["status"] == "PASS"
    old_path = (prior_packet / "actual-execution/lean-smoke-four-01/stdout.log"
        if case == "four" else prior_packet / f"actual-execution/lean-final-02/{case}/stdout.log")
    old_raw = old_path.read_bytes()
    assert sha(old_raw) == saved["lean_output_sha256"], "old table is not the preserved successful output"
    old = json.loads(old_raw)
    new_path = packet / f"actual-execution/{case}-01/stdout.json"
    new_raw = new_path.read_bytes()
    new = json.loads(new_raw)
    check_path = packet / f"independent-execution/{case}-01/THIS_DAG_CHECK.json"
    check_raw = check_path.read_bytes()
    check = json.loads(check_raw)
    assert check["status"] == "PASS" and check["dag_output_sha256"] == sha(new_raw)
    for field in ("case", "horizon", "normal_probabilities", "prior", "tariff",
                  "price", "discount", "wallet", "goal", "initial_damaged", "value"):
        assert old[field] == new[field], f"old and new declared inputs/value differ: {field}"
    old_rows = {tuple(tuple(o) for o in row["history"]): row["action"] for row in old["rows"]}
    assert len(old_rows) == len(old["rows"]), "old table has duplicate histories"
    nodes = new["nodes"]
    compared = []
    terminal_mass = Q(0)
    frontier = [(new["root_id"], (), Q(1))]
    while frontier:
        index, history, mass = frontier.pop()
        row = nodes[index]
        if row["remaining"] == 0:
            terminal_mass += mass
            continue
        action = row["chosen_action"]
        assert mass > 0 and old_rows[history] == action, "positive-history action differs"
        compared.append({"history": [list(o) for o in history], "action": action,
            "current_node": index, "positive_history_mass": str(mass)})
        alt = next(x for x in row["alternatives"] if x["action"] == action)
        for edge in alt["edges"]:
            probability = Q(edge["prob"])
            assert probability > 0
            frontier.append((edge["next"], history + (tuple(edge["obs"]),), mass * probability))
    assert terminal_mass == 1
    assert len(compared) == saved["reachable_decision_histories"]
    return {"case": name, "status": "PASS", "prior_table_sha256": sha(old_raw),
        "current_dag_sha256": sha(new_raw), "current_check_sha256": sha(check_raw),
        "prior_serialized_rows": len(old_rows), "positive_decision_histories": len(compared),
        "same_action_at_every_positive_history": True, "terminal_mass": str(terminal_mass),
        "comparisons": sorted(compared, key=lambda x: (len(x["history"]), x["history"]))}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--packet", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--prior-packet", type=Path)
    parser.add_argument("--case", choices=NAMES, action="append")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists() or args.output.is_symlink():
        parser.error("preserve prior attempts by choosing a new output file")
    prior_packet = args.prior_packet or args.packet.parent / "joint_decision_closure_v1"
    old_path = prior_packet / "actual-execution/THIS-final-02/THIS_LEAN_TABLE_CHECK.json"
    old_raw = old_path.read_bytes()
    result = {"schema": "UEOT/DECISION_REPRESENTATION_PRIOR_ACTION_COMPARISON/V1",
        "adapter_sha256": sha(Path(__file__).read_bytes()), "prior_success_report_sha256": sha(old_raw),
        "scope": "Actual old and new Lean artifacts, positive supported decision histories only; no solver call or old tree regeneration"}
    try:
        result["results"] = [compare(args.packet, prior_packet, case, json.loads(old_raw))
            for case in (args.case or list(NAMES))]
        result["status"] = "PASS"
        code = 0
    except (AssertionError, KeyError, ValueError, OSError) as exc:
        result.update(status="FAIL", reason=str(exc))
        code = 1
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("x", encoding="utf-8") as output:
        output.write(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps(result, ensure_ascii=False, indent=2))
    return code


if __name__ == "__main__":
    raise SystemExit(main())
