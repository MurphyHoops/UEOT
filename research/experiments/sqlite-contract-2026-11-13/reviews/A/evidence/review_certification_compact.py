"""A's read-only reaggregation of B's retained certification readback.

This does not execute SQLite or independently rebuild the oracle from raw events.
"""
import collections
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
BASE = ROOT / "agents/B/evidence/certification/retrieved"
COMPACT = BASE / "exports/B-certification-v2/CERTIFICATION_COMPACT.json"


def read(path):
    return json.loads(path.read_bytes())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


x = read(COMPACT)
receipt_path = BASE / "certification/v1-controller-receipt.json"
receipt = read(receipt_path)
summary_path = BASE / "certification/run-v1/SUMMARY.json"
summary = read(summary_path)
planned_path = BASE / "certification/run-v1/RUNS_PLANNED.json"
planned = read(planned_path)
allocation = read(ROOT / "RUN_ALLOCATION.json")
rows = x["trials"]
summary_rows = summary["results"]
summary_by_id = {t["spec"]["run_id"]: t for t in summary_rows}
if isinstance(planned, dict):
    planned = planned.get("trials", planned.get("runs", planned.get("planned")))
registered = allocation["certification"] if "certification" in allocation else allocation["allocations"]["certification"]
if isinstance(registered, dict):
    registered = registered.get("trials", registered.get("runs", registered.get("planned")))
decisions = collections.Counter()
by_scenario = {}
hot_rows = []
failures = []
out_rows = []
cost_fields = ["callback_count", "rows_returned", "canonical_returned_bytes", "clone_read_bytes", "clone_write_bytes", "oracle_summary_input_bytes"]
costs = {policy: {field: 0 for field in cost_fields} for policy in ["candidate", "strong_baseline"]}
for t in rows:
    spec = t["spec"]
    rid = spec["run_id"]
    a, b = t["policies"]["candidate"], t["policies"]["strong_baseline"]
    s = summary_by_id[rid]
    checks = {
        "summary_spec_same": s["spec"] == spec,
        "summary_status_same": s["status"] == t["status"],
        "summary_ack_same": s["ack_class"] == t["ack_class"],
        "source_config": t["worker_config"]["journal_mode"] == "delete" and t["worker_config"]["synchronous"] == 2,
        "both_status_complete": t["status"] == "COMPLETE",
        "candidate_and_strong_same_decision": a["decision"] == b["decision"],
        "candidate_and_strong_cost_fields_equal": all(a[field] == b[field] for field in cost_fields),
        "candidate_and_strong_state_fields_equal": all(a[field] == b[field] for field in ["complete", "config_valid", "structure_ok", "history_membership", "actual_state_sha256", "budget_exhausted", "budget_within"]),
        "ack_labels_preserved": a["ack_class"] == b["ack_class"] == t["ack_class"],
        "original_recorded_unchanged": t["original_unchanged"] is True,
    }
    for policy in ["candidate", "strong_baseline"]:
        p = t["policies"][policy]
        checks[policy + "_summary_decision"] = p["decision"] == s["policies"][policy]["decision"]
        checks[policy + "_successful_observer_process"] = p["process_returncode"] == 0 and not p["process_timeout"]
        for field in cost_fields:
            costs[policy][field] += p[field]
    scenario = spec["scenario"]
    expected = "REJECT_HISTORY" if scenario == "STALE_BACKUP" else "UNRESOLVED_BUDGET" if scenario.startswith("BUDGET_") else "ACCEPT_CURRENT_ALLOWED"
    checks["registered_decision"] = a["decision"] == expected
    if scenario == "COMMIT_NO_ACK_KILL":
        checks["unknown_retained"] = t["ack_class"] == "UNKNOWN" and a["complete"] and a["history_membership"] is True
    if scenario == "PRECOMMIT_KILL":
        cert = t["completion_certificate"]
        checks["withheld_commit_certificate"] = t["ack_class"] == "NOT_COMMITTED" and cert["kind"] == "PRECOMMIT_GATE_WITHHELD" and cert["ready_received"] and not cert["go_commit_sent"] and cert["worker_reaped_returncode"] == -9
        hot_rows.append({"run_id": rid, "workload": spec["workload"], **t["hot_journal_observation"]})
    if scenario == "STALE_BACKUP":
        checks["stale_structure_and_ablation"] = t["policies"]["weak_structure"]["decision"] == "STRUCTURE_OK" and t["policies"]["identity_ablation"]["decision"] == "ACCEPT_ABLATED" and a["history_membership"] is False
        checks["same_run_current_snapshot_retained"] = t["pre_replacement_current_copy"] is not None
    if scenario == "BUDGET_ZERO":
        checks["zero_no_connect"] = not a["connect_attempted"] and a["callback_count"] == 0 and not a["complete"] and a["rows_returned"] == 0
    if scenario == "BUDGET_SMALL":
        checks["small_actual_interrupt_first_pragma"] = a["callback_count"] == 32 and a["budget_exhausted"] and not a["complete"] and a["rows_returned"] == 0 and len(a["sql_stages"]) == 1 and a["sql_stages"][0]["sql"] == "PRAGMA journal_mode=DELETE" and a["exception"]["message"] == "interrupted"
    failed = [key for key, value in checks.items() if not value]
    if failed:
        failures.append({"run_id": rid, "checks": failed})
    decisions[a["decision"]] += 1
    key = spec["workload"] + "/" + scenario
    by_scenario.setdefault(key, collections.Counter())[a["decision"]] += 1
    out_rows.append({"spec": spec, "ack_class": t["ack_class"], "candidate": a["decision"], "strong": b["decision"], "candidate_callbacks": a["callback_count"], "weak": t["policies"]["weak_structure"]["decision"], "ablation": t["policies"]["identity_ablation"]["decision"], "checks": checks})

frozen_ids = [r["run_id"] for r in registered]
actual_ids = [t["spec"]["run_id"] for t in rows]
record = {
    "status": "A_READ_AND_REAGGREGATED_RETAINED_B_COMPACT_NOT_RAW_ORACLE_RECONSTRUCTION",
    "scope": "A read all 28 compact entries and compared retained controller/summary/allocation and recorded branch facts. B's raw full-value recomputation labels are not counted as A's independent full-value or Mac execution.",
    "input_files": {str(p.relative_to(ROOT)): {"sha256": sha(p), "bytes": p.stat().st_size} for p in [COMPACT, receipt_path, summary_path, planned_path, ROOT / "RUN_ALLOCATION.json"]},
    "registration_commit": receipt["authorization"]["preregistration_commit"],
    "controller_exit": receipt["subprocess_returncode"],
    "controller_started_utc": receipt["started_utc"],
    "controller_finished_utc": receipt["finished_utc"],
    "summary_sha_matches_receipt": sha(summary_path) == receipt["SUMMARY.json"]["sha256"],
    "planned_sha_matches_receipt": sha(planned_path) == receipt["RUNS_PLANNED.json"]["sha256"],
    "frozen_allocation_ids_exact_order": actual_ids == frozen_ids,
    "planned_specs_equal_compact_specs": planned == [t["spec"] for t in rows],
    "count": len(rows),
    "decisions": dict(decisions),
    "ack_counts": dict(collections.Counter(t["ack_class"] for t in rows)),
    "by_workload_scenario": {k: dict(v) for k, v in by_scenario.items()},
    "cost_totals_recomputed_from_entries": costs,
    "hot_precommit_entries": hot_rows,
    "failed_checks": failures,
    "rows": out_rows,
    "still_needed": ["C independent raw request/ACK/gate and full-value reconstruction", "C seven fresh separated replication receipts", "A key full-value and corresponding raw-history readback"],
}
out = Path(__file__).parent / "A_CERTIFICATION_COMPACT_REVIEW.json"
out.write_text(json.dumps(record, ensure_ascii=False, indent=2) + "\n")
print(json.dumps({k: record[k] for k in ["status", "count", "frozen_allocation_ids_exact_order", "planned_specs_equal_compact_specs", "decisions", "ack_counts", "cost_totals_recomputed_from_entries", "hot_precommit_entries", "failed_checks"]}, ensure_ascii=False))
print("OUTPUT_SHA256", sha(out))
