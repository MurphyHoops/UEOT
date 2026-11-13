"""A re-derives eight decisive cases from the transferred C evidence bundle.

No SQLite execution, no import of B/C implementations, no B allowed-state list
or membership/verdict used as truth. File transitions are read from C's retained
direct-query records, not rehashed on the Mac by A.
"""
import collections
import hashlib
import json
import uuid
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
SRC = ROOT / "agents/C/C_DECISIVE_CERT_EVIDENCE.json"
blob = SRC.read_bytes()
x = json.loads(blob)
namespace = uuid.UUID("2e9f8b25-482b-44ad-a8bf-8836b6c097a3")


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()


def repeat(token, length):
    return (token * (length // len(token) + 1))[:length]


def key_files(files):
    return files if isinstance(files, dict) else {f["name"]: f for f in files}


out_cases = []
for direct in x["direct_record"]["results"]:
    rid = direct["run_id"]
    raw = x["source_records"][rid]
    spec = raw["trial_spec"]
    workload = x["protocol"]["workloads"][spec["workload"]]
    keys, payload_length, history_count = workload["keys"], workload["payload_bytes"], workload["history_transactions"]
    failures = []

    def check(ok, label):
        if not ok:
            failures.append(label)

    initial = {"business": [[i, 10000 + i, repeat("initial-%04d|" % i, payload_length)] for i in range(keys)], "transactions": []}
    check(initial == raw["initial"], "initial_equals_registered_formula")
    events = raw["parent_events"]
    sent = [e["message"] for e in events if e["event"] == "PARENT_SENT"]
    received = [e["message"] for e in events if e["event"] == "CHILD_MESSAGE_RECEIVED"]
    check(received == raw["raw_child_messages"], "parent_received_equals_raw_child_sequence")
    requests = [m["request"] for m in sent if m["cmd"] == "TRANSACTION"]
    check(len(requests) == history_count + 1, "request_count")
    ready = next(m for m in received if m["event"] == "READY")
    check(ready["environment"]["sqlite_source_id"] == x["protocol"]["expected_environment"]["sqlite_source_id"], "runtime_source_id")
    check(ready["config"]["journal_mode"] == "delete" and ready["config"]["synchronous"] == 2, "effective_configuration")
    ack_ids = [m["txn_id"] for m in received if m["event"] == "ACK"]
    request_ids = [r["txn_id"] for r in requests]
    check(all(request_ids) and len(set(request_ids)) == len(request_ids), "nonempty_unique_request_ids")
    states = [initial]
    for seq, request in enumerate(requests, 1):
        tid = str(uuid.uuid5(namespace, rid + "/txn/" + str(seq)))
        check(request["txn_id"] == tid and request["seq"] == seq, "request_identity_%d" % seq)
        check(request["payload_length"] == payload_length, "payload_length_%d" % seq)
        raw_request_without_hash = {k: v for k, v in request.items() if k != "request_hash"}
        check(hashlib.sha256(canonical(raw_request_without_hash)).hexdigest() == request["request_hash"], "request_hash_%d" % seq)
        prior = states[-1]
        expected_updates = [[key, old_value + (key + seq) % 7 - 3, hashlib.sha256((tid + ":" + str(key)).encode()).hexdigest()] for key, old_value, _ in prior["business"]]
        check(request["updates"] == expected_updates, "registered_updates_%d" % seq)
        next_state = {
            "business": [[key, value, repeat(token, payload_length)] for key, value, token in expected_updates],
            "transactions": prior["transactions"] + [[seq, tid, request["request_hash"]]],
        }
        states.append(next_state)
    summary = {
        "run_id": rid, "workload": spec["workload"], "scenario": spec["scenario"],
        "request_count": len(requests), "actually_received_ack_count": len(ack_ids),
        "business_row_count": keys, "initial_and_requests_rederived_from_registered_formula": True,
        "source_id": ready["environment"]["sqlite_source_id"],
    }
    if spec["scenario"] == "STALE_BACKUP":
        check(ack_ids == request_ids, "all_requests_acked_in_order")
        check(any(e["event"] == "OLD_BACKUP_REPLACED" for e in events), "replacement_recorded")
        check(any(e["event"] == "TARGET_PROCESS_STOPPED" and e["returncode"] == 0 for e in events), "clean_worker_stop")
        current = direct["observations"]["current"]
        stale = direct["observations"]["stale"]
        check(current["state"] == states[-1], "current_full_values_equal_H_allowed_S1")
        check(stale["state"] == states[1], "stale_full_values_equal_first_acked_prefix")
        check(stale["state"] != states[-1], "stale_not_H_allowed")
        check(current["weak_projection"] == stale["weak_projection"], "same_frozen_weak_projection")
        check(current["weak_projection"] == {"opened": True, "integrity": [["ok"]], "foreign_keys": []}, "projection_exact_definition")
        check(current["source_unchanged"] and stale["source_unchanged"], "C_recorded_originals_unchanged")
        summary.update({
            "H_ack_class_from_raw": "ACKED", "allowed_state_count": 1,
            "current_exact_allowed": current["state"] == states[-1],
            "stale_exact_allowed": stale["state"] == states[-1],
            "current_transaction_sequences": [r[0] for r in current["state"]["transactions"]],
            "stale_transaction_sequences": [r[0] for r in stale["state"]["transactions"]],
            "different_business_rows": sum(a != b for a, b in zip(current["state"]["business"], stale["state"]["business"])),
            "weak_projection": current["weak_projection"],
            "same_weak_projection_recomputed": current["weak_projection"] == stale["weak_projection"],
        })
    elif spec["scenario"] == "PRECOMMIT_KILL":
        last_id = request_ids[-1]
        target_command = [m for m in sent if m["cmd"] == "TRANSACTION"][-1]
        check(target_command.get("pause_precommit") is True, "target_pause_before_commit")
        check(not any(m["cmd"] == "GO_COMMIT" for m in sent), "no_commit_gate_release_sent")
        check(ack_ids == request_ids[:-1], "only_prior_requests_acked")
        check(any(m["event"] == "PRECOMMIT_READY" and m["txn_id"] == last_id and m["transaction_active"] for m in received), "target_precommit_ready_received")
        check(not any(m["event"] == "COMMIT_RETURNED_NO_ACK" and m["txn_id"] == last_id for m in received), "target_no_commit_return")
        check(any(e["event"] == "WORKER_REAPED" and e["returncode"] == -9 for e in events), "worker_killed_and_reaped")
        observed = direct["observation"]
        check(observed["state"] == states[-2], "recovered_full_values_equal_S0")
        check(observed["source_unchanged"], "C_recorded_original_unchanged")
        before, after = key_files(observed["before"]), key_files(observed["after"])
        journal = before.get("db.sqlite-journal", {})
        magic = (journal.get("first28") or journal.get("journal_header_28_hex") or "").startswith("d9d505f920a163d7")
        changed = before["db.sqlite"]["sha256"] != after["db.sqlite"]["sha256"]
        removed = "db.sqlite-journal" in before and "db.sqlite-journal" not in after
        summary.update({
            "H_ack_class_from_raw": "NOT_COMMITTED", "allowed_state_count": 1,
            "observed_exact_S0": observed["state"] == states[-2],
            "transaction_sequences": [r[0] for r in observed["state"]["transactions"]],
            "journal_bytes_before": journal.get("bytes"), "valid_magic_from_C_recorded_bytes": magic,
            "database_recorded_hash_changed": changed, "journal_recorded_removed": removed,
            "full_hot_witness_from_records": magic and changed and removed and observed["state"] == states[-2],
        })
    else:
        check(False, "unexpected_case")
    summary["failures"] = failures
    summary["passed_A_value_and_event_checks"] = not failures
    out_cases.append(summary)

# Separately bind and inspect all 35 of C's independently generated checks.
alloc = json.loads((ROOT / "RUN_ALLOCATION.json").read_bytes())
all_checks = []
for split, filename in [("certification", "CERTIFICATION_INDEPENDENT_CHECK.json"), ("replication", "REPLICATION_INDEPENDENT_CHECK.json")]:
    file = ROOT / "agents/C" / filename
    data = json.loads(file.read_bytes())
    trial_rows = data["trials"]
    all_checks.append({
        "split": split, "file_sha256": hashlib.sha256(file.read_bytes()).hexdigest(),
        "exact_registered_specs_and_order": [r["spec"] for r in trial_rows] == alloc[split],
        "count": len(trial_rows), "C_direct_rehashed_count": data["raw_files_directly_rehashed"],
        "global_errors": data["global_errors"],
        "trial_error_count": sum(len(r["errors"]) for r in trial_rows),
        "all_C_checks_passed": all(r["passed_independent_checks"] for r in trial_rows),
        "C_candidate_observed_counts": data["candidate_observed_counts"],
        "all_unknown_have_two_allowed_states": all(r["allowed_state_count_C"] == 2 for r in trial_rows if r["ack_class_C"] == "UNKNOWN"),
        "source_identity_set": sorted(set(r["worker_source_id"] for r in trial_rows)),
    })

result = {
    "status": "A_READ_AND_REDERIVED_TRANSFERRED_DECISIVE_VALUES_NO_SQLITE_EXECUTION",
    "evidence_bundle_sha256": hashlib.sha256(blob).hexdigest(), "evidence_bundle_bytes": len(blob),
    "preregistration_commit": x["preregistration_commit"],
    "scope": "Eight certification decisive cases: four fixed-H current/stale pairs and four precommit observations. Initial formula, request formula/hash, parent/child message alignment, ACK/gate classes, and complete state arrays are recomputed by A. C performed SQLite reads and Mac file hashing; A reads C's retained values and file transition records. Seven replication cases are assessed via C's complete independent check report, not newly executed or individually reconstructed by A here.",
    "cases": out_cases,
    "total_decisive_cases": len(out_cases), "failed_cases": [r["run_id"] for r in out_cases if r["failures"]],
    "all_35_C_check_records_read": all_checks,
    "limits": ["Shared trust in actual parent logs, initial input, frozen driver, runtime, and transferred record integrity remains.", "Matching the registered initializer formula is not a new physical before-fault measurement.", "No physical I/O bound, power-loss test, service restart, retry policy, independent external operator, or new Lean instantiation is inferred."],
}
path = Path(__file__).parent / "A_DECISIVE_FULL_VALUE_REVIEW.json"
path.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
print(json.dumps({"bundle_sha256": result["evidence_bundle_sha256"], "decisive_cases": len(out_cases), "failed_cases": result["failed_cases"], "cases": [{k: v for k, v in c.items() if k not in ["source_id", "weak_projection"]} for c in out_cases], "C_reports": all_checks}, ensure_ascii=False))
print("OUTPUT_SHA256", hashlib.sha256(path.read_bytes()).hexdigest())
