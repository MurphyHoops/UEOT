#!/usr/bin/env python3
"""Main-agent analysis of raw SQLite evidence; imports neither B nor C code.

Reconstructs the finite contract from the preregistered initial formula and
actual parent request/ACK stream. Full-value comparison does not assume that a
SHA256 digest is an injective mathematical representation. Costs have only the
disclosed logical measurement scope; this is not a physical-I/O measurement.
"""
import argparse
from collections import Counter, defaultdict
import datetime
import hashlib
import json
from pathlib import Path
import statistics


def read(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def canon(x):
    return json.dumps(x, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode()


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def demand(value, message):
    if not value:
        raise ValueError(message)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--allocation", required=True)
    ap.add_argument("--out", required=True)
    args = ap.parse_args()
    root = Path(args.root)
    manifest = read(root / "RUN_MANIFEST.json")
    split = manifest["split"]
    protocol = manifest["protocol"]
    planned = read(root / "RUNS_PLANNED.json")
    demand(planned == read(args.allocation)[split], "external frozen allocation mismatch")
    demand(manifest["authorization"]["preregistration_commit"] ==
           "26902c25152ca3676b4844d2156f028145f62fe2", "wrong preregistration")
    counters = defaultdict(Counter)
    numeric = defaultdict(lambda: defaultdict(list))
    rows = []
    issues = []
    for spec in planned:
        case = root / spec["run_id"]
        row = {"spec": spec}
        try:
            trial = read(case / "trial-result.json")
            row["status"] = trial["status"]
            counters["status"][trial["status"]] += 1
            demand(trial["status"] == "COMPLETE", "registered attempt incomplete")
            ev = [json.loads(s) for s in (case / "parent-events.jsonl").read_text().splitlines()]
            sent = [e["message"] for e in ev if e["event"] == "PARENT_SENT"]
            reqs = [m["request"] for m in sent if m["cmd"] == "TRANSACTION"]
            recv = [e["message"] for e in ev if e["event"] == "CHILD_MESSAGE_RECEIVED"]
            acks = [m for m in recv if m.get("event") == "ACK"]
            wl = protocol["workloads"][spec["workload"]]
            demand(len(reqs) == wl["history_transactions"] + 1, "request count mismatch")
            initial = []
            for key in range(wl["keys"]):
                token = "initial-%04d|" % key
                length = wl["payload_bytes"]
                initial.append([key, 10000 + key, (token * (length // len(token) + 1))[:length]])
            state = {"business": initial, "transactions": []}
            pre_final = None
            for n, q in enumerate(reqs, 1):
                demand(q["seq"] == n, "request sequence mismatch")
                plain = {k: v for k, v in q.items() if k != "request_hash"}
                demand(hashlib.sha256(canon(plain)).hexdigest() == q["request_hash"], "request hash mismatch")
                demand(sorted(u[0] for u in q["updates"]) == list(range(wl["keys"])), "incomplete update coverage")
                if n == len(reqs):
                    pre_final = state
                business = []
                for key, value, token in sorted(q["updates"]):
                    length = q["payload_length"]
                    business.append([key, value, (token * (length // len(token) + 1))[:length]])
                state = {"business": business,
                         "transactions": state["transactions"] + [[n, q["txn_id"], q["request_hash"]]]}
            final_id = reqs[-1]["txn_id"]
            ack_ids = {a["txn_id"] for a in acks}
            demand(all(q["txn_id"] in ack_ids for q in reqs[:-1]), "earlier ACK obligation missing")
            final_command = next(m for m in reversed(sent)
                                 if m.get("cmd") == "TRANSACTION" and m["request"]["txn_id"] == final_id)
            gated = (final_command.get("pause_precommit") is True
                     and any(m.get("event") == "PRECOMMIT_READY" and m.get("txn_id") == final_id for m in recv))
            if final_id in ack_ids:
                knowledge, allowed = "ACKED", [state]
            elif gated and not any(m.get("cmd") == "GO_COMMIT" for m in sent):
                demand(trial["worker_returncode"] == -9, "unreleased gate without reaped kill")
                knowledge, allowed = "NOT_COMMITTED", [pre_final]
            else:
                knowledge, allowed = "UNKNOWN", [pre_final, state]
            demand(knowledge == trial["ack_class"], "ACK knowledge mismatch")
            counters["ack_class"][knowledge] += 1
            row.update(ack_class=knowledge, actual_ack_count=len(acks), request_count=len(reqs),
                       worker_returncode=trial["worker_returncode"],
                       source_log_sha256=sha(case / "parent-events.jsonl"))
            observations = {}
            for name, declared in trial["policies"].items():
                obs = read(case / declared["result_relative_path"])
                observations[name] = obs
                counters[name][obs["decision"]] += 1
                demand(obs["ack_class"] == knowledge, name + " upgraded ACK")
                for field in ("callback_count", "rows_returned", "canonical_returned_bytes",
                              "elapsed_from_before_connect_ns", "oracle_summary_input_bytes"):
                    numeric[name][field].append(obs[field])
                for field in ("application_copy_read_bytes", "application_copy_write_bytes"):
                    numeric[name][field].append(declared["copy"][field])
                if obs["complete"] and name != "weak_structure":
                    measured = {"business": obs["business"], "transactions": obs["transactions"]}
                    membership = any(measured == a for a in allowed)
                    demand(obs["history_membership"] == membership, name + " exact membership mismatch")
                    if name in ("candidate", "strong_baseline"):
                        demand(obs["decision"] == ("ACCEPT_CURRENT_ALLOWED" if membership else "REJECT_HISTORY"),
                               name + " contradicted reconstructed contract")
                if spec["scenario"] == "BUDGET_ZERO":
                    demand(not obs["connect_attempted"] and obs["callback_count"] == 0, name + " zero-budget connect")
                if spec["scenario"] == "BUDGET_SMALL":
                    demand(obs["budget_exhausted"] and obs["callback_count"] == 32, name + " budget not exercised")
            candidate, baseline = observations["candidate"], observations["strong_baseline"]
            fields = ("decision", "ack_class", "config", "structure_ok", "history_membership",
                      "callback_count", "rows_returned", "canonical_returned_bytes", "business", "transactions")
            demand(all(candidate.get(k) == baseline.get(k) for k in fields), "candidate/baseline measured difference")
            row["candidate_strong_same_measured_logic"] = True
            row["candidate"] = {k: candidate.get(k) for k in ("decision", "callback_count", "rows_returned",
                                                               "canonical_returned_bytes", "connect_attempted")}
            row["policy_decisions"] = {k: v["decision"] for k, v in observations.items()}
            row["hot_header_candidate"] = any(x.get("journal_hot_header_candidate") for x in trial["postfault_files"])
            before = {x["name"]: x["sha256"] for x in trial["postfault_files"]}
            after = {x["name"]: x["sha256"] for x in trial["policies"]["candidate"]["files_after"]}
            row["candidate_db_changed"] = before.get("db.sqlite") != after.get("db.sqlite")
            row["candidate_journal_removed"] = "db.sqlite-journal" in before and "db.sqlite-journal" not in after
            row["candidate_sql_first"] = candidate["sql_observations"][0]["sql"] if candidate["sql_observations"] else None
        except Exception as exc:
            row["main_analysis_error"] = str(exc)
            issues.append({"run_id": spec["run_id"], "error": str(exc)})
        rows.append(row)
    costs = {}
    for policy, measures in numeric.items():
        costs[policy] = {}
        for key, values in measures.items():
            costs[policy][key] = {"n": len(values), "sum": sum(values), "min": min(values),
                                  "max": max(values), "median": statistics.median(values)}
    out = {"analysis": "independent main-agent raw request/full-value and cost reconstruction",
           "at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(), "split": split,
           "preregistration_commit": manifest["authorization"]["preregistration_commit"],
           "run_manifest_sha256": sha(root / "RUN_MANIFEST.json"),
           "allocation_sha256": sha(args.allocation), "script_sha256": sha(__file__),
           "registered": len(planned), "issues": issues, "all_registered_analysis_pass": not issues,
           "counts": {k: dict(v) for k, v in counters.items()}, "logical_costs": costs, "trials": rows,
           "limits": "Wall time starts after loading public input; logical copy length is not hardware I/O. No iid or performance superiority inference."}
    Path(args.out).write_text(json.dumps(out, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({k: out[k] for k in ("split", "registered", "all_registered_analysis_pass", "issues", "counts", "logical_costs")}, ensure_ascii=False))
    return 0 if not issues else 1


if __name__ == "__main__":
    raise SystemExit(main())
