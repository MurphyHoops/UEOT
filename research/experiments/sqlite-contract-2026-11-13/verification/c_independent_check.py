#!/usr/bin/env python3
"""C independent checker. Reads raw data; never imports the study runner."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys

def sha_bytes(data):
    return hashlib.sha256(data).hexdigest()

def canonical(obj):
    return json.dumps(obj, separators=(",", ":"), sort_keys=True, ensure_ascii=False).encode("utf-8")

def sha_obj(obj):
    return sha_bytes(canonical(obj))

def strict_pairs(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate JSON key: " + key)
        result[key] = value
    return result

def read_json(path):
    return json.loads(Path(path).read_text(encoding="utf-8"), object_pairs_hook=strict_pairs)

def read_lines(path):
    raw = Path(path).read_bytes()
    if raw and not raw.endswith(b"\n"):
        raise ValueError("unterminated JSONL: " + str(path))
    return [json.loads(line, object_pairs_hook=strict_pairs) for line in raw.decode("utf-8").splitlines()]

def check(condition, label, errors):
    if not condition:
        errors.append(label)
    return bool(condition)

def extend_state(prior, request):
    rows = {row[0]: list(row) for row in prior["business"]}
    for key, new_value, fragment in request["updates"]:
        length = request["payload_length"]
        full = (fragment * ((length // len(fragment)) + 1))[:length]
        rows[key] = [key, new_value, full]
    txs = [list(row) for row in prior["transactions"]]
    txs.append([request["seq"], request["txn_id"], request["request_hash"]])
    return {"business": [rows[k] for k in sorted(rows)], "transactions": txs}

def check_manifest(root, errors):
    entries = read_json(root / "FILE_MANIFEST.json")
    expected = {}
    for item in entries:
        name = item["path"]
        path = Path(name)
        if path.is_absolute() or ".." in path.parts or name in expected:
            errors.append("invalid or duplicate manifest path " + name)
            continue
        expected[name] = item
    actual_paths = {str(p.relative_to(root)) for p in root.rglob("*") if p.is_file()}
    check(actual_paths == set(expected) | {"FILE_MANIFEST.json"}, "payload file-set mismatch", errors)
    observed = {}
    for name, item in expected.items():
        path = root / name
        if not path.is_file() or path.is_symlink():
            errors.append("missing or symlink payload " + name)
            continue
        data = path.read_bytes()
        digest = sha_bytes(data)
        check(len(data) == item["bytes"] and digest == item["sha256"], "payload mismatch " + name, errors)
        observed[name] = {"bytes": len(data), "sha256": digest}
    return observed

def actual_set(root, directory, hashes):
    result = {}
    for path in directory.iterdir():
        if not path.is_file() or path.is_symlink():
            raise ValueError("unexpected DB snapshot entry " + str(path))
        key = str(path.relative_to(root))
        result[path.name] = hashes[key]
    return result

def declared_set(records):
    return {row["name"]: {"bytes": row["bytes"], "sha256": row["sha256"]} for row in records}

def observation_check(base, policy, allowed, visible, errors):
    execution = base / "execution"
    receipt = read_json(execution / "process.json")
    check(receipt["returncode"] == 0 and not receipt["timeout"], policy + " observer process did not finish", errors)
    result_file = execution / "result.json"
    if not result_file.exists():
        errors.append(policy + " missing observer raw result")
        return {"expected": "UNRESOLVED_EXECUTION", "observed": None}
    r = read_json(result_file)
    received_input = read_json(execution / "input.json")
    check(received_input == visible, policy + " public input differs", errors)
    forbidden = {"scenario", "workload", "run_id", "COMMIT_RETURNED_NO_ACK", "oracle_verdict"}
    check(not (forbidden & set(received_input)), policy + " forbidden input key", errors)
    budget = received_input["callback_budget"]
    used = r["callback_count"]
    check(isinstance(used, int) and 0 <= used <= budget, policy + " callback bound", errors)
    entries = r["sql_observations"]
    accumulated = 0
    returned_count = 0
    returned_bytes = 0
    for item in entries:
        check(item["callbacks_before"] == accumulated, policy + " noncontiguous callback ledger", errors)
        check(item["callbacks_after"] >= accumulated, policy + " decreasing callback ledger", errors)
        accumulated = item["callbacks_after"]
        returned_count += len(item["rows"])
        returned_bytes += sum(len(canonical(row)) for row in item["rows"])
    check(accumulated == used, policy + " callback total differs from SQL ledger", errors)
    check(returned_count == r["rows_returned"], policy + " returned row cost mismatch", errors)
    check(returned_bytes == r["canonical_returned_bytes"], policy + " returned byte cost mismatch", errors)
    check(r["oracle_summary_input_bytes"] == (execution / "input.json").stat().st_size,
          policy + " summary input byte mismatch", errors)
    if budget == 0:
        check(not r["connect_attempted"] and used == 0 and not entries, policy + " zero-budget work", errors)
    if r["budget_exhausted"]:
        check(used == budget and budget > 0, policy + " exhaustion does not reach threshold", errors)
        check(not r["complete"], policy + " complete despite budget exhaustion", errors)
    check(r["elapsed_from_before_connect_ns"] >= r.get("connect_elapsed_ns", 0),
          policy + " connect duration outside total", errors)
    by_sql = {}
    for item in entries:
        check(item["sql"] not in by_sql, policy + " duplicate SQL measurement", errors)
        by_sql[item["sql"]] = item["rows"]
    membership = None
    actual_state = None
    structure = None
    if not r["complete"]:
        expected = "UNRESOLVED_BUDGET" if budget == 0 or r["budget_exhausted"] else "UNRESOLVED_SQL_OR_OBSERVATION_ERROR"
    else:
        check(not r.get("exception"), policy + " complete with exception", errors)
        config = r["config"]
        effective = all(config.get(name) == value for name, value in {"journal_mode": "delete", "synchronous": 2}.items())
        check(r["config_valid"] == effective, policy + " config flag disagrees with values", errors)
        for name, value in config.items():
            check(by_sql.get("PRAGMA " + name) == [[value]], policy + " config readback rows " + name, errors)
        integrity = by_sql.get("PRAGMA integrity_check")
        foreign = by_sql.get("PRAGMA foreign_key_check")
        structure = integrity == [["ok"]] and foreign == []
        check(r.get("integrity_rows") == integrity and r.get("foreign_key_rows") == foreign,
              policy + " structure raw-result mismatch", errors)
        check(r["structure_ok"] == structure, policy + " structure flag mismatch", errors)
        if policy != "weak_structure":
            business = by_sql.get("SELECT id,value,payload FROM business ORDER BY id")
            txs = by_sql.get("SELECT seq,txn_id,request_hash FROM transactions ORDER BY seq")
            check(business is not None and txs is not None, policy + " missing full business/transaction scan", errors)
            check(business == r["business"] and txs == r["transactions"], policy + " flattened rows differ", errors)
            actual_state = {"business": business, "transactions": txs}
            membership = any(actual_state == state for state in allowed)
            check(r["history_membership"] == membership, policy + " digest membership differs from full-value equality", errors)
            check(r["actual_state_sha256"] == sha_obj(actual_state), policy + " actual-state digest mismatch", errors)
        if not effective:
            expected = "UNRESOLVED_CONFIGURATION"
        elif not structure:
            expected = "REJECT_STRUCTURE"
        elif policy == "weak_structure":
            expected = "STRUCTURE_OK"
        elif policy == "identity_ablation":
            biz, txs = actual_state["business"], actual_state["transactions"]
            invariant = (len(biz) == received_input["key_count"]
                         and [x[0] for x in biz] == list(range(received_input["key_count"]))
                         and all(type(x[1]) is int and x[1] > 0 for x in biz)
                         and [x[0] for x in txs] == list(range(1, len(txs) + 1))
                         and len({x[1] for x in txs}) == len(txs))
            check(invariant == r["internal_invariants"], policy + " internal invariant mismatch", errors)
            expected = "ACCEPT_ABLATED" if invariant else "REJECT_INTERNAL"
        else:
            expected = "ACCEPT_CURRENT_ALLOWED" if membership else "REJECT_HISTORY"
    check(r["decision"] == expected, policy + " independently recomputed decision differs", errors)
    return {"expected": expected, "observed": r["decision"], "complete": r["complete"],
            "callback_count": used, "budget": budget, "membership_exact": membership,
            "ack_class": r["ack_class"], "structure_ok": structure,
            "actual_state_sha256": sha_obj(actual_state) if actual_state is not None else None,
            "weak_projection": [r["connect_attempted"], r.get("integrity_rows"), r.get("foreign_key_rows")]}

def audit_trial(root, spec, protocol, hashes):
    case = root / spec["run_id"]
    errors = []
    out = {"spec": spec, "errors": errors}
    try:
        result = read_json(case / "trial-result.json")
        check(result["spec"] == spec, "trial spec differs from registered plan", errors)
        check(result["status"] == "COMPLETE", "trial not complete: " + result["status"], errors)
        events = read_lines(case / "parent-events.jsonl")
        child = read_lines(case / "worker.stdout.raw")
        received = [e["message"] for e in events if e["event"] == "CHILD_MESSAGE_RECEIVED"]
        check(received == child, "raw stdout and parent received messages differ", errors)
        check(all(events[i]["monotonic_ns"] <= events[i+1]["monotonic_ns"] for i in range(len(events)-1)),
              "parent event times regress", errors)
        sent = [(i,e["message"]) for i,e in enumerate(events) if e["event"] == "PARENT_SENT"]
        requests = [(i,m["request"],m) for i,m in sent if m["cmd"] == "TRANSACTION"]
        workload = protocol["workloads"][spec["workload"]]
        check(len(requests) == workload["history_transactions"] + 1, "request coverage differs", errors)
        check([q["seq"] for _,q,_ in requests] == list(range(1,len(requests)+1)), "request sequence invalid", errors)
        check(len({q["txn_id"] for _,q,_ in requests}) == len(requests), "duplicate transaction ID", errors)
        ack_events = [(i,e) for i,e in enumerate(events)
                      if e["event"] == "CHILD_MESSAGE_RECEIVED" and e["message"].get("event") == "ACK"]
        acks = {e["message"]["txn_id"]: (i,e) for i,e in ack_events}
        check(len(acks) == len(ack_events), "duplicate ACK received", errors)
        for send_index, request, _ in requests:
            plain = {key:value for key,value in request.items() if key != "request_hash"}
            check(sha_obj(plain) == request["request_hash"], "request hash mismatch", errors)
            if request["txn_id"] in acks:
                receive_index, event = acks[request["txn_id"]]
                check(receive_index > send_index, "ACK precedes request", errors)
                committed = [i for i,e in enumerate(events) if e["event"] == "CHILD_MESSAGE_RECEIVED"
                             and e["message"].get("event") == "COMMIT_RETURNED_NO_ACK"
                             and e["message"].get("txn_id") == request["txn_id"]]
                check(len(committed) == 1 and send_index < committed[0] < receive_index, "ACK lacks earlier commit-return event", errors)
                check(event["message"]["seq"] == request["seq"], "ACK sequence mismatch", errors)
            bound = [[value, (token*((request["payload_length"]//len(token))+1))[:request["payload_length"]], key]
                     for key,value,token in request["updates"]]
            bindings = [e for e in child if e.get("event") == "SQL_BINDING_WITNESS" and e.get("txn_id") == request["txn_id"]]
            check(len(bindings) == 1 and bindings[0]["bound_parameters_sha256"] == sha_obj(bound),
                  "bound SQL parameters not matched to request", errors)
        initial = read_json(case / "oracle" / "initial.json")
        check(initial["transactions"] == [], "unexpected initial transaction history", errors)
        check([row[0] for row in initial["business"]] == list(range(workload["keys"])), "initial key domain differs", errors)
        state = initial
        for n, (_,request,_) in enumerate(requests[:-1]):
            check(request["txn_id"] in acks, "historical request lacks ACK", errors)
            if request["txn_id"] in acks:
                check(acks[request["txn_id"]][0] < requests[n+1][0], "next request predates historical ACK", errors)
            state = extend_state(state, request)
        prior = state
        _,last,last_command = requests[-1]
        final = extend_state(prior,last)
        last_ack = acks.get(last["txn_id"])
        gate_ready = [e for e in child if e.get("event") == "PRECOMMIT_READY" and e.get("txn_id") == last["txn_id"]]
        released = [m for _,m in sent if m.get("cmd") == "GO_COMMIT" and m.get("txn_id") == last["txn_id"]]
        reaped = [e for e in events if e["event"] == "WORKER_REAPED"]
        if last_ack is not None:
            knowledge, allowed = "ACKED", [final]
        elif last_command.get("pause_precommit") and len(gate_ready) == 1 and not released and any(e["returncode"] == -9 for e in reaped):
            knowledge, allowed = "NOT_COMMITTED", [prior]
        else:
            knowledge, allowed = "UNKNOWN", [prior,final]
        check(read_json(case / "oracle" / "requests.json") == [q for _,q,_ in requests], "saved requests differ from actual sent", errors)
        check(read_json(case / "oracle" / "ack_events.json") == [e for _,e in ack_events], "saved ACKs differ from actual received", errors)
        check(read_json(case / "oracle" / "allowed_states.json") == allowed, "B allowed states differ from C reconstruction", errors)
        check(result["ack_class"] == knowledge, "B knowledge label differs", errors)
        expected_environment = protocol.get("expected_environment", {})
        runtime = result["worker_environment"]
        for field in ["sqlite_version", "sqlite_source_id"]:
            if field in expected_environment:
                check(runtime[field] == expected_environment[field], "runtime pin differs: " + field, errors)
        if "compile_options_sha256" in expected_environment:
            check(sha_obj(runtime["compile_options"]) == expected_environment["compile_options_sha256"], "compile-options pin differs", errors)
        for binary in ["python", "_sqlite3"]:
            field = binary + "_binary_sha256"
            if field in expected_environment:
                check(runtime["binaries"][binary]["sha256"] == expected_environment[field], "binary pin differs: " + binary, errors)
        if spec["scenario"].endswith("_KILL"):
            kills = [e for e in events if e["event"] == "SIGKILL_SENT"]
            check(len(kills) == 1 and len(reaped) == 1 and reaped[0]["returncode"] == -9,
                  "registered kill not attained exactly", errors)
        if spec["scenario"] == "COMMIT_NO_ACK_KILL":
            check(knowledge == "UNKNOWN" and any(e.get("event") == "COMMIT_RETURNED_NO_ACK" and e.get("txn_id") == last["txn_id"] for e in child),
                  "unknown-ACK barrier not attained", errors)
        if spec["scenario"] == "STALE_BACKUP":
            replacement = [e for e in events if e["event"] == "OLD_BACKUP_REPLACED"]
            check(len(replacement) == 1 and replacement[0]["source_sha256"] == replacement[0]["new_target_sha256"],
                  "old backup replacement not attained", errors)
        raw = actual_set(root, case / "postfault_raw", hashes)
        check(raw == declared_set(result["postfault_files"]), "original snapshot differs from receipt", errors)
        check(result["original_unchanged"] is True, "producer original-unchanged gate failed", errors)
        policies = {}
        reference_visible = read_json(case / "policy" / "candidate" / "execution" / "input.json")
        check(reference_visible["ack_class"] == knowledge, "public knowledge differs", errors)
        check(reference_visible["allowed_state_sha256"] == [sha_obj(s) for s in allowed], "public allowed digests differ", errors)
        check(reference_visible["key_count"] == workload["keys"], "public key count differs", errors)
        expected_budget = protocol["budgets"]["zero" if spec["scenario"] == "BUDGET_ZERO" else "small" if spec["scenario"] == "BUDGET_SMALL" else "high"]
        check(reference_visible["callback_budget"] == expected_budget, "public budget differs from protocol", errors)
        for name in ["candidate","strong_baseline","weak_structure","identity_ablation"]:
            record = result["policies"][name]
            check(declared_set(record["copy"]["source_files"]) == raw and declared_set(record["copy"]["clone_files_before_open"]) == raw,
                  name + " clone pre-open receipt differs from original", errors)
            after = actual_set(root, case / "policy" / name / "database", hashes)
            check(after == declared_set(record["files_after"]), name + " post-observation DB differs", errors)
            policies[name] = observation_check(case / "policy" / name, name, allowed, reference_visible, errors)
            check(record["decision"] == policies[name]["observed"], name + " trial decision differs from observer raw record", errors)
        judge_input = read_json(case / "adjudication" / "execution" / "input.json")
        check(judge_input == dict(reference_visible,callback_budget=protocol["budgets"]["adjudication"]), "judge has unexpected inputs", errors)
        judge = observation_check(case / "adjudication", "strong_baseline", allowed, judge_input, errors)
        check(judge["complete"] is True, "raw adjudication did not finish", errors)
        check(policies["candidate"]["observed"] == policies["strong_baseline"]["observed"], "candidate/strong decisions differ", errors)
        if spec["scenario"] not in ["BUDGET_ZERO","BUDGET_SMALL"]:
            desired = "REJECT_HISTORY" if spec["scenario"] == "STALE_BACKUP" else "ACCEPT_CURRENT_ALLOWED"
            check(policies["candidate"]["expected"] == desired, "mandatory decidable cell failed", errors)
        if spec["scenario"] == "BUDGET_ZERO":
            check(policies["candidate"]["expected"] == "UNRESOLVED_BUDGET", "zero-budget cell failed", errors)
        out.update({"ack_class_C": knowledge, "allowed_state_count_C":len(allowed),
                    "policies":policies, "adjudication_exact_membership_C":judge["membership_exact"],
                    "worker_source_id":result["worker_environment"]["sqlite_source_id"],
                    "original_files_verified":len(raw)})
    except Exception as exc:
        errors.append(type(exc).__name__ + ": " + str(exc))
    out["passed_independent_checks"] = not errors
    return out

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--root",required=True)
    parser.add_argument("--out",required=True)
    parser.add_argument("--preregistration-commit")
    args = parser.parse_args()
    root = Path(args.root).resolve()
    outpath = Path(args.out).resolve()
    if outpath.exists():
        raise RuntimeError("refusing to overwrite existing C result")
    errors = []
    manifest = read_json(root / "RUN_MANIFEST.json")
    if args.preregistration_commit:
        check(manifest["authorization"]["preregistration_commit"] == args.preregistration_commit, "preregistration commit differs", errors)
    hashes = check_manifest(root,errors)
    specs = read_json(root / "RUNS_PLANNED.json")
    protocol = manifest["protocol"]
    allocation = protocol["allocations"][manifest["split"]]
    expected = {(w,s,r) for w in allocation["workloads"] for s in allocation.get("scenarios", protocol["scenarios"]) for r in range(allocation["repetitions"])}
    observed = {(s["workload"],s["scenario"],s["repetition"]) for s in specs}
    check(observed == expected and len(specs) == len(expected), "planned scenario coverage differs", errors)
    check(len({s["run_id"] for s in specs}) == len(specs), "duplicate planned run ID", errors)
    results = [audit_trial(root,s,protocol,hashes) for s in specs]
    counts = Counter(r.get("policies",{}).get("candidate",{}).get("observed","MISSING") for r in results)
    report = {"checker":"C_INDEPENDENT_RAW_RECONSTRUCTION_V2","checker_sha256":sha_bytes(Path(__file__).read_bytes()),
              "root":str(root),"split":manifest["split"],"preregistration_commit":args.preregistration_commit,
              "runner_sha256_recorded":manifest["runner_sha256"],"protocol_sha256_recorded":manifest["protocol_sha256"],
              "raw_files_directly_rehashed":len(hashes),"global_errors":errors,
              "planned":len(specs),"trials_checked":len(results),
              "trials_without_check_errors":sum(r["passed_independent_checks"] for r in results),
              "candidate_observed_counts":dict(counts),"trials":results,
              "boundary":"Exact permitted-state equality rebuilt from raw sent requests/received ACKs; no B import or verdict generator. Clone-before-open identity is historical producer record, compared to directly rehashed immutable source; post-run files directly rehashed."}
    outpath.parent.mkdir(parents=True,exist_ok=True)
    outpath.write_text(json.dumps(report,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({k:report[k] for k in ["split","raw_files_directly_rehashed","global_errors","planned","trials_checked","trials_without_check_errors","candidate_observed_counts"]},ensure_ascii=False))
    return 0 if not errors and all(r["passed_independent_checks"] for r in results) else 2

if __name__ == "__main__":
    sys.exit(main())

