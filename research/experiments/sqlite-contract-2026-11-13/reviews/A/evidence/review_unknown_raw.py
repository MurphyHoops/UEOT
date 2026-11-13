"""A's bounded raw read of four UNKNOWN certification cases; no SQLite run."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
BASE = ROOT / "agents/B/evidence/full/retrieved/certification/run-v1"
manifest_bytes = (BASE / "FILE_MANIFEST.json").read_bytes()
manifest = {f["path"]: f for f in json.loads(manifest_bytes)}
allocation = json.loads((ROOT / "RUN_ALLOCATION.json").read_bytes())["certification"]
records = []
for spec in allocation:
    if spec["scenario"] != "COMMIT_NO_ACK_KILL":
        continue
    rid = spec["run_id"]
    hashes = {}
    failed = []

    def load(name, lines=False):
        relative = rid + "/" + name
        b = (BASE / relative).read_bytes()
        h = hashlib.sha256(b).hexdigest()
        matches = manifest[relative]["sha256"] == h and manifest[relative]["bytes"] == len(b)
        hashes[name] = {"sha256": h, "bytes": len(b), "matches_manifest": matches}
        if not matches:
            failed.append("manifest:" + name)
        return [json.loads(line) for line in b.splitlines()] if lines else json.loads(b)

    events = load("parent-events.jsonl", True)
    child = load("worker.stdout.raw", True)
    initial = load("oracle/initial.json")
    requests_file = load("oracle/requests.json")
    sent = [e["message"] for e in events if e["event"] == "PARENT_SENT"]
    received = [e["message"] for e in events if e["event"] == "CHILD_MESSAGE_RECEIVED"]
    requests = [m["request"] for m in sent if m["cmd"] == "TRANSACTION"]
    checks = {"raw_child_equals_received": child == received, "request_file_equals_sent": requests == requests_file}
    states = [initial]
    for request in requests:
        old = states[-1]
        by_key = {r[0]: list(r) for r in old["business"]}
        for key, value, token in request["updates"]:
            length = request["payload_length"]
            by_key[key] = [key, value, (token * (length // len(token) + 1))[:length]]
        states.append({"business": [by_key[k] for k in sorted(by_key)], "transactions": old["transactions"] + [[request["seq"], request["txn_id"], request["request_hash"]]]})
    last = requests[-1]["txn_id"]
    acks = [m["txn_id"] for m in received if m["event"] == "ACK"]
    checks["prior_acks_received_target_ack_absent"] = acks == [r["txn_id"] for r in requests[:-1]]
    checks["private_commit_return_hook_recorded"] = any(m["event"] == "COMMIT_RETURNED_NO_ACK" and m["txn_id"] == last for m in received)
    checks["no_go_ack_sent"] = not any(m["cmd"] == "GO_ACK" for m in sent)
    checks["worker_killed_and_reaped"] = any(e["event"] == "WORKER_REAPED" and e["returncode"] == -9 for e in events)
    canonical = lambda value: json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode()
    allowed_hashes = [hashlib.sha256(canonical(s)).hexdigest() for s in states[-2:]]
    inputs = []
    for policy in ["candidate", "strong_baseline"]:
        visible = load("policy/" + policy + "/execution/input.json")
        result = load("policy/" + policy + "/execution/result.json")
        inputs.append(visible)
        prefix = policy + ":"
        checks[prefix + "unknown_label_preserved"] = visible["ack_class"] == result["ack_class"] == "UNKNOWN"
        checks[prefix + "only_request_without_ack_certificate"] = visible["completion_certificate"] == {"kind": "REQUEST_WITHOUT_ACK", "txn_id": last}
        checks[prefix + "two_independently_rebuilt_allowed_hashes"] = visible["allowed_state_sha256"] == allowed_hashes
        checks[prefix + "no_private_stage_in_input"] = not any(k in visible for k in ["scenario", "expected_verdict", "COMMIT_RETURNED", "COMMIT_RETURNED_NO_ACK"])
        checks[prefix + "full_values_equal_S1"] = {"business": result["business"], "transactions": result["transactions"]} == states[-1]
        checks[prefix + "accepted_current_member"] = result["complete"] and result["decision"] == "ACCEPT_CURRENT_ALLOWED"
    checks["same_candidate_strong_visible_input"] = inputs[0] == inputs[1]
    failed.extend(k for k, value in checks.items() if not value)
    records.append({"spec": spec, "raw_received_ack_count": len(acks), "sent_transaction_count": len(requests), "public_ack_class": "UNKNOWN", "current_full_state": "S1", "allowed_state_count": 2, "checks": checks, "files_read_and_hashed": hashes, "failed_checks": failed})
out = {
    "status": "A_READ_REHASHED_AND_REDERIVED_FOUR_RAW_UNKNOWN_CASES_NO_SQLITE_EXECUTION",
    "manifest_sha256": hashlib.sha256(manifest_bytes).hexdigest(),
    "scope": "Exactly the four preregistered COMMIT_NO_ACK_KILL certification cases. Reconstruct current S0/S1 from retained raw sent requests, align raw child and parent receive sequence, and inspect actual public policy inputs and complete values. No new trial or Mac operation.",
    "cases": records, "failed_cases": [r["spec"]["run_id"] for r in records if r["failed_checks"]],
    "limit": "Private intervention logs record commit return; policy permission remains the public UNKNOWN contract. Actual full S1 membership does not create an ACK receive event or prove arbitrary past histories uniquely identifiable. Initial values and parent logs remain declared trust assumptions.",
}
p = Path(__file__).parent / "A_UNKNOWN_RAW_REVIEW.json"
p.write_text(json.dumps(out, ensure_ascii=False, indent=2) + "\n")
print(json.dumps({"count": len(records), "failed_cases": out["failed_cases"], "rows": [{"run_id": r["spec"]["run_id"], "requests": r["sent_transaction_count"], "acks": r["raw_received_ack_count"], "allowed": r["allowed_state_count"], "state": r["current_full_state"]} for r in records], "output_sha256": hashlib.sha256(p.read_bytes()).hexdigest()}, ensure_ascii=False))
