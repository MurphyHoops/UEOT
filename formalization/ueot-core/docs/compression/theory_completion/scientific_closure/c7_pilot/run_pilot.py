#!/usr/bin/env python3
import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
WORKER = ROOT / "worker.py"
REPS = 5
PREREGISTRATION_COMMIT = "1b3e01d236f65e42ceff83a0c2bc152fca293bbb"

class Worker:
    def __init__(self, worker_id: str):
        self.worker_id = worker_id
        self.p = subprocess.Popen(
            [sys.executable, str(WORKER), worker_id],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1,
        )

    @property
    def pid(self):
        return self.p.pid

    def alive(self):
        return self.p.poll() is None

    def ping(self, token: str):
        if not self.alive():
            return {"worker_id": self.worker_id, "pid": self.pid, "status": "DEAD", "latency_ns": None}
        t0 = time.monotonic_ns()
        self.p.stdin.write(f"PING {token}\n")
        self.p.stdin.flush()
        line = self.p.stdout.readline()
        t1 = time.monotonic_ns()
        if not line:
            return {"worker_id": self.worker_id, "pid": self.pid, "status": "NO_REPLY", "latency_ns": t1-t0}
        payload = json.loads(line)
        payload["latency_ns"] = t1 - t0
        return payload

    def terminate(self):
        if self.alive():
            self.p.terminate()
            try:
                self.p.wait(timeout=2)
            except subprocess.TimeoutExpired:
                self.p.kill()
                self.p.wait(timeout=2)
        return self.p.returncode

    def close(self):
        if self.alive():
            try:
                self.p.stdin.write("STOP\n")
                self.p.stdin.flush()
                self.p.wait(timeout=1)
            except Exception:
                self.terminate()
        if self.p.stdin:
            self.p.stdin.close()
        if self.p.stdout:
            self.p.stdout.close()
        if self.p.stderr:
            self.p.stderr.close()


def utc_now():
    return dt.datetime.now(dt.timezone.utc).isoformat()


def quorum(n):
    return n // 2 + 1


def service_query(workers, candidate_size, token):
    replies = [w.ping(token) for w in workers if w.alive()]
    ok = sum(1 for r in replies if r.get("status") == "OK")
    q = quorum(candidate_size)
    return {
        "candidate_size": candidate_size,
        "quorum": q,
        "ok_replies": ok,
        "service_output": "OK" if ok >= q else "UNAVAILABLE",
        "worker_replies": replies,
    }


def fresh_workers(ids):
    workers=[]
    try:
        for worker_id in ids:
            workers.append(Worker(worker_id))
        return workers
    except BaseException:
        cleanup(workers)
        raise


def cleanup(workers):
    for w in workers:
        w.close()


def record(run_id, split, protocol, candidate_ids, action, query, expected, replacement=None):
    observed = query["service_output"]
    return {
        "timestamp_utc": utc_now(),
        "run_id": run_id,
        "split": split,
        "protocol": protocol,
        "candidate_ids": candidate_ids,
        "action": action,
        "replacement": replacement,
        "query": query,
        "expected_service_output": expected,
        "matches_expected": observed == expected,
    }


def run_read(candidate_ids, run_id, split):
    workers = fresh_workers(candidate_ids)
    try:
        q = service_query(workers, len(candidate_ids), run_id)
        return record(run_id, split, "P_READ", candidate_ids, "none", q, "OK")
    finally:
        cleanup(workers)


def run_single_fault(candidate_ids, run_id, split):
    workers = fresh_workers(candidate_ids)
    try:
        victim = workers[-1]
        victim_pid = victim.pid
        rc = victim.terminate()
        q = service_query(workers, len(candidate_ids), run_id)
        expected = "OK" if len(candidate_ids) >= 3 else "UNAVAILABLE"
        return record(run_id, split, "P_SINGLE_FAULT", candidate_ids,
                      {"terminated": victim.worker_id, "pid": victim_pid, "returncode": rc}, q, expected)
    finally:
        cleanup(workers)


def run_replacement(run_id):
    workers = fresh_workers(["W1", "W2", "W3"])
    try:
        old = workers.pop()
        old_pid = old.pid
        old_rc = old.terminate()
        new = Worker("W4")
        workers.append(new)
        read = service_query(workers, 3, run_id + "-read")
        # Held-out single fault is applied to the newly inserted component.
        new_pid = new.pid
        new_rc = new.terminate()
        fault = service_query(workers, 3, run_id + "-single-fault")
        return {
            "timestamp_utc": utc_now(),
            "run_id": run_id,
            "split": "holdout",
            "protocol": "P_REPLACE_HELDOUT",
            "candidate_ids_before": ["W1", "W2", "W3"],
            "candidate_ids_after": ["W1", "W2", "W4"],
            "replacement": {"old_id":"W3", "old_pid":old_pid, "old_returncode":old_rc,
                            "new_id":"W4", "new_pid":new_pid, "new_returncode_after_fault":new_rc},
            "read_query": read,
            "single_fault_query": fault,
            "expected_read": "OK",
            "expected_single_fault": "OK",
            "matches_expected": read["service_output"] == "OK" and fault["service_output"] == "OK",
        }
    finally:
        cleanup(workers)


def run_double_fault(run_id):
    workers = fresh_workers(["W1", "W2", "W3"])
    try:
        actions=[]
        for victim in workers[1:]:
            pid=victim.pid
            rc=victim.terminate()
            actions.append({"terminated":victim.worker_id,"pid":pid,"returncode":rc})
        q = service_query(workers, 3, run_id)
        return record(run_id, "negative_control", "P_DOUBLE_FAULT", ["W1","W2","W3"], actions, q, "UNAVAILABLE")
    finally:
        cleanup(workers)


def logical_signature(records):
    return [
        {
            "run_id": r["run_id"],
            "split": r["split"],
            "protocol": r["protocol"],
            "matches_expected": r["matches_expected"],
            "service_output": r.get("query", {}).get("service_output"),
            "read_output": r.get("read_query", {}).get("service_output"),
            "heldout_fault_output": r.get("single_fault_query", {}).get("service_output"),
        }
        for r in records
    ]


def sha256(path):
    h=hashlib.sha256()
    with open(path,"rb") as f:
        for chunk in iter(lambda:f.read(1<<20), b""):
            h.update(chunk)
    return h.hexdigest()


class DurableJsonlWriter:
    """Exclusive, append-in-order raw evidence writer.

    The raw file is created *before* the first registered attempt.  Every
    completed attempt, including an execution error, is flushed and fsynced
    before the next attempt may start.  Therefore an interrupted label cannot
    be silently rerun: the raw path already exists and the normal entry point
    refuses to overwrite it.
    """

    def __init__(self, path: Path):
        self.path = Path(path)
        self._file = open(self.path, "x", encoding="utf-8", buffering=1)

    def append(self, payload):
        self._file.write(json.dumps(payload, sort_keys=True) + "\n")
        self._file.flush()
        os.fsync(self._file.fileno())

    def close(self):
        if not self._file.closed:
            self._file.close()

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc, tb):
        self.close()


def execution_error_record(run_id, split, protocol, candidate_ids, exc):
    return {
        "timestamp_utc": utc_now(),
        "run_id": run_id,
        "split": split,
        "protocol": protocol,
        "candidate_ids": list(candidate_ids),
        "record_status": "EXECUTION_ERROR",
        "matches_expected": False,
        "error_type": type(exc).__name__,
        "error_message": str(exc),
    }


def execute_attempt(writer, *, run_id, split, protocol, candidate_ids, thunk):
    """Execute one registered attempt and durably persist its outcome.

    Any Python-level failure is converted to an `EXECUTION_ERROR` record before
    it is re-raised.  Hard process termination can prevent that final record,
    but the already-created raw file and all prior fsynced rows remain, so the
    verifier sees missing run IDs and the same label cannot be silently reused.
    """
    try:
        payload = thunk()
        if payload.get("run_id") != run_id:
            raise RuntimeError(
                f"registered run id mismatch: expected {run_id}, got {payload.get('run_id')}"
            )
        payload = dict(payload)
        payload.setdefault("record_status", "OBSERVED")
        writer.append(payload)
        return payload
    except BaseException as exc:
        writer.append(execution_error_record(run_id, split, protocol, candidate_ids, exc))
        raise


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--label", required=True)
    ap.add_argument("--inject-failure-run-id", help=argparse.SUPPRESS)
    args=ap.parse_args()
    raw=ROOT / f"raw_{args.label}.jsonl"
    summary_path=ROOT / f"summary_{args.label}.json"
    if raw.exists() or summary_path.exists():
        raise SystemExit(f"refusing to overwrite existing evidence for label {args.label}")

    records=[]

    def durable_attempt(writer, *, run_id, split, protocol, candidate_ids, thunk):
        def guarded():
            if args.inject_failure_run_id == run_id:
                raise RuntimeError(f"injected test failure for {run_id}")
            return thunk()
        return execute_attempt(
            writer,
            run_id=run_id,
            split=split,
            protocol=protocol,
            candidate_ids=candidate_ids,
            thunk=guarded,
        )

    # The raw evidence path is reserved before any worker is launched.  A
    # partial/failed attempt therefore permanently occupies the label.
    with DurableJsonlWriter(raw) as writer:
        # Registered certification candidate family.
        for n in [1,2,3]:
            ids=[f"W{i}" for i in range(1,n+1)]
            for rep in range(1,REPS+1):
                read_id=f"cert-n{n}-read-r{rep}"
                records.append(durable_attempt(
                    writer,
                    run_id=read_id,
                    split="certification",
                    protocol="P_READ",
                    candidate_ids=ids,
                    thunk=lambda ids=ids, run_id=read_id: run_read(ids, run_id, "certification"),
                ))
                fault_id=f"cert-n{n}-single-r{rep}"
                records.append(durable_attempt(
                    writer,
                    run_id=fault_id,
                    split="certification",
                    protocol="P_SINGLE_FAULT",
                    candidate_ids=ids,
                    thunk=lambda ids=ids, run_id=fault_id: run_single_fault(ids, run_id, "certification"),
                ))

        # Held-out replacement, negative control, and naive baseline are
        # separate registered groups.
        for rep in range(1,REPS+1):
            replace_id=f"holdout-replace-r{rep}"
            records.append(durable_attempt(
                writer,
                run_id=replace_id,
                split="holdout",
                protocol="P_REPLACE_HELDOUT",
                candidate_ids=["W1","W2","W3"],
                thunk=lambda run_id=replace_id: run_replacement(run_id),
            ))
            negative_id=f"neg-double-r{rep}"
            records.append(durable_attempt(
                writer,
                run_id=negative_id,
                split="negative_control",
                protocol="P_DOUBLE_FAULT",
                candidate_ids=["W1","W2","W3"],
                thunk=lambda run_id=negative_id: run_double_fault(run_id),
            ))
            baseline_id=f"baseline-single-r{rep}"
            records.append(durable_attempt(
                writer,
                run_id=baseline_id,
                split="baseline",
                protocol="P_SINGLE_FAULT",
                candidate_ids=["W1"],
                thunk=lambda run_id=baseline_id: run_single_fault(["W1"], run_id, "baseline"),
            ))

    def group(prefix):
        return [r for r in records if r["run_id"].startswith(prefix)]

    first_good=None
    candidate_results={}
    for n in [1,2,3]:
        rs=group(f"cert-n{n}-single-")
        survives=all(r["query"]["service_output"]=="OK" for r in rs)
        candidate_results[str(n)]={"repetitions":len(rs),"survives_single_fault":survives}
        if survives and first_good is None:
            first_good=n

    summary={
        "kind":"LOCAL_CONSTRUCTED_DIGITAL_PROCESS_PILOT_NOT_EXTERNAL_REAL_WORLD_VALIDATION",
        "label":args.label,
        "preregistration_commit":PREREGISTRATION_COMMIT,
        "environment":{
            "python":platform.python_version(),
            "system":platform.system(),
            "machine":platform.machine(),
        },
        "registered_repetitions":REPS,
        "record_count":len(records),
        "all_registered_outcomes_match":all(r["matches_expected"] for r in records),
        "candidate_single_fault":candidate_results,
        "first_good_nested_candidate_size":first_good,
        "heldout_replacement_all_pass":all(r["matches_expected"] for r in group("holdout-replace-")),
        "double_fault_negative_all_pass":all(r["matches_expected"] for r in group("neg-double-")),
        "single_worker_baseline_all_pass":all(r["matches_expected"] for r in group("baseline-single-")),
        "claim_verdicts":{
            "C7-LOCAL-FORM-01":"SUPPORTED_LOCAL" if first_good==3 else "REJECTED_LOCAL",
            "C7-LOCAL-FBT-01":"SUPPORTED_LOCAL" if all(r["matches_expected"] for r in group("holdout-replace-")) else "REJECTED_LOCAL",
            "C7-LOCAL-NEG-01":"SUPPORTED_LOCAL" if all(r["matches_expected"] for r in group("neg-double-")) else "REJECTED_LOCAL",
        },
        "logical_signature":logical_signature(records),
        "nonclaims":[
            "not external or natural-system real-world validation",
            "not independent review",
            "not universal carrier minimality",
            "not universal structural identity",
        ]
    }
    summary_path.write_text(json.dumps(summary,indent=2,sort_keys=True)+"\n",encoding="utf-8")
    print(json.dumps({
        "summary":summary,
        "sha256":{
            raw.name:sha256(raw),
            summary_path.name:sha256(summary_path),
            "run_pilot.py":sha256(Path(__file__)),
            "worker.py":sha256(WORKER),
        }
    },indent=2,sort_keys=True))

if __name__ == "__main__":
    main()
