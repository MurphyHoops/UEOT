#!/usr/bin/env python3
"""Finite SQLite process-fault study. Research code; see repository LICENSE_SCOPE."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import platform
import random
import selectors
import shutil
import signal
import sqlite3
import subprocess
import sys
import time
import traceback
import uuid

POLICIES = ["candidate", "strong_baseline", "weak_structure", "identity_ablation"]
NAMESPACE = uuid.UUID("2e9f8b25-482b-44ad-a8bf-8836b6c097a3")
SCRIPT = Path(__file__).resolve()

def utc():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()

def canonical(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode("utf-8")

def digest(value):
    return hashlib.sha256(canonical(value)).hexdigest()

def file_sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as stream:
        for chunk in iter(lambda: stream.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()

def require(ok, why):
    if not ok:
        raise RuntimeError(why)

def save_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "x", encoding="utf-8") as stream:
        json.dump(value, stream, ensure_ascii=False, indent=2)
        stream.write("\n")

def emit(kind, **fields):
    print(json.dumps(dict(event=kind, pid=os.getpid(), monotonic_ns=time.monotonic_ns(), utc=utc(), **fields), ensure_ascii=False), flush=True)

def environment(connection):
    import _sqlite3
    identities = {}
    for name, filename in [("python", sys.executable), ("_sqlite3", _sqlite3.__file__)]:
        p = Path(filename).resolve()
        identities[name] = {"path": str(p), "sha256": file_sha(p) if p.is_file() else None}
    return {
        "python": sys.version, "platform": platform.platform(),
        "sqlite_version": connection.execute("SELECT sqlite_version()").fetchone()[0],
        "sqlite_source_id": connection.execute("SELECT sqlite_source_id()").fetchone()[0],
        "compile_options": [x[0] for x in connection.execute("PRAGMA compile_options")],
        "binaries": identities,
    }

def configure(connection, execute=None):
    execute = execute or (lambda sql: list(connection.execute(sql)))
    for sql in ["PRAGMA journal_mode=DELETE", "PRAGMA synchronous=FULL",
                "PRAGMA foreign_keys=ON", "PRAGMA cache_size=5",
                "PRAGMA cache_spill=ON", "PRAGMA busy_timeout=1000"]:
        execute(sql)
    names = ["journal_mode", "synchronous", "foreign_keys", "page_size",
             "cache_size", "cache_spill", "locking_mode", "busy_timeout", "fullfsync"]
    return {name: execute("PRAGMA " + name)[0][0] for name in names}

def config_valid(config):
    return config.get("journal_mode") == "delete" and config.get("synchronous") == 2

def make_payload(token, length):
    return (token * ((length + len(token) - 1) // len(token)))[:length]

def initial_state(keys, payload_length):
    return {"business": [[i, 10000 + i, make_payload("initial-%04d|" % i, payload_length)] for i in range(keys)],
            "transactions": []}

def request_for(run_id, seq, state, payload_length):
    txn_id = str(uuid.uuid5(NAMESPACE, run_id + "/txn/" + str(seq)))
    updates = []
    for key, value, _ in state["business"]:
        token = hashlib.sha256((txn_id + ":" + str(key)).encode()).hexdigest()
        updates.append([key, value + ((key + seq) % 7) - 3, token])
    request = {"txn_id": txn_id, "seq": seq, "payload_length": payload_length, "updates": updates}
    request["request_hash"] = digest(request)
    return request

def apply_reference(state, request):
    by_key = {row[0]: row[:] for row in state["business"]}
    for key, value, token in request["updates"]:
        by_key[key] = [key, value, make_payload(token, request["payload_length"])]
    return {"business": [by_key[k] for k in sorted(by_key)],
            "transactions": state["transactions"] + [[request["seq"], request["txn_id"], request["request_hash"]]]}

def read_command():
    raw = sys.stdin.readline()
    require(bool(raw), "controller closed protocol")
    return json.loads(raw)

def worker_main(args):
    setup = json.loads(Path(args.setup).read_text())
    connection = sqlite3.connect(args.db, isolation_level=None, timeout=1.0)
    try:
        config = configure(connection)
        require(config_valid(config), "worker PRAGMA readback mismatch")
        connection.execute("CREATE TABLE business(id INTEGER PRIMARY KEY,value INTEGER NOT NULL,payload TEXT NOT NULL)")
        connection.execute("CREATE TABLE transactions(seq INTEGER PRIMARY KEY,txn_id TEXT NOT NULL UNIQUE,request_hash TEXT NOT NULL)")
        connection.execute("BEGIN IMMEDIATE")
        connection.executemany("INSERT INTO business VALUES(?,?,?)", setup["initial"]["business"])
        connection.execute("COMMIT")
        config = configure(connection)
        emit("READY", config=config, environment=environment(connection))
        while True:
            command = read_command()
            if command["cmd"] == "CLOSE":
                connection.close()
                emit("CLOSED")
                return
            if command["cmd"] == "BACKUP":
                destination = sqlite3.connect(args.backup, isolation_level=None)
                try:
                    connection.backup(destination)
                finally:
                    destination.close()
                emit("BACKUP_COMPLETE", path=args.backup, sha256=file_sha(args.backup))
                continue
            require(command["cmd"] == "TRANSACTION", "unexpected worker command")
            request = command["request"]
            copy_request = dict(request)
            expected_hash = copy_request.pop("request_hash")
            require(digest(copy_request) == expected_hash, "request hash mismatch")
            connection.execute("BEGIN IMMEDIATE")
            bound = [[value, make_payload(token, request["payload_length"]), key]
                     for key, value, token in request["updates"]]
            emit("SQL_BINDING_WITNESS", txn_id=request["txn_id"],
                 sql="UPDATE business SET value=?,payload=? WHERE id=?", row_count=len(bound),
                 bound_parameters_sha256=digest(bound),
                 reconstruction="request updates [key,value,token]; repeat token and truncate to payload_length; bind [value,payload,key]")
            connection.executemany("UPDATE business SET value=?,payload=? WHERE id=?", bound)
            connection.execute("INSERT INTO transactions VALUES(?,?,?)",
                               [request["seq"], request["txn_id"], request["request_hash"]])
            emit("PRECOMMIT_READY", txn_id=request["txn_id"], transaction_active=connection.in_transaction,
                 page_count=connection.execute("PRAGMA page_count").fetchone()[0],
                 cache_size=connection.execute("PRAGMA cache_size").fetchone()[0],
                 cache_spill=connection.execute("PRAGMA cache_spill").fetchone()[0])
            if command.get("pause_precommit"):
                release = read_command()
                require(release == {"cmd": "GO_COMMIT", "txn_id": request["txn_id"]}, "invalid commit release")
            connection.execute("COMMIT")
            emit("COMMIT_RETURNED_NO_ACK", txn_id=request["txn_id"], transaction_active=connection.in_transaction)
            if command.get("pause_preack"):
                release = read_command()
                require(release == {"cmd": "GO_ACK", "txn_id": request["txn_id"]}, "invalid ACK release")
            emit("ACK", txn_id=request["txn_id"], seq=request["seq"])
    finally:
        try:
            connection.close()
        except Exception:
            pass

class Budget:
    def __init__(self, limit):
        self.limit = limit
        self.used = 0
        self.exhausted = False

    def callback(self):
        self.used += 1
        if self.used >= self.limit:
            self.exhausted = True
            return 1
        return 0

def candidate_decision(observation):
    if not observation["complete"]:
        return "UNRESOLVED_" + observation["incomplete_reason"]
    gates = {
        "source": observation["config_valid"],
        "structure": observation["structure_ok"],
        "history": observation["history_membership"],
        "resource": observation["budget_within"],
    }
    if not gates["source"]:
        return "UNRESOLVED_CONFIGURATION"
    if not gates["resource"]:
        return "UNRESOLVED_BUDGET"
    if not gates["structure"]:
        return "REJECT_STRUCTURE"
    if not gates["history"]:
        return "REJECT_HISTORY"
    return "ACCEPT_CURRENT_ALLOWED"

def strong_decision(observation):
    # Independent spelling of exactly the same finite reference-model rule.
    if observation["complete"] is False:
        return "UNRESOLVED_" + observation["incomplete_reason"]
    if observation["config_valid"] is False:
        return "UNRESOLVED_CONFIGURATION"
    if observation["budget_within"] is False:
        return "UNRESOLVED_BUDGET"
    if observation["structure_ok"] is False:
        return "REJECT_STRUCTURE"
    if observation["history_membership"] is not True:
        return "REJECT_HISTORY"
    return "ACCEPT_CURRENT_ALLOWED"

def observer_main(args):
    visible = json.loads(Path(args.input).read_text())
    started_ns = time.monotonic_ns()
    meter = Budget(visible["callback_budget"])
    result = {
        "policy": args.policy, "pid": os.getpid(), "started_utc": utc(),
        "ack_class": visible["ack_class"], "completion_certificate": visible["completion_certificate"],
        "callback_budget": meter.limit, "callback_interval": 1,
        "oracle_summary_input_bytes": Path(args.input).stat().st_size,
        "complete": False, "incomplete_reason": "NOT_STARTED", "sql_observations": [],
        "config_valid": False, "structure_ok": False, "history_membership": None,
        "business": None, "transactions": None, "actual_state_sha256": None,
        "rows_returned": 0, "canonical_returned_bytes": 0, "connect_attempted": False,
        "resource_scope": "observed SQLite progress callbacks, not total VM, disk, kernel or recovery work",
    }
    connection = None
    try:
        if meter.limit <= 0:
            result["incomplete_reason"] = "BUDGET"
        else:
            result["connect_attempted"] = True
            before_connect = time.monotonic_ns()
            connection = sqlite3.connect("file:" + str(Path(args.db).resolve()) + "?mode=rw",
                                         uri=True, isolation_level=None, timeout=1.0)
            result["connect_elapsed_ns"] = time.monotonic_ns() - before_connect
            connection.set_progress_handler(meter.callback, 1)
            def query(sql):
                require(not meter.exhausted, "query after budget exhaustion")
                entry = {"sql": sql, "callbacks_before": meter.used, "started_ns": time.monotonic_ns(), "rows": []}
                result["sql_observations"].append(entry)
                try:
                    cursor = connection.execute(sql)
                    while True:
                        row = cursor.fetchone()
                        if row is None:
                            break
                        row = list(row)
                        entry["rows"].append(row)
                        result["rows_returned"] += 1
                        result["canonical_returned_bytes"] += len(canonical(row))
                    return entry["rows"]
                finally:
                    entry["callbacks_after"] = meter.used
                    entry["elapsed_ns"] = time.monotonic_ns() - entry["started_ns"]
            result["config"] = configure(connection, query)
            result["config_valid"] = config_valid(result["config"])
            result["integrity_rows"] = query("PRAGMA integrity_check")
            result["foreign_key_rows"] = query("PRAGMA foreign_key_check")
            result["structure_ok"] = result["integrity_rows"] == [["ok"]] and result["foreign_key_rows"] == []
            if args.policy != "weak_structure":
                result["business"] = query("SELECT id,value,payload FROM business ORDER BY id")
                result["transactions"] = query("SELECT seq,txn_id,request_hash FROM transactions ORDER BY seq")
                state = {"business": result["business"], "transactions": result["transactions"]}
                result["actual_state_sha256"] = digest(state)
                result["history_membership"] = result["actual_state_sha256"] in visible["allowed_state_sha256"]
                result["internal_invariants"] = (
                    len(result["business"]) == visible["key_count"]
                    and [r[0] for r in result["business"]] == list(range(visible["key_count"]))
                    and all(isinstance(r[1], int) and r[1] > 0 for r in result["business"])
                    and [r[0] for r in result["transactions"]] == list(range(1, len(result["transactions"]) + 1))
                    and len({r[1] for r in result["transactions"]}) == len(result["transactions"])
                )
            result["complete"] = True
            result["incomplete_reason"] = None
    except Exception as exc:
        result["exception"] = {"type": type(exc).__name__, "message": str(exc),
                               "sqlite_errorcode": getattr(exc, "sqlite_errorcode", None),
                               "sqlite_errorname": getattr(exc, "sqlite_errorname", None)}
        result["incomplete_reason"] = "BUDGET" if meter.exhausted else "SQL_OR_OBSERVATION_ERROR"
    finally:
        if connection is not None:
            connection.set_progress_handler(None, 0)
            connection.close()
        result["callback_count"] = meter.used
        result["budget_exhausted"] = meter.exhausted
        result["budget_within"] = meter.used <= max(meter.limit, 0)
        result["elapsed_from_before_connect_ns"] = time.monotonic_ns() - started_ns
        result["finished_utc"] = utc()
    if args.policy == "candidate":
        result["decision"] = candidate_decision(result)
    elif args.policy == "strong_baseline":
        result["decision"] = strong_decision(result)
    elif args.policy == "weak_structure":
        if not result["complete"]:
            result["decision"] = "UNRESOLVED_" + result["incomplete_reason"]
        elif not result["config_valid"]:
            result["decision"] = "UNRESOLVED_CONFIGURATION"
        else:
            result["decision"] = "STRUCTURE_OK" if result["structure_ok"] else "REJECT_STRUCTURE"
    elif args.policy == "identity_ablation":
        if not result["complete"]:
            result["decision"] = "UNRESOLVED_" + result["incomplete_reason"]
        elif not result["config_valid"]:
            result["decision"] = "UNRESOLVED_CONFIGURATION"
        elif not result["structure_ok"]:
            result["decision"] = "REJECT_STRUCTURE"
        else:
            result["decision"] = "ACCEPT_ABLATED" if result["internal_invariants"] else "REJECT_INTERNAL"
    else:
        raise RuntimeError("unknown policy")
    save_json(args.output, result)
    emit("OBSERVER_COMPLETE", policy=args.policy, decision=result["decision"], callback_count=meter.used)

class ParentLog:
    def __init__(self, path):
        self.stream = open(path, "x", encoding="utf-8")
        self.events = []

    def append(self, event, **fields):
        value = dict(event=event, utc=utc(), monotonic_ns=time.monotonic_ns(), **fields)
        self.events.append(value)
        self.stream.write(json.dumps(value, ensure_ascii=False, sort_keys=True) + "\n")
        self.stream.flush()
        os.fsync(self.stream.fileno())
        return value

    def close(self):
        self.stream.close()

class WorkerChannel:
    def __init__(self, process, log, raw):
        self.process, self.log, self.raw = process, log, raw
        self.selector = selectors.DefaultSelector()
        self.selector.register(process.stdout, selectors.EVENT_READ)
        self.buffer = b""
        self.queue = []
        self.acks = {}
        self.eof = False

    def send(self, message):
        self.process.stdin.write(canonical(message) + b"\n")
        self.process.stdin.flush()
        self.log.append("PARENT_SENT", message=message)

    def pump(self, timeout):
        if self.eof:
            return
        for key, _ in self.selector.select(timeout):
            chunk = os.read(key.fileobj.fileno(), 65536)
            if not chunk:
                self.eof = True
                self.selector.unregister(key.fileobj)
                return
            self.raw.write(chunk)
            self.raw.flush()
            self.buffer += chunk
            while b"\n" in self.buffer:
                line, self.buffer = self.buffer.split(b"\n", 1)
                value = json.loads(line.decode("utf-8"))
                self.queue.append(value)
                event = self.log.append("CHILD_MESSAGE_RECEIVED", message=value)
                if value.get("event") == "ACK":
                    self.acks[value["txn_id"]] = event

    def wait(self, event, txn_id=None, seconds=15):
        deadline = time.monotonic() + seconds
        while True:
            for i, item in enumerate(self.queue):
                if item.get("event") == event and (txn_id is None or item.get("txn_id") == txn_id):
                    return self.queue.pop(i)
            if self.eof:
                raise RuntimeError("worker EOF waiting for " + event)
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise TimeoutError("worker timeout waiting for " + event)
            self.pump(min(0.2, remaining))

    def drain(self):
        deadline = time.monotonic() + 2
        while not self.eof and time.monotonic() < deadline:
            self.pump(0.05)
        require(not self.buffer, "partial worker JSON message at EOF")

def file_set(directory):
    result = []
    for path in sorted(Path(directory).iterdir()):
        require(path.is_file() and not path.is_symlink(), "unexpected snapshot entry: " + str(path))
        raw_header = b""
        if path.name.endswith("-journal"):
            with open(path, "rb") as stream:
                raw_header = stream.read(28)
        result.append({
            "name": path.name, "bytes": path.stat().st_size, "sha256": file_sha(path),
            "journal_header_28_hex": raw_header.hex() if raw_header else None,
            "journal_hot_header_candidate": bool(path.name.endswith("-journal") and path.stat().st_size > 512
                                                and raw_header[:8] == bytes.fromhex("d9d505f920a163d7")),
        })
    return result

def clone_files(source, destination):
    destination.mkdir(parents=True, exist_ok=False)
    before = file_set(source)
    copied = 0
    for item in before:
        shutil.copyfile(source / item["name"], destination / item["name"])
        copied += item["bytes"]
    after = file_set(destination)
    require(before == after, "clone does not match original complete file set")
    return {"source_files": before, "clone_files_before_open": after,
            "application_copy_read_bytes": copied, "application_copy_write_bytes": copied}

def terminate_worker(process, channel, log, reason):
    require(process.poll() is None, "worker already exited before requested SIGKILL")
    process.kill()
    log.append("SIGKILL_SENT", pid=process.pid, reason=reason)
    code = process.wait(timeout=15)
    log.append("WORKER_REAPED", pid=process.pid, returncode=code)
    channel.drain()
    require(code == -signal.SIGKILL, "SIGKILL exit code not observed")

def execute_observer(db_dir, visible, policy, output_dir, timeout):
    output_dir.mkdir(parents=True, exist_ok=False)
    input_path, result_path = output_dir / "input.json", output_dir / "result.json"
    save_json(input_path, visible)
    args = [sys.executable, str(SCRIPT), "observer", "--db", str(db_dir / "db.sqlite"),
            "--input", str(input_path), "--policy", policy, "--output", str(result_path)]
    started = utc()
    with open(output_dir / "stdout.log", "xb") as stdout, open(output_dir / "stderr.log", "xb") as stderr:
        try:
            result = subprocess.run(args, stdout=stdout, stderr=stderr, timeout=timeout, check=False)
            code = result.returncode
            timeout_hit = False
        except subprocess.TimeoutExpired:
            code, timeout_hit = None, True
    receipt = {"argv": args, "started_utc": started, "finished_utc": utc(),
               "returncode": code, "timeout": timeout_hit}
    save_json(output_dir / "process.json", receipt)
    if code != 0 or not result_path.exists():
        return {"decision": "UNRESOLVED_EXECUTION", "complete": False, "process": receipt}
    return json.loads(result_path.read_text())

def run_trial(root, spec, protocol):
    case = root / spec["run_id"]
    case.mkdir(parents=True, exist_ok=False)
    oracle_dir, target = case / "oracle", case / "target"
    oracle_dir.mkdir()
    target.mkdir()
    backup = case / "old-backup.sqlite"
    workload = protocol["workloads"][spec["workload"]]
    state = initial_state(workload["keys"], workload["payload_bytes"])
    save_json(oracle_dir / "initial.json", state)
    save_json(oracle_dir / "trial_spec.json", spec)
    setup = case / "worker-setup.json"
    save_json(setup, {"initial": state})
    log = ParentLog(case / "parent-events.jsonl")
    trial = {"spec": spec, "status": "STARTED", "started_utc": utc(), "policies": {}}
    process = channel = raw_stdout = stderr = None
    requests = []
    try:
        stderr = open(case / "worker.stderr.log", "xb")
        raw_stdout = open(case / "worker.stdout.raw", "xb")
        args = [sys.executable, str(SCRIPT), "worker", "--db", str(target / "db.sqlite"),
                "--backup", str(backup), "--setup", str(setup)]
        process = subprocess.Popen(args, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=stderr, bufsize=0)
        trial["worker_pid"] = process.pid
        log.append("WORKER_STARTED", argv=args, pid=process.pid)
        channel = WorkerChannel(process, log, raw_stdout)
        ready = channel.wait("READY", seconds=protocol["timeouts"]["worker_seconds"])
        trial["worker_environment"] = ready["environment"]
        trial["worker_config"] = ready["config"]
        expected_environment = protocol.get("expected_environment", {})
        for field in ["sqlite_version", "sqlite_source_id"]:
            if field in expected_environment:
                require(ready["environment"][field] == expected_environment[field], "runtime environment mismatch: " + field)
        if "compile_options_sha256" in expected_environment:
            require(digest(ready["environment"]["compile_options"]) == expected_environment["compile_options_sha256"],
                    "SQLite compile options differ from registered environment")
        for binary in ["python", "_sqlite3"]:
            key = binary + "_binary_sha256"
            if key in expected_environment:
                require(ready["environment"]["binaries"][binary]["sha256"] == expected_environment[key],
                        "registered binary differs: " + binary)
        for seq in range(1, workload["history_transactions"] + 1):
            request = request_for(spec["run_id"], seq, state, workload["payload_bytes"])
            requests.append(request)
            channel.send({"cmd": "TRANSACTION", "request": request})
            channel.wait("ACK", request["txn_id"], protocol["timeouts"]["worker_seconds"])
            state = apply_reference(state, request)
            if seq == 1:
                channel.send({"cmd": "BACKUP"})
                channel.wait("BACKUP_COMPLETE", seconds=protocol["timeouts"]["worker_seconds"])
        prior_state = state
        request = request_for(spec["run_id"], workload["history_transactions"] + 1, prior_state, workload["payload_bytes"])
        requests.append(request)
        after_state = apply_reference(prior_state, request)
        scenario = spec["scenario"]
        channel.send({"cmd": "TRANSACTION", "request": request,
                      "pause_precommit": scenario == "PRECOMMIT_KILL",
                      "pause_preack": scenario == "COMMIT_NO_ACK_KILL"})
        precommit_witness = False
        if scenario == "PRECOMMIT_KILL":
            channel.wait("PRECOMMIT_READY", request["txn_id"], protocol["timeouts"]["worker_seconds"])
            precommit_witness = True
            terminate_worker(process, channel, log, scenario)
        elif scenario == "COMMIT_NO_ACK_KILL":
            channel.wait("COMMIT_RETURNED_NO_ACK", request["txn_id"], protocol["timeouts"]["worker_seconds"])
            terminate_worker(process, channel, log, scenario)
        else:
            channel.wait("ACK", request["txn_id"], protocol["timeouts"]["worker_seconds"])
            if scenario == "POST_ACK_KILL":
                terminate_worker(process, channel, log, scenario)
            else:
                channel.send({"cmd": "CLOSE"})
                channel.wait("CLOSED", seconds=protocol["timeouts"]["worker_seconds"])
                trial["worker_returncode"] = process.wait(timeout=15)
                channel.drain()
                require(trial["worker_returncode"] == 0, "normal worker did not exit successfully")
        trial["worker_returncode"] = process.returncode
        log.append("TARGET_PROCESS_STOPPED", pid=process.pid, returncode=process.returncode)
        if request["txn_id"] in channel.acks:
            ack_class, states = "ACKED", [after_state]
            certificate = {"kind": "ACK_RECEIVED", "txn_id": request["txn_id"],
                           "parent_receive_monotonic_ns": channel.acks[request["txn_id"]]["monotonic_ns"]}
        elif precommit_witness:
            ack_class, states = "NOT_COMMITTED", [prior_state]
            certificate = {"kind": "PRECOMMIT_GATE_WITHHELD", "txn_id": request["txn_id"],
                           "ready_received": True, "go_commit_sent": False,
                           "worker_reaped_returncode": process.returncode}
        else:
            ack_class, states = "UNKNOWN", [prior_state, after_state]
            certificate = {"kind": "REQUEST_WITHOUT_ACK", "txn_id": request["txn_id"]}
        save_json(oracle_dir / "requests.json", requests)
        save_json(oracle_dir / "ack_events.json", list(channel.acks.values()))
        save_json(oracle_dir / "allowed_states.json", states)
        trial["ack_class"], trial["completion_certificate"] = ack_class, certificate
        trial["before_intervention_files"] = file_set(target)
        if scenario == "STALE_BACKUP":
            require(all(x["name"] == "db.sqlite" for x in file_set(target)), "stale replacement requires closed clean DB with no sidecars")
            current_snapshot = case / "pre_replacement_current"
            trial["pre_replacement_current_copy"] = clone_files(target, current_snapshot)
            save_json(case / "pre-replacement-current-files.json", file_set(current_snapshot))
            before_hash = file_sha(target / "db.sqlite")
            size = backup.stat().st_size
            shutil.copyfile(backup, target / "db.sqlite")
            log.append("OLD_BACKUP_REPLACED", source_sha256=file_sha(backup), old_target_sha256=before_hash,
                       new_target_sha256=file_sha(target / "db.sqlite"), application_read_bytes=size,
                       application_write_bytes=size)
        raw = case / "postfault_raw"
        trial["snapshot_copy"] = clone_files(target, raw)
        original_manifest = file_set(raw)
        trial["postfault_files"] = original_manifest
        save_json(case / "postfault-files.json", original_manifest)
        budget = protocol["budgets"]["high"]
        if scenario == "BUDGET_ZERO":
            budget = protocol["budgets"]["zero"]
        elif scenario == "BUDGET_SMALL":
            budget = protocol["budgets"]["small"]
        visible = {
            "allowed_state_sha256": [digest(s) for s in states],
            "ack_class": ack_class, "completion_certificate": certificate,
            "key_count": workload["keys"], "callback_budget": budget,
            "summary_scope": "derived only from caller requests/received ACK or shared withheld-commit protocol certificate",
            "digest_assumption": "SHA256 canonical finite state; raw rows and full oracle states retained for exact independent comparison",
        }
        policies = POLICIES[spec["policy_rotation"]:] + POLICIES[:spec["policy_rotation"]]
        for policy in policies:
            policy_dir = case / "policy" / policy
            clone_dir = policy_dir / "database"
            copy_record = clone_files(raw, clone_dir)
            result = execute_observer(clone_dir, visible, policy, policy_dir / "execution",
                                      protocol["timeouts"]["observer_seconds"])
            trial["policies"][policy] = {
                "decision": result["decision"], "complete": result["complete"],
                "history_membership": result.get("history_membership"),
                "callback_count": result.get("callback_count"),
                "budget_exhausted": result.get("budget_exhausted"),
                "budget_within": result.get("budget_within"),
                "config_valid": result.get("config_valid"),
                "result_relative_path": str((policy_dir / "execution" / "result.json").relative_to(case)),
                "copy": copy_record, "files_after": file_set(clone_dir),
            }
            require(file_set(raw) == original_manifest, "postfault original mutated during policy")
        # A separate last clone, unlimited for this finite workload, is retained
        # for independent adjudication. Its raw result is not fed back to policies.
        judge_dir = case / "adjudication"
        judge_copy = clone_files(raw, judge_dir / "database")
        judge_input = dict(visible, callback_budget=protocol["budgets"]["adjudication"])
        judge = execute_observer(judge_dir / "database", judge_input, "strong_baseline",
                                 judge_dir / "execution", protocol["timeouts"]["observer_seconds"])
        trial["adjudication"] = {"copy": judge_copy, "complete": judge["complete"],
                                 "decision": judge["decision"], "history_membership": judge.get("history_membership"),
                                 "files_after": file_set(judge_dir / "database")}
        trial["original_unchanged"] = file_set(raw) == original_manifest
        require(trial["original_unchanged"], "original snapshot changed")
        trial["candidate_baseline_same_decision"] = trial["policies"]["candidate"]["decision"] == trial["policies"]["strong_baseline"]["decision"]
        trial["status"] = "COMPLETE"
    except Exception as exc:
        trial["status"] = "EXECUTION_ERROR"
        trial["exception"] = {"type": type(exc).__name__, "message": str(exc), "traceback": traceback.format_exc()}
        log.append("EXECUTION_ERROR", detail=trial["exception"])
    finally:
        if process is not None and process.poll() is None:
            process.kill()
            process.wait(timeout=15)
            log.append("CLEANUP_SIGKILL", pid=process.pid, returncode=process.returncode)
        if raw_stdout is not None:
            raw_stdout.close()
        if stderr is not None:
            stderr.close()
        trial["finished_utc"] = utc()
        log.append("TRIAL_TERMINAL", status=trial["status"])
        log.close()
        save_json(case / "trial-result.json", trial)
    return trial

def authorization_check(args, protocol_sha, script_sha):
    if args.split == "calibration":
        require(args.authorization is None, "calibration cannot consume certification authorization")
        return None
    require(args.authorization is not None, "certification/replication requires frozen preregistration authorization")
    auth = json.loads(Path(args.authorization).read_text())
    require(auth.get("approved") is True, "authorization is not approved")
    commit = auth.get("preregistration_commit", "")
    require(len(commit) == 40 and all(c in "0123456789abcdef" for c in commit), "invalid preregistration commit")
    require(auth.get("runner_sha256") == script_sha, "runner differs from authorized preregistration")
    require(auth.get("protocol_sha256") == protocol_sha, "protocol differs from authorized preregistration")
    require(args.split in auth.get("allowed_splits", []), "phase is not authorized")
    return auth

def run_main(args):
    protocol_path = Path(args.protocol).resolve()
    protocol = json.loads(protocol_path.read_text())
    script_sha, protocol_sha = file_sha(SCRIPT), file_sha(protocol_path)
    if args.split != "calibration":
        require(protocol.get("status") == "FROZEN_BEFORE_CERTIFICATION", "protocol is not frozen")
    auth = authorization_check(args, protocol_sha, script_sha)
    root = Path(args.out).resolve()
    root.mkdir(parents=True, exist_ok=False)
    allocation = protocol["allocations"][args.split]
    specs = []
    for workload in allocation["workloads"]:
        for scenario in allocation.get("scenarios", protocol["scenarios"]):
            require(scenario in protocol["scenarios"], "unregistered allocation scenario")
            for repetition in range(allocation["repetitions"]):
                label = protocol["study_id"] + "/" + protocol.get("protocol_revision", "1") + "/" + args.split + "/" + workload + "/" + scenario + "/" + str(repetition)
                specs.append({"run_id": str(uuid.uuid5(NAMESPACE, label)), "split": args.split,
                              "workload": workload, "scenario": scenario, "repetition": repetition})
    random.Random(allocation["order_seed"]).shuffle(specs)
    for index, spec in enumerate(specs):
        spec["order"] = index
        spec["policy_rotation"] = index % len(POLICIES)
    save_json(root / "RUNS_PLANNED.json", specs)
    save_json(root / "RUN_MANIFEST.json", {
        "study_id": protocol["study_id"], "split": args.split, "started_utc": utc(),
        "runner_sha256": script_sha, "protocol_sha256": protocol_sha,
        "authorization": auth, "runner_path": str(SCRIPT), "protocol": protocol,
        "planned_count": len(specs), "execution_environment": {"python": sys.version, "platform": platform.platform()},
    })
    results = []
    allocation_started = time.monotonic()
    start_budget_seconds = protocol["timeouts"]["stop_starting_trials_after_seconds"]
    for spec in specs:
        if time.monotonic() - allocation_started >= start_budget_seconds:
            case = root / spec["run_id"]
            case.mkdir(parents=True, exist_ok=False)
            result = {"spec": spec, "status": "NOT_RUN", "policies": {}, "recorded_utc": utc(),
                      "reason": "TOTAL_RUN_START_BUDGET_EXHAUSTED"}
            save_json(case / "trial-result.json", result)
        else:
            result = run_trial(root, spec, protocol)
        results.append(result)
        print(json.dumps({"run_id": spec["run_id"], "status": result["status"], "scenario": spec["scenario"],
                          "decisions": {k: v["decision"] for k, v in result["policies"].items()}}), flush=True)
    summary = {
        "study_id": protocol["study_id"], "split": args.split, "finished_utc": utc(),
        "attempted": sum(x["status"] != "NOT_RUN" for x in results), "planned": len(specs),
        "complete": sum(x["status"] == "COMPLETE" for x in results),
        "execution_errors": sum(x["status"] == "EXECUTION_ERROR" for x in results),
        "not_run": sum(x["status"] == "NOT_RUN" for x in results),
        "stop_starting_trials_after_seconds": start_budget_seconds,
        "deadline_scope": "checked before each trial; not a hard wall-clock limit on current trial, teardown or OS I/O",
        "candidate_baseline_disagreements": [x["spec"]["run_id"] for x in results if x.get("candidate_baseline_same_decision") is False],
        "results": [{"spec": x["spec"], "status": x["status"], "ack_class": x.get("ack_class"),
                     "policies": x["policies"], "postfault_files": x.get("postfault_files"),
                     "adjudication": x.get("adjudication"), "exception": x.get("exception")} for x in results],
    }
    save_json(root / "SUMMARY.json", summary)
    manifest = []
    for path in sorted(root.rglob("*")):
        if path.is_file():
            manifest.append({"path": str(path.relative_to(root)), "bytes": path.stat().st_size, "sha256": file_sha(path)})
    save_json(root / "FILE_MANIFEST.json", manifest)
    print(json.dumps({"terminal": "RUN_FINISHED", "attempted": summary["attempted"], "not_run": summary["not_run"],
                      "execution_errors": summary["execution_errors"]}), flush=True)
    return 0 if summary["complete"] == summary["planned"] else 2

def main():
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)
    run = sub.add_parser("run")
    run.add_argument("--split", choices=["calibration", "certification", "replication"], required=True)
    run.add_argument("--protocol", required=True)
    run.add_argument("--out", required=True)
    run.add_argument("--authorization")
    worker = sub.add_parser("worker")
    worker.add_argument("--db", required=True)
    worker.add_argument("--backup", required=True)
    worker.add_argument("--setup", required=True)
    observer = sub.add_parser("observer")
    observer.add_argument("--db", required=True)
    observer.add_argument("--input", required=True)
    observer.add_argument("--policy", choices=POLICIES, required=True)
    observer.add_argument("--output", required=True)
    args = parser.parse_args()
    if args.command == "run":
        return run_main(args)
    if args.command == "worker":
        worker_main(args)
    else:
        observer_main(args)
    return 0

if __name__ == "__main__":
    sys.exit(main())

