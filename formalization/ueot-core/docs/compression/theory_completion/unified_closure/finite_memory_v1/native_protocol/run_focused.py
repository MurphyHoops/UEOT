#!/usr/bin/env python3
"""Preserve each exact source attempt and run only its requested Lean targets."""
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

payload_path = Path(sys.argv[1])
payload = json.loads(payload_path.read_text())
repo = Path(payload["repo"])
evidence = payload_path.parent
attempt = evidence / payload["attempt"]
attempt.mkdir(exist_ok=False)
lake = Path(payload["lake"])
lean = lake.with_name("lean")
env = os.environ.copy()
env["PATH"] = str(lake.parent) + ":" + env.get("PATH", "")
state = {
    "attempt": payload["attempt"],
    "state": "RUNNING",
    "started": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "lean_version": subprocess.check_output([str(lean), "--version"], text=True),
    "results": [],
}


def save():
    (attempt / "STATUS.json").write_text(json.dumps(state, indent=2) + "\n")


save()
for source in payload["files"]:
    data = source["content"].encode()
    assert hashlib.sha256(data).hexdigest() == source["sha256"]
    target = repo / source["path"]
    assert target.is_relative_to(repo / "formalization/ueot-core/UEOT")
    target.write_bytes(data)
    snapshot = attempt / "source" / source["path"]
    snapshot.parent.mkdir(parents=True, exist_ok=True)
    snapshot.write_bytes(data)
for source in payload["files"]:
    rel = Path(source["path"]).relative_to("formalization/ueot-core")
    if payload.get("targets") and rel.stem not in payload["targets"]:
        continue
    module = str(rel.with_suffix("")).replace("/", ".")
    output = Path(".lake/build/lib/lean") / rel.with_suffix(".olean")
    (repo / "formalization/ueot-core" / output).parent.mkdir(parents=True, exist_ok=True)
    args = [str(lake), "env", "lean", "-o", str(output), str(rel)]
    started = time.monotonic()
    result = subprocess.run(args, cwd=repo / "formalization/ueot-core", env=env,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (attempt / (rel.stem + ".log")).write_bytes(result.stdout)
    row = {"module": module, "source_sha256": source["sha256"],
           "exit_code": result.returncode, "seconds": time.monotonic() - started,
           "log_sha256": hashlib.sha256(result.stdout).hexdigest(), "args": args}
    state["results"].append(row)
    save()
    print(json.dumps(row), flush=True)
    print(result.stdout.decode(errors="replace"), flush=True)
state["state"] = "PASS" if all(row["exit_code"] == 0 for row in state["results"]) else "FAIL"
state["finished"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
save()
print("FINAL_STATE=" + state["state"], flush=True)
