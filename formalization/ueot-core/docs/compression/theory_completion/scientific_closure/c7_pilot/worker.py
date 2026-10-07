#!/usr/bin/env python3
import json
import os
import sys

worker_id = sys.argv[1]
for line in sys.stdin:
    line = line.rstrip("\n")
    if not line:
        continue
    parts = line.split(" ", 1)
    cmd = parts[0]
    token = parts[1] if len(parts) == 2 else ""
    if cmd == "PING":
        print(json.dumps({
            "worker_id": worker_id,
            "pid": os.getpid(),
            "token": token,
            "status": "OK"
        }, sort_keys=True), flush=True)
    elif cmd == "STOP":
        print(json.dumps({"worker_id": worker_id, "status": "STOPPING"}, sort_keys=True), flush=True)
        break
    else:
        print(json.dumps({"worker_id": worker_id, "status": "UNKNOWN_COMMAND"}, sort_keys=True), flush=True)
