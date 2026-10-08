#!/usr/bin/env python3
"""Predeclared SQLite file-clone/rename method pilot (self-administered).

Never touches an existing database: an empty output directory must not exist
before launching, and an isolated temporary directory owns every SQLite file.
Append/fsync each step immediately; retain failure records on exceptions.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time


REGISTERED_RUN = "SISC_SQLITE_METHOD_20261008_V1"
PHASES = ["INITIAL", "COPY", "RENAME", "UPDATE", "COMPLETE"]


def sql(path, stmt):
    cmd = ["/usr/bin/sqlite3", str(path), stmt]
    result = subprocess.run(cmd, check=True, capture_output=True, text=True, timeout=15)
    return result.stdout.strip()


def observe(path):
    st = path.stat()
    query = sql(path, "SELECT id, value FROM items ORDER BY id;")
    return {
        "carrier": path.name,
        "device": st.st_dev,
        "inode": st.st_ino,
        "query": query,
        "query_sha256": hashlib.sha256(query.encode()).hexdigest(),
    }


def run(output_dir):
    output_dir.mkdir(parents=True, exist_ok=False)
    raw = output_dir / "events.jsonl"
    with raw.open("x", encoding="utf-8") as events:
        seq = 0

        def append(phase, **values):
            nonlocal seq
            event = {
                "run": REGISTERED_RUN,
                "seq": seq,
                "phase": phase,
                "time_ns": time.time_ns(),
                **values,
            }
            events.write(json.dumps(event, sort_keys=True) + "\n")
            events.flush()
            os.fsync(events.fileno())
            seq += 1

        try:
            version = subprocess.run(
                ["/usr/bin/sqlite3", "--version"], check=True, capture_output=True,
                text=True, timeout=15,
            ).stdout.strip()
            with tempfile.TemporaryDirectory(prefix="ueot-sisc-sqlite-") as td:
                root = Path(td)
                a, b, c = root / "original.db", root / "clone.db", root / "moved.db"
                sql(a, "CREATE TABLE items(id INTEGER PRIMARY KEY, value TEXT);"
                       " INSERT INTO items(id, value) VALUES(1, 'alpha');")
                s0 = observe(a)
                append("INITIAL", sqlite_version=version, original=s0)

                shutil.copy2(a, b)
                clone = observe(b)
                append("COPY", original=s0, clone=clone)

                a.rename(c)
                moved = observe(c)
                append("RENAME", original=s0, moved=moved)

                sql(c, "UPDATE items SET value='beta' WHERE id=1;")
                updated, clone_after = observe(c), observe(b)
                append("UPDATE", moved=updated, clone=clone_after)

                passed = (
                    s0["query"] == "1|alpha"
                    and clone["query"] == s0["query"]
                    and (clone["device"], clone["inode"]) != (s0["device"], s0["inode"])
                    and moved["query"] == s0["query"]
                    and (moved["device"], moved["inode"]) == (s0["device"], s0["inode"])
                    and updated["query"] == "1|beta"
                    and clone_after["query"] == "1|alpha"
                )
                append("COMPLETE", claimed_result="PASS_METHOD" if passed else "REJECTED_METHOD")
        except Exception as exc:
            append("EXECUTION_ERROR", error_type=type(exc).__name__, error=str(exc))
            raise

    digest = hashlib.sha256(raw.read_bytes()).hexdigest()
    (output_dir / "manifest.json").write_text(
        json.dumps({"run": REGISTERED_RUN, "raw_sha256": digest,
                    "registered_phases": PHASES}, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    if not passed:
        raise RuntimeError("registered SQLite witness failed")
    print(f"RAW={raw}\nSHA256={digest}\nRESULT=PENDING_INDEPENDENT_RAW_RECOMPUTATION")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    run(args.output)
