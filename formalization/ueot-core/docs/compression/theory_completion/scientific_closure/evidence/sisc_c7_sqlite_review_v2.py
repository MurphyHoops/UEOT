#!/usr/bin/env python3
"""Post-collection *shadow* consistency review of the frozen SQLite v1 pilot.

This verifier is written AFTER the original pilot. It cannot independently
attest to real-world collection, authenticity of the writer's timestamps,
uncensored attempts, or observations not stored in the raw file. It never
modifies archive data. Its pinned archive SHA verifies only the exact v1 bytes.
"""
import hashlib
import json
from pathlib import Path
import re
import sys


RUN = "SISC_SQLITE_METHOD_20261008_V1"
EXPECTED_PHASES = ("INITIAL", "COPY", "RENAME", "UPDATE", "COMPLETE")
ARCHIVED_SHA256 = "7484c8212c5aba6ad076d4359aa6c467ea3063f339400405211a5739052ff9d5"
REQUIRED_CARRIERS = ("original.db", "clone.db", "moved.db")


def observation_consistent(state, expected_name):
    if not isinstance(state, dict) or set(state) != {
        "carrier", "device", "inode", "query", "query_sha256"
    }:
        return False
    return (
        state["carrier"] == expected_name
        and type(state["device"]) is int and state["device"] >= 0
        and type(state["inode"]) is int and state["inode"] > 0
        and isinstance(state["query"], str)
        and re.fullmatch(r"[0-9a-f]{64}", state["query_sha256"]) is not None
        and hashlib.sha256(state["query"].encode()).hexdigest() == state["query_sha256"]
    )


def classify_raw(events):
    """Classify internal consistency only; DOES NOT authenticate the collector."""
    if not isinstance(events, list) or len(events) != 5:
        return "UNRESOLVED: cardinality"
    if any(not isinstance(e, dict) for e in events):
        return "UNRESOLVED: invalid event"
    if [e.get("phase") for e in events] != list(EXPECTED_PHASES):
        return "UNRESOLVED: phases"
    if [e.get("seq") for e in events] != list(range(5)) or any(
        type(e.get("seq")) is not int for e in events
    ):
        return "UNRESOLVED: sequence"
    if any(e.get("run") != RUN or type(e.get("time_ns")) is not int or
           e["time_ns"] <= 0 for e in events):
        return "UNRESOLVED: missing provenance field"
    if any(events[i]["time_ns"] > events[i + 1]["time_ns"] for i in range(4)):
        return "UNRESOLVED: nonmonotone timestamps"
    a0, copied, renamed, updated, terminal = events
    if not isinstance(a0.get("sqlite_version"), str) or not a0["sqlite_version"]:
        return "UNRESOLVED: missing engine version"
    needed = (
        (a0.get("original"), "original.db"),
        (copied.get("original"), "original.db"),
        (copied.get("clone"), "clone.db"),
        (renamed.get("original"), "original.db"),
        (renamed.get("moved"), "moved.db"),
        (updated.get("moved"), "moved.db"),
        (updated.get("clone"), "clone.db"),
    )
    if any(not observation_consistent(s, n) for s, n in needed):
        return "UNRESOLVED: malformed carrier, query, digest, or inode"
    a, a_copy, clone, a_rename, moved, after, clone_after = (s for s, _ in needed)
    if a != a_copy or a != a_rename:
        return "UNRESOLVED: contradictory source snapshot"
    if (moved["device"], moved["inode"]) != (after["device"], after["inode"]):
        return "UNRESOLVED: update carrier unexpectedly replaced"
    if (clone["device"], clone["inode"]) != (clone_after["device"], clone_after["inode"]):
        return "UNRESOLVED: clone carrier unexpectedly replaced"

    supported = (
        a["query"] == "1|alpha"
        and clone["query"] == a["query"]
        and (a["device"], a["inode"]) != (clone["device"], clone["inode"])
        and moved["query"] == a["query"]
        and (moved["device"], moved["inode"]) == (a["device"], a["inode"])
        and after["query"] == "1|beta"
        and clone_after["query"] == "1|alpha"
    )
    result = "PASS_METHOD" if supported else "REJECTED_METHOD"
    if terminal.get("claimed_result") != result:
        return "UNRESOLVED: producer-claim discrepancy"
    return result


def review_archive(directory):
    try:
        raw = (directory / "events.jsonl").read_bytes()
        manifest = json.loads((directory / "manifest.json").read_text())
        digest = hashlib.sha256(raw).hexdigest()
        if digest != ARCHIVED_SHA256:
            return "UNRESOLVED: archive deviates from pinned v1 digest"
        if manifest != {"run": RUN, "raw_sha256": ARCHIVED_SHA256,
                        "registered_phases": list(EXPECTED_PHASES)}:
            return "UNRESOLVED: manifest mismatch"
        events = [json.loads(line) for line in raw.decode("utf-8").splitlines()]
        return classify_raw(events)
    except (OSError, ValueError, UnicodeError, TypeError, KeyError) as exc:
        return f"UNRESOLVED: unreadable archive: {type(exc).__name__}"


if __name__ == "__main__":
    result = review_archive(Path(sys.argv[1]))
    print(result)
    sys.exit(0 if result == "PASS_METHOD" else 2)
