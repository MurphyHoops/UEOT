#!/usr/bin/env python3
"""Recompute preregistered method verdict *from raw event fields*.

Authored by the same project: this is reproducibility, NOT independent review.
"""
import argparse
import hashlib
import json
from pathlib import Path


PHASES = ["INITIAL", "COPY", "RENAME", "UPDATE", "COMPLETE"]
RUN = "SISC_SQLITE_METHOD_20261008_V1"


def verify(directory):
    raw = directory / "events.jsonl"
    manifest = json.loads((directory / "manifest.json").read_text(encoding="utf-8"))
    if hashlib.sha256(raw.read_bytes()).hexdigest() != manifest["raw_sha256"]:
        return "UNRESOLVED: manifest mismatch"
    try:
        events = [json.loads(s) for s in raw.read_text(encoding="utf-8").splitlines()]
        if (
            len(events) != len(PHASES)
            or [e["phase"] for e in events] != PHASES
            or [e["seq"] for e in events] != list(range(len(PHASES)))
            or any(e["run"] != RUN for e in events)
            or manifest["run"] != RUN
            or manifest["registered_phases"] != PHASES
        ):
            return "UNRESOLVED: missing, duplicated or unregistered event"
        initial, copied, renamed, changed, terminal = events
        a, b, c, changed_a, changed_b = (
            initial["original"], copied["clone"], renamed["moved"],
            changed["moved"], changed["clone"],
        )
        for state in (a, b, c, changed_a, changed_b):
            if hashlib.sha256(state["query"].encode()).hexdigest() != state["query_sha256"]:
                return "UNRESOLVED: inconsistent raw response hash"
        success = (
            a == copied["original"] == renamed["original"]
            and a["query"] == "1|alpha"
            and b["query"] == a["query"]
            and (a["device"], a["inode"]) != (b["device"], b["inode"])
            and c["query"] == a["query"]
            and (c["device"], c["inode"]) == (a["device"], a["inode"])
            and changed_a["query"] == "1|beta"
            and changed_b["query"] == "1|alpha"
        )
        result = "PASS_METHOD" if success else "REJECTED_METHOD"
        if terminal["claimed_result"] != result:
            return "UNRESOLVED: producer/independent-rule mismatch"
        return result
    except (KeyError, IndexError, TypeError, ValueError) as exc:
        return "UNRESOLVED: invalid raw data: " + str(exc)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("directory", type=Path)
    args = parser.parse_args()
    result = verify(args.directory)
    print(result)
    raise SystemExit(0 if result == "PASS_METHOD" else 2)
