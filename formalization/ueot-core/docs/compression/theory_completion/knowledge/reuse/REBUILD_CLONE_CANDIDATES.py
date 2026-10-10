#!/usr/bin/env python3
"""Reproduce the 68 cross-module source snippets from 633 pinned Lean files.

Read-only: compares a freshly computed 8-line window scan to the immutable
CLONE_CANDIDATES_68.json and raises on drift. Does not overwrite evidence.
"""
from collections import defaultdict
import itertools
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import fkrg_reuse as reuse

sys.path.insert(0, str(HERE.parent))
from fkrg import no_lean_comments


def scan():
    data = reuse.load()
    source_lines = {}
    for item in data["modules"]:
        path = item["path"]
        stripped = no_lean_comments((reuse.REPO / path).read_text())
        source_lines[path] = [
            (line_number + 1, re.sub(r"\s+", " ", line.strip()))
            for line_number, line in enumerate(stripped.splitlines())
            if line.strip()
        ]
    windows = defaultdict(list)
    for path, lines in source_lines.items():
        for i in range(len(lines) - 7):
            windows[tuple(text for _, text in lines[i:i+8])].append((path, i))
    groups = [(words, locations) for words, locations in windows.items()
              if len({path for path, _ in locations}) > 1]
    expansions = {}
    for _, locations in groups:
        for (a, ia), (b, ib) in itertools.combinations(locations, 2):
            if a == b:
                continue
            lines_a, lines_b = source_lines[a], source_lines[b]
            if ia and ib and lines_a[ia-1][1] == lines_b[ib-1][1]:
                continue
            end = 8
            while ia+end < len(lines_a) and ib+end < len(lines_b) and (
                lines_a[ia+end][1] == lines_b[ib+end][1]
            ):
                end += 1
            if end >= 8:
                expansions[a,b,ia,ib] = end
    result = []
    for (a,b,ia,ib),length in expansions.items():
        la, lb = source_lines[a], source_lines[b]
        if not any(any(t in line for t in ("theorem ", "lemma ", "def ", "simp", "exact", "rw "))
                   for _, line in la[ia:ia+length]):
            continue
        result.append({
            "file_a": a, "file_b": b,
            "start_line_a": la[ia][0], "start_line_b": lb[ib][0],
            "end_line_a": la[ia+length-1][0],
            "end_line_b": lb[ib+length-1][0],
            "equal_nonblank_code_lines": length,
            "excerpt": "\n".join(text for _,text in la[ia:min(ia+12,ia+length)])
        })
    result.sort(key=lambda x: -x["equal_nonblank_code_lines"])
    return result


if __name__ == "__main__":
    fresh = scan()
    pinned = json.loads((HERE / "CLONE_CANDIDATES_68.json").read_text())
    if fresh != pinned:
        raise RuntimeError(f"CLONE_REGEN_MISMATCH: freshly {len(fresh)}, archived {len(pinned)}")
    print(json.dumps({
        "status": "PASS", "cross_file_proof_related_code_clone_pairs": len(fresh),
        "length_15_plus": sum(x["equal_nonblank_code_lines"] >= 15 for x in fresh),
        "max_code_lines": max(x["equal_nonblank_code_lines"] for x in fresh),
        "kind": "exact normalized source snippet matching, NOT logical theorem equivalence"
    }, indent=2))
