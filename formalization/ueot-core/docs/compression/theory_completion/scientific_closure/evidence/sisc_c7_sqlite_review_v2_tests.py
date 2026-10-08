#!/usr/bin/env python3
"""Shadow-review mutations operate in memory or disposable folders only."""
import copy
import hashlib
import json
from pathlib import Path
import shutil
import tempfile
import sys

from sisc_c7_sqlite_review_v2 import classify_raw, review_archive
from sisc_c7_sqlite_verify import verify as v1_verify


def check(archive):
    assert review_archive(archive) == "PASS_METHOD"
    events = [json.loads(line) for line in (archive / "events.jsonl").read_text().splitlines()]
    assert classify_raw(events) == "PASS_METHOD"

    mutation = copy.deepcopy(events)
    mutation[3]["moved"]["inode"] += 1
    assert classify_raw(mutation).startswith("UNRESOLVED:")

    mutation = copy.deepcopy(events)
    mutation[3]["clone"]["inode"] += 1
    assert classify_raw(mutation).startswith("UNRESOLVED:")

    mutation = copy.deepcopy(events)
    mutation[2]["time_ns"] = mutation[0]["time_ns"] - 1
    assert classify_raw(mutation).startswith("UNRESOLVED:")

    mutation = copy.deepcopy(events)
    mutation[1]["clone"]["query"] = "1|different"
    mutation[1]["clone"]["query_sha256"] = hashlib.sha256(b"1|different").hexdigest()
    mutation[-1]["claimed_result"] = "REJECTED_METHOD"
    assert classify_raw(mutation) == "REJECTED_METHOD"

    # Internal hashes *alone* cannot detect a coherent fabricated inode map.
    # This is a self-contained counterexample to post-hoc hash-as-authenticity.
    with tempfile.TemporaryDirectory(prefix="sisc-c7-review-v2-") as tmp:
        forged = Path(tmp) / "forged"
        shutil.copytree(archive, forged)
        mutation = copy.deepcopy(events)
        for e in mutation:
            for field in ("original", "clone", "moved"):
                if field in e:
                    e[field]["inode"] += 1000000
        # All equality checks remain true: same-author v1 verifier accepts it.
        raw = "".join(json.dumps(e, sort_keys=True) + "\n" for e in mutation).encode()
        (forged / "events.jsonl").write_bytes(raw)
        manifest = json.loads((forged / "manifest.json").read_text())
        manifest["raw_sha256"] = hashlib.sha256(raw).hexdigest()
        (forged / "manifest.json").write_text(json.dumps(manifest))
        assert v1_verify(forged) == "PASS_METHOD"
        assert review_archive(forged).startswith("UNRESOLVED:")
        assert classify_raw(mutation) == "PASS_METHOD"

    print("PASS: original archive; cross-phase inode/timestamp invalidation; coherent hypothesis failure; self-hash forgery no-go")


if __name__ == "__main__":
    check(Path(sys.argv[1]))
