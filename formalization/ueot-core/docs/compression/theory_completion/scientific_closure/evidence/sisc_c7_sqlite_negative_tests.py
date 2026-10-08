#!/usr/bin/env python3
"""Mutations on TEMP COPIES only; frozen preregistered evidence untouched."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import tempfile

from sisc_c7_sqlite_verify import verify


def rewrite(folder, events, manifest):
    raw = folder / "events.jsonl"
    raw.write_text("".join(json.dumps(e, sort_keys=True) + "\n" for e in events), encoding="utf-8")
    manifest["raw_sha256"] = hashlib.sha256(raw.read_bytes()).hexdigest()
    (folder / "manifest.json").write_text(json.dumps(manifest, sort_keys=True) + "\n")


def check(source):
    assert verify(source) == "PASS_METHOD"
    with tempfile.TemporaryDirectory(prefix="sisc-c7-negative-") as scratch:
        parent = Path(scratch)

        tampered = parent / "tampered"
        shutil.copytree(source, tampered)
        raw = tampered / "events.jsonl"
        raw.write_bytes(raw.read_bytes().replace(b"alpha", b"omega", 1))
        assert verify(tampered).startswith("UNRESOLVED:")

        missing = parent / "missing"
        shutil.copytree(source, missing)
        events = [json.loads(s) for s in (missing / "events.jsonl").read_text().splitlines()]
        manifest = json.loads((missing / "manifest.json").read_text())
        rewrite(missing, [e for e in events if e["phase"] != "UPDATE"], manifest)
        assert verify(missing).startswith("UNRESOLVED:")

        contradiction = parent / "contradiction"
        shutil.copytree(source, contradiction)
        events = [json.loads(s) for s in (contradiction / "events.jsonl").read_text().splitlines()]
        manifest = json.loads((contradiction / "manifest.json").read_text())
        clone = events[1]["clone"]
        clone["query"] = "1|different"
        clone["query_sha256"] = hashlib.sha256(clone["query"].encode()).hexdigest()
        events[-1]["claimed_result"] = "REJECTED_METHOD"
        rewrite(contradiction, events, manifest)
        assert verify(contradiction) == "REJECTED_METHOD"

    print("PASS: original, tampered-raw UNRESOLVED, missing-event UNRESOLVED, coherent-contradiction REJECTED_METHOD")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("directory", type=Path)
    check(parser.parse_args().directory)
