#!/usr/bin/env python3
"""Check the exact delivered evidence; optionally extract into a new directory.

This opens no SQLite database and launches no experimental process. It verifies
archive hashes, manifest hashes, exact member sets, and every payload byte/hash.
"""
import argparse
import datetime
import hashlib
import json
from pathlib import Path, PurePosixPath
import tarfile


def digest(data):
    return hashlib.sha256(data).hexdigest()


def require(ok, message):
    if not ok:
        raise ValueError(message)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--catalog", type=Path, default=Path(__file__).resolve().parents[1] / "raw/RAW_ARCHIVES.json")
    ap.add_argument("--extract-to", type=Path)
    ap.add_argument("--receipt", type=Path)
    args = ap.parse_args()
    catalog = json.loads(args.catalog.read_text())
    study = args.catalog.resolve().parents[1]
    if args.extract_to:
        require(not args.extract_to.exists(), "extraction destination must be new")
    reports = []
    for record in catalog["archives"]:
        archive = study / record["path"]
        data = archive.read_bytes()
        require(len(data) == record["bytes"] and digest(data) == record["sha256"], "archive identity mismatch")
        with tarfile.open(archive, "r:xz") as tar:
            members = tar.getmembers()
            names = [m.name for m in members]
            require(len(names) == len(set(names)), "duplicate archive member")
            for m in members:
                p = PurePosixPath(m.name)
                require(m.isfile() and not p.is_absolute() and ".." not in p.parts,
                        "unsafe or non-file member: " + m.name)
            manifest_raw = tar.extractfile(record["manifest_name"]).read()
            require(digest(manifest_raw) == record["manifest_sha256"], "manifest identity mismatch")
            manifest = json.loads(manifest_raw)
            entries = manifest["files"]
            require(len(entries) == record["payload_files"], "payload count mismatch")
            require(len({e["path"] for e in entries}) == len(entries), "duplicate manifest entry")
            require(set(names) == {e["path"] for e in entries} | {record["manifest_name"]}, "exact file-set mismatch")
            total = 0
            for e in entries:
                raw = tar.extractfile(e["path"]).read()
                require(len(raw) == e["bytes"] and digest(raw) == e["sha256"], "payload mismatch: " + e["path"])
                total += len(raw)
            require(total == record["payload_bytes"], "payload byte count mismatch")
            if args.extract_to:
                destination = args.extract_to / record["label"]
                destination.mkdir(parents=True, exist_ok=False)
                for m in members:
                    p = destination / m.name
                    p.parent.mkdir(parents=True, exist_ok=True)
                    with p.open("xb") as out:
                        out.write(tar.extractfile(m).read())
            reports.append({"label": record["label"], "archive_sha256": record["sha256"],
                            "payload_files": len(entries), "payload_bytes": total, "all_exact": True})
    receipt = {"status": "PASS_DELIVERED_BYTES", "at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
               "catalog_sha256": digest(args.catalog.read_bytes()), "script_sha256": digest(Path(__file__).read_bytes()),
               "archives": reports, "extraction": str(args.extract_to) if args.extract_to else None,
               "scope": "Archive and payload identity only; no SQLite process, query, fault injection, or statistical trial."}
    if args.receipt:
        require(not args.receipt.exists(), "receipt destination must be new")
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps(receipt, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
