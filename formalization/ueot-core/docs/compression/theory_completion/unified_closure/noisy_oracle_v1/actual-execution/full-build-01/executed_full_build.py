#!/usr/bin/env python3
"""Preserve one real full UEOT build with unchanged, pinned proof inputs.

No success record is generated from an old receipt or a source-only scan.
The output directory is new and outside the repository; failures retain the
actual log, exit status, and initial build identity.
"""
from __future__ import annotations

import argparse
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import time

CORE = "formalization/ueot-core/"
IDENTITY_HELPER = CORE + "docs/compression/theory_completion/unified_closure/registered_interfaces/native_protocol/build_identity.py"


def dump(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n")


def run(repo, out, base, lake, lean):
    repo, out = Path(repo).resolve(), Path(out).resolve()
    if out.is_relative_to(repo) or out.exists():
        raise RuntimeError("NEW_OUTPUT_DIRECTORY_OUTSIDE_REPOSITORY_REQUIRED")
    base = subprocess.check_output(
        ["git", "rev-parse", "--verify", base + "^{commit}"], cwd=repo, text=True).strip()
    helper = repo / IDENTITY_HELPER
    baseline = subprocess.check_output(["git", "show", base + ":" + IDENTITY_HELPER], cwd=repo)
    if helper.read_bytes() != baseline:
        raise RuntimeError("IMMUTABLE_BUILD_IDENTITY_HELPER_CHANGED")
    spec = importlib.util.spec_from_file_location("longterm_full_build_identity", helper)
    identity_helper = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = identity_helper
    spec.loader.exec_module(identity_helper)
    identity = identity_helper.capture(repo, lake=lake, lean=lean)
    out.mkdir(parents=True)
    receipt_path = out / "FULL_BUILD_RECEIPT.json"
    receipt = {"schema": "NOISY_ORACLE_ACTUAL_FULL_BUILD_V1", "state": "RUNNING",
               "baseline_ref": base, "identity": identity,
               "driver_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
               "identity_helper_sha256": sha256(baseline).hexdigest()}
    dump(receipt_path, receipt)
    command = [identity["runtime_tools"]["lake"]["executable"], "build", "UEOT"]
    log = out / "full-build.log"
    started = time.monotonic()
    try:
        with log.open("w") as stream:
            process = subprocess.run(command, cwd=repo / CORE, stdout=stream, stderr=subprocess.STDOUT)
        receipt["full_build"] = {"command": command, "exit_code": process.returncode,
                                  "seconds": round(time.monotonic() - started, 3),
                                  "log_name": log.name, "log_sha256": sha256(log.read_bytes()).hexdigest()}
        if process.returncode != 0:
            raise RuntimeError("ACTUAL_FULL_BUILD_FAILED")
        if "Build completed successfully" not in log.read_text():
            raise RuntimeError("ACTUAL_FULL_BUILD_SUCCESS_MARKER_MISSING")
        identity_helper.capture(repo, lake=lake, lean=lean, expected=identity)
        receipt["state"] = "PASS"
    except Exception as error:
        receipt["state"] = "FAILED"
        receipt["error"] = repr(error)
        raise
    finally:
        dump(receipt_path, receipt)
    return {"state": receipt["state"], "receipt": str(receipt_path),
            "module_count": identity["module_count"], "source_tree_sha256": identity["source_tree_sha256"],
            "full_build": receipt["full_build"]}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--base-ref", required=True)
    parser.add_argument("--lake", required=True)
    parser.add_argument("--lean", required=True)
    args = parser.parse_args()
    print(json.dumps(run(args.repo, args.output, args.base_ref, args.lake, args.lean), indent=2))
