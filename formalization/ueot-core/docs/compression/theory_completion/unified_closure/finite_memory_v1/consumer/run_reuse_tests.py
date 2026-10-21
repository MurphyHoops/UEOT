#!/usr/bin/env python3
"""Run the installed 50-test reuse suite once and retain its exact output."""
import argparse
from datetime import datetime, timezone
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time


def encoded(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + "\n").encode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True)
    parser.add_argument("--proposal", required=True)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    repo, proposal = Path(args.repo).resolve(strict=True), Path(args.proposal).resolve(strict=True)
    output = Path(args.output).resolve()
    applied_path = proposal / "APPLIED_CONSUMER_UPDATE.json"
    applied_bytes = applied_path.read_bytes()
    applied = json.loads(applied_bytes)
    if applied["state"] != "APPLIED_FIVE_CONSUMERS_TESTS_PENDING":
        raise RuntimeError("CONSUMER_PROPOSAL_NOT_APPLIED")
    files = applied["files"]
    before = {row["path"]: sha256((repo / row["path"]).read_bytes()).hexdigest() for row in files}
    if any(before[row["path"]] != row["after_sha256"] for row in files):
        raise RuntimeError("INSTALLED_CONSUMER_DIFFERS_FROM_REVIEWED_PROPOSAL")
    suite = "formalization/ueot-core/docs/compression/theory_completion/knowledge/reuse/test_fkrg_reuse.py"
    command = [sys.executable, suite, "-v"]
    started = {"schema": "FINITE_MEMORY_REUSE_TEST_EXECUTION_V1", "state": "RUNNING",
               "started_utc": datetime.now(timezone.utc).isoformat(),
               "baseline_ref": applied["baseline_ref"], "source_tree_sha256": applied["source_tree_sha256"],
               "command": command, "cwd": str(repo), "expected_tests": 50,
               "proposal_patch_sha256": applied["patch_sha256"],
               "applied_receipt_sha256": sha256(applied_bytes).hexdigest(),
               "runner_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
               "before_consumer_sha256s": before}
    output.mkdir(parents=True, exist_ok=False)
    (output / "STARTED.json").write_bytes(encoded(started))
    begin = time.monotonic()
    with (output / "reuse-tests.log").open("xb") as log:
        result = subprocess.run(command, cwd=repo, stdout=log, stderr=subprocess.STDOUT,
                                env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"})
    log = (output / "reuse-tests.log").read_bytes()
    matches = re.findall(rb"Ran (\d+) tests? in ", log)
    count = int(matches[-1]) if matches else None
    after = {row["path"]: sha256((repo / row["path"]).read_bytes()).hexdigest() for row in files}
    passed = result.returncode == 0 and count == 50 and before == after
    receipt = {**started, "state": "PASS" if passed else "FAIL",
               "finished_utc": datetime.now(timezone.utc).isoformat(),
               "exit_code": result.returncode, "seconds": round(time.monotonic() - begin, 3),
               "observed_tests": count, "after_consumer_sha256s": after,
               "consumer_files_unchanged_during_test": before == after,
               "log_name": "reuse-tests.log", "log_bytes": len(log), "log_sha256": sha256(log).hexdigest(),
               "scope": "All 47 retained reuse tests plus three finite-memory native/source/metadata regressions; includes the existing full-current clone regeneration test. No FKRG 30-test or Lean run."}
    (output / "REUSE_TEST_RECEIPT.json").write_bytes(encoded(receipt))
    print(json.dumps({key: receipt[key] for key in ("state", "exit_code", "seconds", "observed_tests", "log_sha256")}, indent=2))
    if not passed:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
