#!/usr/bin/env python3
"""Execute the unchanged full canonical audit with fixed build/input identity."""
from __future__ import annotations

import argparse
from hashlib import sha256
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import time

PREFIX = "formalization/ueot-core/docs/compression/theory_completion/"
INPUTS = [
    PREFIX + "unified_closure/UMC_GLOBAL_MODULE_DAG_V4.json",
    PREFIX + "knowledge/README.md",
    PREFIX + "knowledge/reuse/fkrg_reuse.py",
    PREFIX + "knowledge/reuse/test_fkrg_reuse.py",
    PREFIX + "knowledge/reuse/README.md",
    PREFIX + "knowledge/reuse/REBUILD_CLONE_CANDIDATES.py",
    PREFIX + "knowledge/reuse/TOTAL_KERNEL_MEMORY_REUSE_OVERLAY_V1.json",
    PREFIX + "knowledge/reuse/TOTAL_KERNEL_MEMORY_NATIVE_V1.json",
    PREFIX + "knowledge/reuse/VERIFY_TOTAL_KERNEL_MEMORY_OVERLAY_TYPES.lean",
    PREFIX + "unified_closure/audit_umc_local.py",
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for key in ("repo", "output", "build-receipt", "lake", "lean"):
        parser.add_argument("--" + key, type=Path, required=True)
    args = parser.parse_args()
    repo, out = args.repo.resolve(strict=True), args.output.resolve()
    if not __debug__ or sys.flags.optimize or os.environ.get("PYTHONOPTIMIZE"):
        raise RuntimeError("NORMAL_UNOPTIMIZED_PYTHON_REQUIRED")
    out.mkdir(parents=True, exist_ok=False)
    build = json.loads(args.build_receipt.read_bytes())
    assert build["state"] == "PASS"
    helper_path = repo / (PREFIX + "unified_closure/registered_interfaces/native_protocol/build_identity.py")
    assert sha256(helper_path.read_bytes()).hexdigest() == build["identity_helper_sha256"]
    spec = importlib.util.spec_from_file_location("canonical_build_identity", helper_path)
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    before = helper.capture(repo, lake=args.lake, lean=args.lean, expected=build["identity"])
    inputs = [{"path": p, "sha256": sha256((repo / p).read_bytes()).hexdigest()} for p in INPUTS]
    auditor = repo / (PREFIX + "unified_closure/audit_umc_local.py")
    command = [sys.executable, "-B", str(auditor), "--full", "--output", str(out / "UMC_FULL_AUDIT.json")]
    environment = os.environ.copy()
    environment["PATH"] = str(args.lake.parent) + os.pathsep + environment["PATH"]
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    start = time.monotonic()
    result = subprocess.run(command, cwd=repo, env=environment, capture_output=True)
    seconds = time.monotonic() - start
    (out / "STDOUT.txt").write_bytes(result.stdout)
    (out / "STDERR.txt").write_bytes(result.stderr)
    after = helper.capture(repo, lake=args.lake, lean=args.lean, expected=before)
    stable = all(sha256((repo / row["path"]).read_bytes()).hexdigest() == row["sha256"] for row in inputs)
    passed = result.returncode == 0 and stable and before == after
    if passed:
        audit = json.loads((out / "UMC_FULL_AUDIT.json").read_bytes())
        passed = (audit["full_Lean"] == "PASS" and audit["global_bundled_Lean_modules"] == 694
                  and audit["global_strong_unified_closure"] == "NOT_ESTABLISHED"
                  and audit["scientific_external_evidence"] == "UNVERIFIED")
    receipt = {
        "schema": "TOTAL_KERNEL_MEMORY_CANONICAL_EXECUTION_V1",
        "state": "PASS" if passed else "FAIL",
        "command": command, "exit_code": result.returncode, "seconds": round(seconds, 3),
        "runner_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "build_receipt_sha256": sha256(args.build_receipt.read_bytes()).hexdigest(),
        "source_tree_sha256": before["source_tree_sha256"],
        "module_count": before["module_count"],
        "source_runtime_dependencies_equal_before_after": before == after,
        "source_runtime_dependencies_equal_to_full_build": before == build["identity"],
        "input_files": inputs, "input_files_unchanged": stable,
        "stdout_sha256": sha256(result.stdout).hexdigest(),
        "stderr_sha256": sha256(result.stderr).hexdigest(),
        "audit_sha256": sha256((out / "UMC_FULL_AUDIT.json").read_bytes()).hexdigest() if (out / "UMC_FULL_AUDIT.json").exists() else None,
    }
    (out / "EXECUTION_RECEIPT.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
