"""Bounded execution wrapper: actual logs, source identity and environment receipts."""
import argparse
from datetime import datetime, timezone
import hashlib
from importlib.metadata import version, PackageNotFoundError
import json
from pathlib import Path
import platform
import subprocess
import sys
import time
import traceback


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    out = args.output_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    versions = {"python": sys.version, "platform": platform.platform()}
    for package in ("numpy", "scipy", "sympy"):
        try:
            versions[package] = version(package)
        except PackageNotFoundError:
            versions[package] = "NOT_INSTALLED"
    source_names = ["finite_conditioning.py", "fixtures.py", "frozen_plan.json", "positive_chain_plan.json", "test_finite_conditioning.py",
                    "exact_witnesses.py", "run_reference.py", "verify_runtime.py", "README.md"]
    manifest = {n: hashlib.sha256((root / n).read_bytes()).hexdigest() for n in source_names}
    commands = [
        ("semantic_tests", [sys.executable, "-m", "unittest", "-v", "test_finite_conditioning.py"]),
        ("exact_witnesses", [sys.executable, "exact_witnesses.py", "--output-dir", str(out)]),
        ("numerical_reference", [sys.executable, "run_reference.py", "--output-dir", str(out)]),
    ]
    gates = []
    for name, argv in commands:
        start = time.monotonic()
        checked_at = datetime.now(timezone.utc).isoformat()
        try:
            result = subprocess.run(argv, cwd=root, text=True, capture_output=True, timeout=60)
            stdout, stderr, code = result.stdout, result.stderr, result.returncode
            status = "PASS" if code == 0 else "EXECUTION_FAILED"
        except subprocess.TimeoutExpired as exc:
            stdout = exc.stdout or ""
            stderr = exc.stderr or ""
            if isinstance(stdout, bytes):
                stdout = stdout.decode(errors="replace")
            if isinstance(stderr, bytes):
                stderr = stderr.decode(errors="replace")
            stderr += "\nTIMEOUT: an infrastructure failure, not a mathematical rejection.\n"
            code, status = None, "INFRASTRUCTURE_TIMEOUT"
        except Exception:
            stdout, stderr, code, status = "", traceback.format_exc(), None, "INFRASTRUCTURE_ERROR"
        log = out / (name + ".log")
        log.write_text("STDOUT\n" + stdout + "\nSTDERR\n" + stderr)
        gates.append({"name": name, "status": status, "returncode": code, "command": argv,
                      "started_at_utc": checked_at, "seconds": time.monotonic() - start,
                      "log": log.name, "log_sha256": hashlib.sha256(log.read_bytes()).hexdigest()})
    identity_unchanged = all(hashlib.sha256((root / n).read_bytes()).hexdigest() == digest
                             for n, digest in manifest.items())
    passed = all(g["status"] == "PASS" for g in gates) and identity_unchanged
    receipt = {"schema": "ueot-qm.finite-reference-execution/1", "status": "PASS" if passed else "FAILED",
               "evidence_scope": "actual numerical/semantic tests and exact finite symbolic witnesses; not general Lean or hardware evidence",
               "executed_at_utc": datetime.now(timezone.utc).isoformat(), "source_directory": str(root),
               "versions": versions, "source_sha256": manifest, "source_unchanged_during_execution": identity_unchanged,
               "gates": gates, "real_hardware_data": False}
    (out / "execution_receipt.json").write_text(json.dumps(receipt, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({"status": receipt["status"], "gates": [{"name": g["name"], "status": g["status"]} for g in gates],
                      "receipt": str(out / "execution_receipt.json")}))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
