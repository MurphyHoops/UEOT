#!/usr/bin/env python3
"""Capture one unchanged canonical UMC audit against the accepted build identity."""
import argparse
import datetime
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

parser = argparse.ArgumentParser(description=__doc__)
for name in ("repo", "output", "build-receipt"):
    parser.add_argument("--" + name, required=True)
args = parser.parse_args()
repo = Path(args.repo).resolve(strict=True)
out = Path(args.output).resolve()
if out.exists():
    raise RuntimeError("NEW_CANONICAL_EXECUTION_DIRECTORY_REQUIRED")
out.mkdir(parents=True)
driver = Path(__file__).read_bytes()
(out / "driver.py").write_bytes(driver)
build_path = Path(args.build_receipt).resolve(strict=True)
build_bytes = build_path.read_bytes()
build = json.loads(build_bytes)
assert build["state"] == "PASS" and build["full_build"]["exit_code"] == 0
helper_path = repo / "formalization/ueot-core/docs/compression/theory_completion/unified_closure/registered_interfaces/native_protocol/build_identity.py"
assert hashlib.sha256(helper_path.read_bytes()).hexdigest() == build["identity_helper_sha256"]
spec = importlib.util.spec_from_file_location("canonical_umc_build_identity", helper_path)
identity = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = identity
spec.loader.exec_module(identity)
runtime = build["identity"]["runtime_tools"]
lake, lean = runtime["lake"]["executable"], runtime["lean"]["executable"]
assert str(Path(shutil.which("lake")).resolve()) == str(Path(lake).resolve())
assert str(Path(shutil.which("lean")).resolve()) == str(Path(lean).resolve())
identity.capture(repo, lake=lake, lean=lean, expected=build["identity"])
command = [sys.executable, "-B", "formalization/ueot-core/docs/compression/theory_completion/unified_closure/audit_umc_local.py",
           "--full", "--output", str(out / "UMC_FULL_AUDIT.json")]
environment = os.environ.copy()
environment["PYTHONDONTWRITEBYTECODE"] = "1"
started = datetime.datetime.now(datetime.timezone.utc).isoformat()
begin = time.monotonic()
result = subprocess.run(command, cwd=repo, env=environment, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
(out / "canonical-audit.log").write_bytes(result.stdout)
receipt = {"state": "AUDIT_EXIT_ZERO_POSTCHECK_PENDING" if result.returncode == 0 else "FAIL", "started_at_utc": started,
           "command": command, "exit_code": result.returncode, "seconds": time.monotonic() - begin,
           "log_sha256": hashlib.sha256(result.stdout).hexdigest(),
           "driver_sha256": hashlib.sha256(driver).hexdigest(),
           "full_build_receipt_sha256": hashlib.sha256(build_bytes).hexdigest(),
           "source_tree_sha256": build["identity"]["source_tree_sha256"],
           "source_runtime_dependencies_before": "EXACT_ACCEPTED_FULL_BUILD_IDENTITY",
           "source_runtime_dependencies_after": "PENDING_POSTCHECK"}
(out / "EXECUTION.json").write_text(json.dumps(receipt, indent=2) + "\n")
identity.capture(repo, lake=lake, lean=lean, expected=build["identity"])
receipt["source_runtime_dependencies_after"] = "EXACT_ACCEPTED_FULL_BUILD_IDENTITY"
if result.returncode == 0:
    audit = json.loads((out / "UMC_FULL_AUDIT.json").read_text())
    assert audit["full_Lean"] == "PASS" and audit["global_bundled_Lean_modules"] == 691
    assert audit["global_strong_unified_closure"] == "NOT_ESTABLISHED"
    receipt["audit_sha256"] = hashlib.sha256((out / "UMC_FULL_AUDIT.json").read_bytes()).hexdigest()
    receipt["state"] = "PASS"
(out / "EXECUTION.json").write_text(json.dumps(receipt, indent=2) + "\n")
print(json.dumps(receipt, indent=2))
if result.returncode:
    print(result.stdout.decode(errors="replace")[-6000:])
raise SystemExit(result.returncode)
