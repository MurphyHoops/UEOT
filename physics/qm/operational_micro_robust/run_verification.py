#!/usr/bin/env python3
"""Execute only the v31.11 increment and preserve actual command identities.

This runner does not execute unchanged historical suites. Synthetic output is
explicitly synthetic, and finite exact checks are not universal proofs.
"""
from datetime import datetime, timezone
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
QM = HERE.parent


def identity(path):
    label = str(path.relative_to(REPO)) if path.is_relative_to(REPO) else str(path)
    return {"path": label,
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "bytes": path.stat().st_size}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", type=Path,
                        default=QM / "kernel/evidence/v31.11/runtime")
    args = parser.parse_args()
    out = args.output_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    inputs = sorted([*HERE.glob("*.py"), *HERE.glob("*.json")])
    inputs = [p for p in inputs if p.name not in
              {"operational_controls_receipt.json", "candidate.json", "exact_check_receipt.json"}]
    inputs += [QM / "conditioning/finite_conditioning.py",
               QM / "audits/OPERATIONAL_MICRO_ROBUST_v31.11/SHARED_MODEL.md",
               QM / "audits/OPERATIONAL_MICRO_ROBUST_v31.11/C_ROBUST_CALIBRATION.md"]
    before = [identity(p) for p in inputs]
    commands = []

    def execute(label, script, extra=()):
        command = [sys.executable, str(HERE / script), *map(str, extra)]
        started = datetime.now(timezone.utc).isoformat()
        result = subprocess.run(command, cwd=REPO, capture_output=True, text=True)
        log = out / (label + ".log")
        log.write_text(result.stdout + result.stderr)
        commands.append({"label": label, "argv": command, "cwd": str(REPO),
                         "started_at_utc": started,
                         "finished_at_utc": datetime.now(timezone.utc).isoformat(),
                         "exit_code": result.returncode, "log": identity(log)})
        if result.returncode:
            (out / "failed-execution.json").write_text(json.dumps(commands, indent=2)+"\n")
            raise RuntimeError(f"Actual command failed: {label}; inspect {log}")

    execute("operational-controls", "check_operational_controls.py")
    generated = HERE / "operational_controls_receipt.json"
    shutil.copyfile(generated, out / generated.name)
    generated.unlink()
    execute("micro-truncation", "check_micro_truncation.py",
            ["--output", out / "micro-truncation.json"])
    execute("certificate-producer", "robust_certificate.py",
            ["--model", HERE / "frozen_model.json", "--output", out / "candidate.json"])
    execute("certificate-independent-checker", "exact_checker.py",
            ["--model", HERE / "frozen_model.json", "--candidate", out / "candidate.json",
             "--output", out / "exact-certificate.json"])
    with tempfile.TemporaryDirectory(prefix="ueot-v31-11-crosscheck-") as temp:
        temp = Path(temp)
        for source, name in [(HERE / "frozen_model.json", "frozen_model.json"),
                             (out / "candidate.json", "candidate.json"),
                             (inputs[-1], "C_ROBUST_CALIBRATION.md")]:
            (temp / name).symlink_to(source)
        execute("independent-b-review-check", "review_c_exact.py",
                ["--c-dir", temp, "--output", out / "independent-b-check.json"])
    execute("source-to-cq-integration", "verify_integration.py", ["--output-dir", out])
    execute("synthetic-calibration-and-holdout", "synthetic_calibration.py",
            ["--model", HERE / "frozen_model.json", "--output-dir", out / "synthetic"])
    after = [identity(p) for p in inputs]
    assert before == after, "Consumed source changed during execution"
    github_actions = os.environ.get("GITHUB_ACTIONS") == "true"
    checkout = subprocess.run(["git", "rev-parse", "HEAD"], cwd=REPO,
                              capture_output=True, text=True)
    execution_context = {
        "provider": "github_actions" if github_actions else "local_python_process",
        "observed_git_head": checkout.stdout.strip() if checkout.returncode == 0 else None,
        "identity_authority": "The consumed-input hashes bind actual bytes; git HEAD alone does not identify a dirty worktree",
    }
    if github_actions:
        execution_context["workflow"] = {key: os.environ.get(key) for key in
            ["GITHUB_REPOSITORY", "GITHUB_RUN_ID", "GITHUB_RUN_ATTEMPT",
             "GITHUB_JOB", "GITHUB_EVENT_NAME", "GITHUB_SHA"]}
    receipt = {"schema": "ueot-qm.runtime-increment/2", "version": "v31.11",
               "status": "PASS", "created_at_utc": datetime.now(timezone.utc).isoformat(),
               "baseline": "16a89154183c22030d4526413167d095d94e6890",
               "execution_actor": "GitHub Actions runner" if github_actions else "local Python process",
               "execution_context": execution_context,
               "python": sys.version, "platform": platform.platform(),
               "commands": commands, "inputs": before, "inputs_stable_during_execution": True,
               "outputs": [identity(p) for p in sorted(out.rglob("*"))
                           if p.is_file() and p.name not in {"execution_receipt.json", "failed-execution.json"}
                           and "prior" not in p.parts],
               "evidence_classes": ["exact finite symbolic arithmetic", "floating diagnostics",
                                    "synthetic iid coverage and finite-record holdout",
                                    "synthetic correlated-trial failure control"],
               "not_evidence_of": ["hardware accuracy", "new natural law", "experimental closure",
                                   "universal proof by finite sampling", "full-state tomography"],
               "historical_suites_reexecuted": False, "new_hardware_data": False}
    (out / "execution_receipt.json").write_text(json.dumps(receipt, indent=2)+"\n")
    print(json.dumps({"status": "PASS", "commands": len(commands),
                      "input_count": len(before), "new_hardware_data": False}))


if __name__ == "__main__":
    main()
