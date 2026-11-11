#!/usr/bin/env python3
"""Verify exact inherited proof inputs without reporting a new Lean build.

CI may reuse the pinned v31.11 proof execution only when its recorded bytes and
the entire proof/tool inventory are unchanged. A new/changed source or checker
selects the existing full Lean job. Current paper claims acquire no Lean status.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess

REPO = Path(__file__).resolve().parents[3]
BASE = "06ca0dce8b03cd34e86785e97fdc3c7aa2c582bd"
EVIDENCE = "physics/qm/kernel/evidence/v31.11/"
PINNED = {
    "source-manifest.json": "ec214db86cebe2e0bae2f02e5fe2028fc63d99c585ad655170bc2c9f4881bb2a",
    "lean-verification.json": "45afc9ee3bc2d02fd0c687c60910b5775831844a68416373e05f32fcdf21af8c",
    "remote/main/github-run.json": "d9d60b2f3859f7acf4730cd774c7b67ebc4ab556f118fa35e98aba61342b5cbf",
    "remote/main/lean-inspection.json": "f32d0a4e5b1320e87cb3cf63f6fa22d005aaf225e4c3c29409b569f8feb77575",
    "runtime/execution_receipt.json": "44c4d1a1e06144c1b8f7932fc576cba5e17e0fdf669a0198f480e390c5547523",
}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inspect():
    errors = []
    for name, expected in PINNED.items():
        path = REPO / EVIDENCE / name
        if not path.is_file() or digest(path) != expected:
            errors.append("pinned historical receipt changed: " + name)
    if errors:
        return {"proof_reuse_eligible": False, "errors": errors}
    manifest = json.loads((REPO / EVIDENCE / "source-manifest.json").read_text())
    entries = manifest["sources"]
    if len(entries) != 158:
        errors.append("unexpected historical proof inventory")
    for item in entries:
        path = REPO / item["path"]
        if not path.is_file() or digest(path) != item["sha256"] or path.stat().st_size != item["bytes"]:
            errors.append("proof input mismatch: " + item["path"])
    # Compare full inventories, so an added module or changed verification tool
    # outside the old manifest cannot silently ride on the old proof receipt.
    selectors = ["formalization/ueot-qm", "formalization/ueot-core",
                 "physics/qm/kernel", ":(exclude)physics/qm/kernel/evidence/**"]
    try:
        changed = subprocess.check_output(["git", "diff", "--name-only", BASE,
                   "--", *selectors], cwd=REPO, text=True).splitlines()
        untracked = subprocess.check_output(["git", "ls-files", "--others", "--exclude-standard",
                     "--", *selectors], cwd=REPO, text=True).splitlines()
        if changed or untracked:
            errors.extend("changed proof/tool inventory: " + x for x in sorted(set(changed+untracked)))
    except subprocess.CalledProcessError:
        errors.append("verified historical Git object unavailable; cannot reuse")
    run = json.loads((REPO / EVIDENCE / "remote/main/github-run.json").read_text())
    if run["head_sha"] != BASE or run["conclusion"] != "success":
        errors.append("historical CI identity is not the verified scientific main")
    runtime = json.loads((REPO / EVIDENCE / "runtime/execution_receipt.json").read_text())
    runtime_errors = []
    if runtime.get("status") != "PASS" or len(runtime.get("inputs", [])) != 13 or len(runtime.get("commands", [])) != 7:
        runtime_errors.append("historical runtime receipt must be PASS with 13 inputs and 7 commands")
    for item in runtime["inputs"]:
        path = REPO / item["path"]
        if not path.is_file() or digest(path) != item["sha256"]:
            runtime_errors.append(item["path"])
    return {"proof_reuse_eligible": not errors, "errors": errors,
            "proof_input_count":len(entries),"proof_source_set_sha256":manifest["source_set_sha256"],
            "old_runtime_input_count":len(runtime["inputs"]),
            "old_runtime_inputs_identical":not runtime_errors,"runtime_mismatches":runtime_errors,
            "reused_proof_commit":BASE,"reused_workflow_run":run["id"],
            "reused_axiom_reports":1365,"new_lean_execution":False,
            "new_lean_theorems":0,"new_paper_claims_not_promoted_to_lean":True}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path,required=True)
    parser.add_argument("--detect",action="store_true",help="CI selection: report mismatch without failing the full-build fallback")
    parser.add_argument("--github-output",type=Path)
    args=parser.parse_args()
    report=inspect()
    report.update({"schema":"ueot-qm.scoped-proof-reuse/1",
                   "checked_at_utc":datetime.now(timezone.utc).isoformat(),
                   "status":"SOURCE_IDENTITY_REUSED" if report["proof_reuse_eligible"] else "FULL_LEAN_REQUIRED",
                   "new_hardware_data":False})
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+"\n")
    if args.github_output:
        with args.github_output.open("a") as stream:
            stream.write("reuse="+str(report["proof_reuse_eligible"]).lower()+"\n")
    print(json.dumps(report))
    if not args.detect and (not report["proof_reuse_eligible"] or not report.get("old_runtime_inputs_identical")):
        raise SystemExit(1)


if __name__=="__main__":main()
