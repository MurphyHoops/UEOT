#!/usr/bin/env python3
"""Targeted v31.11 compiler and exhaustive exported-namespace axiom audit."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time

from verify_finite_conditioning import source_closure, strip_comments, declarations

PACKAGE = Path(__file__).resolve().parents[1]
REPO = PACKAGE.parents[1]
SOURCE = PACKAGE / "UEOTQM/OperationalEquivalence.lean"
AUDIT = PACKAGE / "scripts/OperationalEquivalenceAxiomAudit.lean"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def inputs():
    rows = {r["path"]: r for r in source_closure(PACKAGE)}
    for p in [SOURCE, AUDIT, Path(__file__)]:
        key = str(p.relative_to(REPO))
        rows[key] = {"path": key, "sha256": digest(p), "bytes": p.stat().st_size}
    return [rows[k] for k in sorted(rows)]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    out = args.output_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    before = inputs()
    code = strip_comments(SOURCE.read_text())
    if re.search(r'^\s*(axiom|opaque)\s|\b(sorry|admit|native_decide)\b', code, re.M):
        raise ValueError("Forbidden proof escape in new source")
    inventory = declarations(SOURCE)
    gates = []
    for label, command in [
        ("dependencies", [sys.executable, "scripts/check_dependencies.py"]),
        ("new_module_build", ["lake", "build", "UEOTQM.OperationalEquivalence"]),
        ("new_namespace_axioms", ["lake", "env", "lean", str(AUDIT.relative_to(PACKAGE))]),
    ]:
        started = datetime.now(timezone.utc).isoformat()
        tic = time.monotonic()
        log = out/(label+".log")
        with log.open("w") as stream:
            result = subprocess.run(command, cwd=PACKAGE, stdout=stream, stderr=subprocess.STDOUT)
        gates.append({"name": label, "argv": command, "cwd": str(PACKAGE),
                      "started_at_utc": started, "seconds": time.monotonic()-tic,
                      "exit_code": result.returncode, "log": log.name, "log_sha256": digest(log)})
        print(json.dumps({"gate": label, "exit_code": result.returncode}), flush=True)
        if result.returncode:
            break
    reports = {}
    good = False
    if len(gates)==3 and all(g["exit_code"]==0 for g in gates):
        text = (out/"new_namespace_axioms.log").read_text()
        rows = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", text)
        reports = {n: sorted(a.strip() for a in aa.split(",") if a.strip()) for n,aa in rows}
        expected = re.search(r'AUDITED_NAMESPACE_DECLARATIONS (\d+)', text)
        good = (expected is not None and int(expected.group(1))==len(rows)==len(reports)
                and all(n.startswith("UEOTQM.OperationalEquivalence.") for n in reports)
                and all(set(a)<=ALLOWED for a in reports.values())
                and {r["name"] for r in inventory} <= set(reports))
    after = inputs()
    passed = good and before==after
    manifest = {"schema": "ueot_qm.recursive_scientific_inputs.v2", "sources": before,
                "source_count": len(before), "identity_unchanged_during_execution": before==after,
                "source_set_sha256": hashlib.sha256(json.dumps(before, sort_keys=True, separators=(",", ":")).encode()).hexdigest(),
                "scope": "Input closure inventory; execution is new target plus its dependencies and exhaustive new namespace only"}
    (out/"source-manifest.json").write_text(json.dumps(manifest, indent=2)+"\n")
    (out/"proof-axioms.json").write_text(json.dumps({"status": "PASS" if good else "FAILED",
        "allowed_foundation": sorted(ALLOWED), "declaration_count": len(reports), "declarations": reports}, indent=2)+"\n")
    (out/"new-declarations.json").write_text(json.dumps(inventory, indent=2)+"\n")
    receipt = {"schema": "ueot_qm.operational_equivalence_increment.v1", "status": "PASS" if passed else "FAILED",
               "recorded_at_utc": datetime.now(timezone.utc).isoformat(), "gates": gates,
               "source_sha256": digest(SOURCE), "source_set_sha256": manifest["source_set_sha256"],
               "source_count": len(before), "identity_unchanged_during_execution": before==after,
               "new_modules": 1, "new_explicit_theorems": sum(r["kind"]=="theorem" for r in inventory),
               "new_explicit_named_declarations": len(inventory), "new_named_axiom_reports": len(reports),
               "allowed_axioms_only": good, "all_new_exported_namespace_constants_audited": good,
               "ordinary_lean_linter_warnings_present": True, "new_hardware_data": False,
               "scope": "Actual new-module build and all exported constants in its namespace; full OPT, trace-class and robust paper proofs are not inferred",
               "historical_gate_policy": "Unchanged historical execution identity is reused; no claim of a fresh local unified historical gate"}
    (out/"lean-verification.json").write_text(json.dumps(receipt, indent=2)+"\n")
    print(json.dumps({k: receipt[k] for k in ["status", "new_explicit_theorems", "new_named_axiom_reports", "source_sha256"]}), flush=True)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
