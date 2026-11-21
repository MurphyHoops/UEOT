"""Reproduce this continuation without rebuilding unchanged Lean or the books.

Each entry's own scope is retained. Passing this runner does not close the
physical dynamic RSET, the apparatus transfer or the unified physics goal.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import json
import os
import subprocess
import sys
import time

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[4]
BASE="a3ae75078ae903163bf0759fbd302e836aeeea84"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run():
    if not __debug__:
        raise RuntimeError("verification requires assertions; do not use -O")
    base_paths=[
        "physics/qm/null_source/timelike/instrument/instrument.py",
        "physics/qm/null_source/timelike/instrument/joint_bound.py",
        "physics/qm/null_source/timelike/instrument/result.json",
        "physics/qm/null_source/timelike/identification/reference.py",
        "physics/qm/null_source/FINITE_WINDOW.md",
        "physics/qm/status/CURRENT.json",
        "formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/ScientificClosure/SISCFutureResponseCore.lean",
    ]
    inherited={}
    for rel in base_paths:
        old=subprocess.run(["git","show",f"{BASE}:{rel}"],cwd=REPO,check=True,capture_output=True).stdout
        current=(REPO/rel).read_bytes()
        if old!=current:
            raise RuntimeError(f"Inherited scientific input changed: {rel}; review its reuse first")
        inherited[rel]=hashlib.sha256(current).hexdigest()
    env=dict(os.environ,OPENBLAS_NUM_THREADS="1",OMP_NUM_THREADS="1",PYTHONDONTWRITEBYTECODE="1")
    entries=[("shared_reference",["source_contract.py"]),
             ("minimal_quantum_stress",["quantum/minimal_response.py","--check"]),
             ("apparatus_constraints",["apparatus/shell.py","--check"]),
             ("finite_data_identification",["identification/check.py","--check"]),
             ("independent_stress_apparatus_review",["identification/review_bc.py","--check"])]
    results=[]
    for name,args in entries:
        started=time.monotonic()
        proc=subprocess.run([sys.executable,"-B",str(HERE/args[0]),*args[1:]],
                            cwd=REPO,env=env,capture_output=True,text=True)
        row={"entry":name,"returncode":proc.returncode,
             "duration_seconds":round(time.monotonic()-started,3),
             "stdout_sha256":hashlib.sha256(proc.stdout.encode()).hexdigest()}
        if proc.returncode:
            print(proc.stdout);print(proc.stderr,file=sys.stderr)
            raise RuntimeError(f"Failed scientific reproduction: {name}")
        results.append(row)
        print(f"PASS {name}",flush=True)
    manifest={}
    for path in sorted(HERE.rglob("*")):
        if path.is_file() and path.suffix in (".py",".json",".md") and path.name not in ("verification.json","integration.json"):
            manifest[str(path.relative_to(REPO))]=digest(path)
    return {"schema":"ueot-physics-source-response-verification/1",
        "timestamp_utc":datetime.now(timezone.utc).isoformat(),
        "scientific_base":BASE,
        "git_head_at_execution":subprocess.check_output(["git","rev-parse","HEAD"],cwd=REPO,text=True).strip(),
        "python":sys.version,"new_entry_results":results,
        "inherited_inputs_unchanged":inherited,"current_source_manifest":manifest,
        "mathematical_scope":"finite-budget statistical theorem; exact minimal state difference; classical apparatus counterexample",
        "numerical_scope":"certified auxiliary static RSET tail; apparatus intervals; diagnostic ODE; 400000 synthetic pointer starts",
        "dynamic_absolute_RSET_on_physical_sphere":"OPEN",
        "finite_error_nonlinear_feedback":"OPEN",
        "apparatus_full_protocol_calibration":"OPEN",
        "Core_unique_physical_selection":"OPEN",
        "new_Lean_proofs":False,"matched_device_data":False,
        "whole_unified_physics_goal":"OPEN"}


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    args=parser.parse_args()
    result=run()
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(result,indent=2,ensure_ascii=False)+"\n")
        print(f"Saved {args.output}")
    else:
        print(json.dumps(result,indent=2,ensure_ascii=False))
