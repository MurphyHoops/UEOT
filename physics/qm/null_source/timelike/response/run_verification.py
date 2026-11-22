"""Run four new response checks and reuse 18 unchanged scientific entries.

Old scientific inputs are frozen to d6ec9eda. Four routing/documentation files
that the old local receipt also recorded are allowed to change, are checked
against their historical hashes, and are frozen again in the current manifest.
They are not inputs to any of the four old scientific checkers.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
from importlib.metadata import version
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import tempfile
import time

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[4]
BASE="d6ec9eda409ba78d1d7993d7648ba26b5a34374d"
WORKFLOW=".github/workflows/ueot-physics-source-response.yml"
PREFIX="physics/qm/null_source/timelike/"
RANGES=[
 PREFIX+"continuation/",PREFIX+"evolution/",PREFIX+"compatibility/",
 PREFIX+"instrument/",PREFIX+"identification/",
 "physics/qm/null_source/FINITE_WINDOW.md",
 "physics/qm/status/CURRENT.json",
 "formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/ScientificClosure/SISCFutureResponseCore.lean",
]
ROUTES=[WORKFLOW,"physics/qm/README.md","physics/qm/ROADMAP.md",PREFIX+"README.md"]
VERSIONS={"numpy":"2.5.4","scipy":"1.18.1","sympy":"1.14.0","mpmath":"1.3.0"}
ENTRIES=[
 ("biased_sign_preparation_and_records","preparation/check.py"),
 ("full_noise_scaling_and_local_linear_bound","noise/check.py"),
 ("constraint_preserving_linear_geometry","geometry/check.py"),
 ("independent_geometry_state_and_scope_review","review.py"),
]

def sha(data):return hashlib.sha256(data).hexdigest()
def file_sha(path):return sha(path.read_bytes())
def git(*args):return subprocess.check_output(["git",*args],cwd=REPO)
def require(value,message):
    if not value:raise RuntimeError(message)
def names(*args):return {p.decode() for p in git(*args).split(b"\0") if p}
def inherited_manifest():
    old=names("ls-tree","-rz","--name-only",BASE,"--",*RANGES)
    current=names("ls-files","-z","--cached","--others","--exclude-standard","--",*RANGES)
    require(old==current,"Inherited inventory changed: "+repr(sorted(old^current)))
    require(len(old)==76,"Unexpected predecessor scientific file count")
    result={}
    for rel in sorted(old):
        p=REPO/rel
        require(p.is_file() and not p.is_symlink(),"Nonregular inherited file: "+rel)
        expected=sha(git("show",BASE+":"+rel));actual=file_sha(p)
        require(actual==expected,"Inherited scientific bytes changed: "+rel)
        result[rel]=actual
    return result
def current_manifest():
    paths=[p for p in HERE.rglob("*") if p.is_file() and "__pycache__" not in p.parts
           and p!=HERE/"verification.json" and p.suffix in {".py",".json",".md"}]
    paths += [REPO/p for p in ROUTES]
    return {str(p.relative_to(REPO)):file_sha(p) for p in sorted(set(paths))}

def check_ci(snapshot,head,run_id,steps):
    run=snapshot["run"]
    require(run["head_sha"]==head and run["id"]==run_id and
            run["status"]=="completed" and run["conclusion"]=="success" and
            run["path"]==WORKFLOW,"Predecessor CI identity/status mismatch")
    require(run["html_url"]=="https://github.com/MurphyHoops/UEOT/actions/runs/"+str(run_id),
            "Unexpected predecessor CI URL")
    job=next(j for j in snapshot["jobs"] if j["name"]=="reproduce")
    require(job["head_sha"]==head and job["conclusion"]=="success","CI job did not pass head")
    for name in steps:
        row=next(s for s in job["steps"] if s["name"]==name)
        require(row["status"]=="completed" and row["conclusion"]=="success","CI step not passed")
    return run

def predecessor_evidence(inherited):
    receipts=[];routes={}
    def consume_manifest(manifest,allow_routes=False):
        for path,expected in manifest.items():
            require(sha(git("show",BASE+":"+path))==expected,
                    "Old receipt did not bind its archived source: "+path)
            if path in inherited:
                require(inherited[path]==expected,"Transitive scientific input changed: "+path)
            else:
                require(allow_routes and path in ROUTES,"Unfrozen transitive input: "+path)
                routes[path]={
                    "previous_receipt_sha256":expected,
                    "current_sha256":file_sha(REPO/path),
                    "role":"reading route or workflow; not consumed by predecessor scientific checkers",
                    "current_bytes_frozen_in_new_manifest":True,
                }
    for directory,field,count in [
        ("continuation","new_entry_results",5),
        ("evolution","entries",9),
        ("compatibility","executed_now",4),
    ]:
        path=PREFIX+directory+"/verification.json"
        old=json.loads((REPO/path).read_text());rows=old[field]
        require(len(rows)==count and all(r["returncode"]==0 for r in rows),
                "Predecessor receipt failed: "+directory)
        consume_manifest(old["current_source_manifest"],directory=="compatibility")
        if directory=="compatibility":
            require(old["status"]=="PASS" and old["new_mode_integrations"]==0,
                    "Unexpected compatibility receipt status")
            consume_manifest(old["reused"]["inherited_source_manifest"])
        else:
            consume_manifest(old["inherited_inputs_unchanged"])
        receipts.append({
            "path":path,"sha256":inherited[path],
            "local_git_head_at_execution":old["git_head_at_execution"],
            "entries":[r["entry"] for r in rows],"count":count,
            "executed_again_this_run":False,
        })
    require(set(routes)==set(ROUTES),"Expected four audited routing files")
    previous=json.loads((REPO/(PREFIX+"compatibility/baseline_ci.json")).read_text())
    ci14=check_ci(previous,"1a90c68b6178968e6b8239fc97a8b26200f8d59d",44491673166,[
        "Reproduce source binding, stress, apparatus and finite-data results",
        "Reproduce dynamic stress, initial constraint and finite-window inference",
    ])
    current=json.loads((HERE/"baseline_ci.json").read_text())
    ci4=check_ci(current,BASE,44499725123,[
        "Reuse unchanged predecessor proofs and verify four compatibility results",
    ])
    return {
        "base_commit":BASE,"inherited_scientific_file_count":len(inherited),
        "inherited_scientific_manifest":inherited,
        "entry_count_reused":18,"archived_local_receipts":receipts,
        "exact_head_ci_proof_chain":[ci14,ci4],
        "ci_observation_semantics":current["semantics"],
        "audited_routing_changes":routes,
        "old_workflow_at_base_sha256":sha(git("show",BASE+":"+WORKFLOW)),
    }

def scientific_exit():
    review=json.loads((HERE/"review.json").read_text())
    require(review["new_mode_integrations"]==0,"Unexpected new mode integration")
    n=review["numerical"];q=review["joint_finite_test_scale_theorem"]
    require(Fraction(n["uniform_first_order_scale_relative_upper"][1])<Fraction(1,4000),
            "Independent scale response budget failed")
    require(n["distance_to_exact_SCE_solution_certified"] is False,
            "Linear response mislabeled as exact SCE distance")
    require(q["full_C0_numerical_upper_bound_at_8192_available"] is False and
            q["uniform_over_all_resolutions_at_fixed_lambda"] is False,
            "Noise scope upgraded without proof")
    return {
        "independent_review":n,"fixed_finite_test_theorem":q,
        "component_receipts":{directory:{
            "path":str((HERE/directory/"result.json").relative_to(REPO)),
            "sha256":file_sha(HERE/directory/"result.json")}
            for directory in ["preparation","noise","geometry"]},
        "new_preparation_and_conditional_records":"CERTIFIED",
        "background_sourced_linear_Einstein_scalar_response":"CERTIFIED",
        "full_noise_numerics_at_lambda8192":"C0_STILL_OPEN",
        "full_nonlinear_SCE_and_stability":"OPEN",
        "physical_device_and_driver_realization":"OPEN",
        "Core_unique_physical_selection":"OPEN",
        "new_Lean_proofs":False,"new_matching_hardware_data":False,
        "whole_unified_physics_goal":"OPEN",
    }

def main():
    require(__debug__ and sys.flags.optimize==0,"Use unoptimized Python for proof assertions")
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output",type=Path,default=HERE/"verification.json")
    ap.add_argument("--logs",type=Path)
    args=ap.parse_args();output=args.output.resolve()
    logs=(args.logs or Path(tempfile.mkdtemp(prefix="ueot-response-logs-"))).resolve()
    require(REPO not in logs.parents and logs!=REPO,"Logs must be outside repository")
    require(output==HERE/"verification.json" or (REPO not in output.parents and output!=REPO),
            "Only default verification.json may be written inside repository")
    require(sys.version_info[:2]==(3,14),"Replay requires Python 3.14")
    actual={k:version(k) for k in VERSIONS}
    require(actual==VERSIONS,"Scientific dependency versions changed")
    logs.mkdir(parents=True,exist_ok=True);output.parent.mkdir(parents=True,exist_ok=True)
    old_before=inherited_manifest();reused=predecessor_evidence(old_before)
    new_before=current_manifest()
    head=git("rev-parse","HEAD").decode().strip();status=git("status","--short").decode()
    env=os.environ.copy()
    env.update({"OPENBLAS_NUM_THREADS":"1","OMP_NUM_THREADS":"1","PYTHONDONTWRITEBYTECODE":"1"})
    results=[]
    for name,relative in ENTRIES:
        start=time.monotonic()
        process=subprocess.run([sys.executable,"-B",str(HERE/relative),"--check"],
                               cwd=REPO,env=env,capture_output=True,timeout=120)
        out=logs/(name+".stdout.txt");err=logs/(name+".stderr.txt")
        out.write_bytes(process.stdout);err.write_bytes(process.stderr)
        results.append({
            "entry":name,"source":str((HERE/relative).relative_to(REPO)),
            "arguments":["--check"],"returncode":process.returncode,
            "duration_seconds":round(time.monotonic()-start,3),
            "stdout_path":str(out),"stderr_path":str(err),
            "stdout_sha256":sha(process.stdout),"stderr_sha256":sha(process.stderr),
        })
        print(("PASS" if process.returncode==0 else "FAIL")+": "+name,flush=True)
        if process.returncode:
            print(process.stdout.decode(errors="replace"),flush=True)
            print(process.stderr.decode(errors="replace"),flush=True)
    require(old_before==inherited_manifest(),"Old scientific inputs changed during execution")
    require(new_before==current_manifest(),"New source changed during execution")
    passed=all(r["returncode"]==0 for r in results)
    result={
        "schema":"ueot-response-verification/1",
        "timestamp_utc":datetime.now(timezone.utc).isoformat(),
        "git_head_at_execution":head,"working_tree_status_before_execution":status,
        "receipt_generated_before_commit_if_worktree_dirty":bool(status),
        "python":sys.version,"platform":platform.platform(),"dependencies":actual,
        "reused":reused,"executed_now":results,"current_source_manifest":new_before,
        "source_manifests_unchanged_after_execution":True,
        "old_scientific_entries_rerun":0,"new_mode_integrations":0,
        "scientific_exit":scientific_exit() if passed else {"status":"FAILED"},
        "status":"PASS" if passed else "FAIL",
    }
    output.write_text(json.dumps(result,indent=2,sort_keys=True,ensure_ascii=False)+"\n")
    print("Reused 18 previous entries with 76 unchanged scientific files; executed 4 new entries.")
    print("Receipt: "+str(output))
    return 0 if passed else 1

if __name__=="__main__":raise SystemExit(main())
