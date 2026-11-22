"""Run four overlapping-response checks and reuse 34 unchanged predecessor results."""
from __future__ import annotations
import argparse
from datetime import datetime,timezone
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
BASE="c57e2f411e58dc1dae60de8f3c97fbd680e46d8b"
WORKFLOW=".github/workflows/ueot-physics-source-response.yml"
PREFIX="physics/qm/null_source/timelike/"
RANGES=[PREFIX+d+"/" for d in ["continuation","evolution","compatibility","response","instrument","identification","stress_kernel","metric_response","operational_response"]]+[
 "physics/qm/null_source/FINITE_WINDOW.md","physics/qm/status/CURRENT.json",
 "formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/ScientificClosure/SISCFutureResponseCore.lean"]
ROUTES=[WORKFLOW,"physics/qm/README.md","physics/qm/ROADMAP.md",PREFIX+"README.md"]
VERSIONS={"numpy":"2.5.4","scipy":"1.18.1","sympy":"1.14.0","mpmath":"1.3.0"}
ENTRIES=[
 ("complete_local_curvature_TT_operator","local/check.py"),
 ("causal_logarithmic_quantum_response_contract","quantum/check.py"),
 ("all_mode_local_retarded_resolvent","resolvent/check.py"),
 ("independent_four_dimensional_overlap_review","review.py"),
]

def sha(data):return hashlib.sha256(data).hexdigest()
def file_sha(path):return sha(path.read_bytes())
def git(*args):return subprocess.check_output(["git",*args],cwd=REPO)
def require(value,message):
    if not value:raise RuntimeError(message)
def names(*args):return {p.decode() for p in git(*args).split(b"\0") if p}

def inherited_manifest():
    previous=names("ls-tree","-rz","--name-only",BASE,"--",*RANGES)
    current=names("ls-files","-z","--cached","--others","--exclude-standard","--",*RANGES)
    require(previous==current,"Inherited file inventory changed: "+repr(sorted(previous^current)))
    require(len(previous)==140,"Unexpected inherited scientific inventory size")
    result={}
    for rel in sorted(previous):
        p=REPO/rel
        require(p.is_file() and not p.is_symlink(),"Nonregular inherited file: "+rel)
        expected=sha(git("show",BASE+":"+rel));actual=file_sha(p)
        require(expected==actual,"Inherited scientific bytes changed: "+rel)
        result[rel]=actual
    return result

def current_manifest():
    paths=[p for p in HERE.rglob("*") if p.is_file() and "__pycache__" not in p.parts
           and p!=HERE/"verification.json" and p.suffix in {".py",".md",".json"}]
    paths += [REPO/p for p in ROUTES]
    return {str(p.relative_to(REPO)):file_sha(p) for p in sorted(set(paths))}

def predecessor_evidence(inherited):
    parent_path=PREFIX+"operational_response/verification.json"
    parent=json.loads((REPO/parent_path).read_text())
    rows=parent["executed_now"]
    require(parent["status"]=="PASS" and len(rows)==4 and
            all(r["returncode"]==0 for r in rows),"Immediate predecessor did not pass")
    require(parent["new_mode_integrations"]==0 and
            parent["old_scientific_entries_rerun"]==0,"Unexpected predecessor execution identity")
    routes={}
    def consume(manifest,allow_routes=False):
        for rel,expected in manifest.items():
            require(sha(git("show",BASE+":"+rel))==expected,"Parent receipt source mismatch: "+rel)
            if rel in inherited:
                require(inherited[rel]==expected,"Inherited input changed: "+rel)
            else:
                require(allow_routes and rel in ROUTES,"Unfrozen transitive input: "+rel)
                routes[rel]={"previous_receipt_sha256":expected,"current_sha256":file_sha(REPO/rel),
                    "role":"reading/workflow route, not consumed by predecessor scientific checkers",
                    "current_bytes_frozen_in_this_manifest":True}
    consume(parent["current_source_manifest"],True)
    require(set(routes)==set(ROUTES),"Expected four explicitly audited routing changes")
    old=parent["reused"]
    require(old["entry_count_reused"]==30 and old["inherited_scientific_file_count"]==124,
            "Parent reuse count changed")
    consume(old["inherited_scientific_manifest"])
    receipts=old["archived_earlier_local_receipts"]+[old["parent_receipt"]]
    require([r["count"] for r in receipts]==[5,9,4,4,4,4],"Predecessor proof chain counts changed")
    for receipt in receipts:
        require(inherited[receipt["path"]]==receipt["sha256"],"Archived proof receipt changed")
    ci=json.loads((HERE/"baseline_ci.json").read_text());run=ci["run"]
    require(run["id"]==44568965734 and run["head_sha"]==BASE and
            run["path"]==WORKFLOW and run["status"]=="completed" and run["conclusion"]=="success",
            "Exact-head predecessor CI is not passed")
    require(run["html_url"]=="https://github.com/MurphyHoops/UEOT/actions/runs/44568965734",
            "Unexpected CI identity")
    job=next(j for j in ci["jobs"] if j["name"]=="reproduce")
    require(job["head_sha"]==BASE and job["status"]=="completed" and job["conclusion"]=="success",
            "Predecessor CI job did not pass")
    step=next(s for s in job["steps"] if s["name"]=="Reuse 30 predecessor results and verify four operational-response results")
    require(step["status"]=="completed" and step["conclusion"]=="success","Predecessor check step failed")
    return {
        "base_commit":BASE,"inherited_scientific_file_count":len(inherited),
        "inherited_scientific_manifest":inherited,"entry_count_reused":34,
        "parent_receipt":{"path":parent_path,"sha256":inherited[parent_path],
            "entries":[r["entry"] for r in rows],"count":4,"executed_again_this_run":False,
            "local_git_head_at_execution":parent["git_head_at_execution"]},
        "archived_earlier_local_receipts":receipts,
        "exact_head_ci_proof_chain":old["exact_head_ci_proof_chain"]+[run],
        "ci_observation_semantics":ci["semantics"],"audited_routing_changes":routes,
        "old_workflow_at_base_sha256":sha(git("show",BASE+":"+WORKFLOW)),
    }

def scientific_exit():
    review=json.loads((HERE/"review.json").read_text())
    require(review["status"]=="PASS" and review["new_mode_integrations"]==0,"Invalid primary review")
    prescription=review["physical_prescription"]
    require([prescription[k] for k in ["physical_mu","alpha_AE","Einstein_z","b_extra","c_extra"]]
            ==[1,0,1,0,0],"Frozen physical prescription changed")
    require(not prescription["extra_couplings_reopened"] and
            not prescription["reference_contacts_assumed_zero"],"Finite terms conflated with reference contacts")
    geometry=review["local_geometry"];quantum=review["quantum_overlap"]
    require(geometry["full_closed_FLRW_Weyl_operator"] and geometry["mixed_R2_operator"],
            "Local geometric certificate incomplete")
    require(quantum["causal_log_finite_part_defined"] and
            quantum["scalar_log_normal_form_exact_causal_inverse"] and
            quantum["same_background_state_difference_Volterra_theorem"],"Quantum overlap increment incomplete")
    require(not quantum["scalar_log_inverse_stable"] and
            not quantum["actual_state_difference_M8_certified"],"Quantum scope improperly upgraded")
    require(review["scope"]["full_quantum_feedback_resolvent"] is False and
            review["scope"]["full_nonlinear_SCE_solution"] is False,"Scientific scope improperly upgraded")
    return {
        "physical_prescription":prescription,"local_geometry":geometry,
        "quantum_overlap":quantum,"explicit_local_family":review["explicit_local_family"],
        "independent_review":review["independent_geometry"],
        "component_receipts":{directory:{"path":str((HERE/directory/"result.json").relative_to(REPO)),
            "sha256":file_sha(HERE/directory/"result.json")} for directory in ["local","quantum","resolvent"]},
        "fixed_reference_complete_TT_polarization_and_contacts":"OPEN",
        "actual_curved_prepared_state_remainder_norm":"OPEN",
        "full_quantum_feedback_and_nonlinear_SCE":"OPEN",
        "physical_device_and_driver_realization":"OPEN",
        "Core_unique_physical_selection":"OPEN",
        "new_Lean_proofs":False,"new_matching_hardware_data":False,
        "whole_unified_physics_goal":"OPEN",
    }

def main():
    require(__debug__ and sys.flags.optimize==0,"Scientific assertions must remain enabled")
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output",type=Path,default=HERE/"verification.json")
    ap.add_argument("--logs",type=Path)
    args=ap.parse_args();output=args.output.resolve()
    logs=(args.logs or Path(tempfile.mkdtemp(prefix="ueot-overlap-response-logs-"))).resolve()
    require(REPO not in logs.parents and logs!=REPO,"Logs must stay outside repository")
    require(output==HERE/"verification.json" or (REPO not in output.parents and output!=REPO),
            "Only default verification.json may be written in the repository")
    require(sys.version_info[:2]==(3,14),"Use Python 3.14")
    actual={k:version(k) for k in VERSIONS}
    require(actual==VERSIONS,"Dependency versions changed")
    logs.mkdir(parents=True,exist_ok=True);output.parent.mkdir(parents=True,exist_ok=True)
    inherited=inherited_manifest();reused=predecessor_evidence(inherited)
    sources=current_manifest()
    head=git("rev-parse","HEAD").decode().strip();status=git("status","--short").decode()
    env=os.environ.copy()
    env.update({"OPENBLAS_NUM_THREADS":"1","OMP_NUM_THREADS":"1","PYTHONDONTWRITEBYTECODE":"1"})
    entries=[]
    for name,relative in ENTRIES:
        start=time.monotonic()
        process=subprocess.run([sys.executable,"-B",str(HERE/relative),"--check"],
            cwd=REPO,env=env,capture_output=True,timeout=120)
        out=logs/(name+".stdout.txt");err=logs/(name+".stderr.txt")
        out.write_bytes(process.stdout);err.write_bytes(process.stderr)
        entries.append({"entry":name,"source":str((HERE/relative).relative_to(REPO)),
            "arguments":["--check"],"returncode":process.returncode,
            "duration_seconds":round(time.monotonic()-start,3),
            "stdout_path":str(out),"stderr_path":str(err),
            "stdout_sha256":sha(process.stdout),"stderr_sha256":sha(process.stderr)})
        print(("PASS" if process.returncode==0 else "FAIL")+": "+name,flush=True)
        if process.returncode:
            print(process.stdout.decode(errors="replace"),flush=True)
            print(process.stderr.decode(errors="replace"),flush=True)
    require(inherited==inherited_manifest(),"Inherited inputs changed during execution")
    require(sources==current_manifest(),"Current sources changed during execution")
    passed=all(r["returncode"]==0 for r in entries)
    result={
        "schema":"ueot-overlap-response-verification/1",
        "timestamp_utc":datetime.now(timezone.utc).isoformat(),
        "git_head_at_execution":head,"working_tree_status_before_execution":status,
        "receipt_generated_before_commit_if_worktree_dirty":bool(status),
        "python":sys.version,"platform":platform.platform(),"dependencies":actual,
        "reused":reused,"executed_now":entries,"current_source_manifest":sources,
        "source_manifests_unchanged_after_execution":True,
        "old_scientific_entries_rerun":0,"new_mode_integrations":0,"new_geometry_ODE_integrations":0,
        "scientific_exit":scientific_exit() if passed else {"status":"FAILED"},
        "status":"PASS" if passed else "FAIL",
    }
    output.write_text(json.dumps(result,indent=2,sort_keys=True,ensure_ascii=False)+"\n")
    print("Reused 34 results with 140 unchanged scientific files; executed 4 new entries.")
    print("Receipt: "+str(output))
    return 0 if passed else 1

if __name__=="__main__":raise SystemExit(main())
