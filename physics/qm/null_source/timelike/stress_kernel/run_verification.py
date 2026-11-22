"""Run four stress-kernel checks and reuse 22 unchanged predecessor results."""
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
BASE="29d49e3eee6299e2085492b0e061288b8166b5fa"
WORKFLOW=".github/workflows/ueot-physics-source-response.yml"
PREFIX="physics/qm/null_source/timelike/"
RANGES=[PREFIX+d+"/" for d in ["continuation","evolution","compatibility","response","instrument","identification"]]+[
 "physics/qm/null_source/FINITE_WINDOW.md","physics/qm/status/CURRENT.json",
 "formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/ScientificClosure/SISCFutureResponseCore.lean"]
ROUTES=[WORKFLOW,"physics/qm/README.md","physics/qm/ROADMAP.md",PREFIX+"README.md"]
VERSIONS={"numpy":"2.5.4","scipy":"1.18.1","sympy":"1.14.0","mpmath":"1.3.0"}
ENTRIES=[
 ("complete_quadratic_stress_noise","noise/check.py"),
 ("retarded_response_and_lapse_records","response/check.py"),
 ("legal_smeared_geometry_and_constraints","geometry/check.py"),
 ("independent_common_scale_integration","review.py"),
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
    require(len(previous)==92,"Unexpected inherited scientific inventory size")
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
    parent_path=PREFIX+"response/verification.json"
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
    require(old["entry_count_reused"]==18 and old["inherited_scientific_file_count"]==76,
            "Parent reuse count changed")
    consume(old["inherited_scientific_manifest"])
    receipts=old["archived_local_receipts"]
    require([r["count"] for r in receipts]==[5,9,4],"Predecessor proof chain counts changed")
    for receipt in receipts:
        require(inherited[receipt["path"]]==receipt["sha256"],"Archived proof receipt changed")
    ci=json.loads((HERE/"baseline_ci.json").read_text());run=ci["run"]
    require(run["id"]==44511966040 and run["head_sha"]==BASE and
            run["path"]==WORKFLOW and run["status"]=="completed" and run["conclusion"]=="success",
            "Exact-head predecessor CI is not passed")
    require(run["html_url"]=="https://github.com/MurphyHoops/UEOT/actions/runs/44511966040",
            "Unexpected CI identity")
    job=next(j for j in ci["jobs"] if j["name"]=="reproduce")
    require(job["head_sha"]==BASE and job["status"]=="completed" and job["conclusion"]=="success",
            "Predecessor CI job did not pass")
    step=next(s for s in job["steps"] if s["name"]=="Reuse 18 predecessor results and verify four response results")
    require(step["status"]=="completed" and step["conclusion"]=="success","Predecessor check step failed")
    return {
        "base_commit":BASE,"inherited_scientific_file_count":len(inherited),
        "inherited_scientific_manifest":inherited,"entry_count_reused":22,
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
    noise=json.loads((HERE/"noise/result.json").read_text())
    row=review["same_scale"]
    require(review["new_mode_integrations"]==0,"Unexpected integration")
    require(row["lambda"]==noise["certificate"]["lambda_certified"],"Scale identities differ")
    require(Fraction(row["relative_total_stress_variance_upper"][1])<Fraction(1,100),
            "Complete relative noise gate did not pass")
    require(row["independent_fresh_starts"]==128 and
            Fraction(row["per_candidate_classification_error_upper"])<Fraction(1,100000),
            "Same-scale conditional record gate failed")
    require(row["finite_epsilon_probability_bound_proved"] is False and
            row["full_nonlinear_SCE_solution_or_distance_certified"] is False,
            "Scientific scope was improperly upgraded")
    return {
        "same_scale":row,
        "canonical_algebra_review":review["canonical_algebra"],
        "component_receipts":{directory:{"path":str((HERE/directory/"result.json").relative_to(REPO)),
            "sha256":file_sha(HERE/directory/"result.json")} for directory in ["noise","response","geometry"]},
        "complete_quadratic_noise_numerical_bound":"CERTIFIED_FOR_DECLARED_TEST",
        "mean_response_equivalence":"CERTIFIED_IN_COMMON_ADMISSIBLE_METRIC_CLASS",
        "lapse_probe_response":"FIRST_DERIVATIVE_AT_ZERO",
        "compact_adjoint_geometry_tests":"CLASSIFIED_FOR_DECLARED_LINEAR_OPERATOR",
        "full_nonlinear_SCE_and_stability":"OPEN",
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
    logs=(args.logs or Path(tempfile.mkdtemp(prefix="ueot-stress-kernel-logs-"))).resolve()
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
        "schema":"ueot-stress-kernel-verification/1",
        "timestamp_utc":datetime.now(timezone.utc).isoformat(),
        "git_head_at_execution":head,"working_tree_status_before_execution":status,
        "receipt_generated_before_commit_if_worktree_dirty":bool(status),
        "python":sys.version,"platform":platform.platform(),"dependencies":actual,
        "reused":reused,"executed_now":entries,"current_source_manifest":sources,
        "source_manifests_unchanged_after_execution":True,
        "old_scientific_entries_rerun":0,"new_mode_integrations":0,
        "scientific_exit":scientific_exit() if passed else {"status":"FAILED"},
        "status":"PASS" if passed else "FAIL",
    }
    output.write_text(json.dumps(result,indent=2,sort_keys=True,ensure_ascii=False)+"\n")
    print("Reused 22 results with 92 unchanged scientific files; executed 4 new entries.")
    print("Receipt: "+str(output))
    return 0 if passed else 1

if __name__=="__main__":raise SystemExit(main())
