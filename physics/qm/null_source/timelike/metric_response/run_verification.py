"""Run four metric-response checks and reuse 26 unchanged predecessor results."""
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
BASE="719babd3386b9d9274d5c91dd0b8ad5e71688049"
WORKFLOW=".github/workflows/ueot-physics-source-response.yml"
PREFIX="physics/qm/null_source/timelike/"
RANGES=[PREFIX+d+"/" for d in ["continuation","evolution","compatibility","response","instrument","identification","stress_kernel"]]+[
 "physics/qm/null_source/FINITE_WINDOW.md","physics/qm/status/CURRENT.json",
 "formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/ScientificClosure/SISCFutureResponseCore.lean"]
ROUTES=[WORKFLOW,"physics/qm/README.md","physics/qm/ROADMAP.md",PREFIX+"README.md"]
VERSIONS={"numpy":"2.5.4","scipy":"1.18.1","sympy":"1.14.0","mpmath":"1.3.0"}
ENTRIES=[
 ("finite_lapse_Weyl_record_bound","finite/check.py"),
 ("compact_local_TT_noise_and_geometry","tensor/check.py"),
 ("finite_proper_clock_classical_benchmark","clock/check.py"),
 ("independent_metric_response_and_64_start_review","review.py"),
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
    require(len(previous)==108,"Unexpected inherited scientific inventory size")
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
    parent_path=PREFIX+"stress_kernel/verification.json"
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
    require(old["entry_count_reused"]==22 and old["inherited_scientific_file_count"]==92,
            "Parent reuse count changed")
    consume(old["inherited_scientific_manifest"])
    receipts=old["archived_earlier_local_receipts"]+[old["parent_receipt"]]
    require([r["count"] for r in receipts]==[5,9,4,4],"Predecessor proof chain counts changed")
    for receipt in receipts:
        require(inherited[receipt["path"]]==receipt["sha256"],"Archived proof receipt changed")
    ci=json.loads((HERE/"baseline_ci.json").read_text());run=ci["run"]
    require(run["id"]==44543549093 and run["head_sha"]==BASE and
            run["path"]==WORKFLOW and run["status"]=="completed" and run["conclusion"]=="success",
            "Exact-head predecessor CI is not passed")
    require(run["html_url"]=="https://github.com/MurphyHoops/UEOT/actions/runs/44543549093",
            "Unexpected CI identity")
    job=next(j for j in ci["jobs"] if j["name"]=="reproduce")
    require(job["head_sha"]==BASE and job["status"]=="completed" and job["conclusion"]=="success",
            "Predecessor CI job did not pass")
    step=next(s for s in job["steps"] if s["name"]=="Reuse 22 predecessor results and verify four stress-kernel results")
    require(step["status"]=="completed" and step["conclusion"]=="success","Predecessor check step failed")
    return {
        "base_commit":BASE,"inherited_scientific_file_count":len(inherited),
        "inherited_scientific_manifest":inherited,"entry_count_reused":26,
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
    require(review["status"]=="PASS" and review["new_mode_integrations"]==0,"Invalid review")
    records=review["conditional_records"]
    require(records["fixed_number_of_all_starts"]==64,"Wrong record horizon")
    require(Fraction(records["old_error_upper"])<Fraction(1,100000) and
            Fraction(records["new_error_upper"])<Fraction(1,100000),"Record risk gate failed")
    require(review["finite_metric"]["finite_abs_epsilon_le_one_probability_bound"] is True,
            "Finite response theorem did not pass")
    require(review["scope"]["full_nonlinear_SCE_solution"] is False and
            review["scope"]["full_quantum_metric_response"] is False,
            "Scientific scope was improperly upgraded")
    return {
        "finite_metric":review["finite_metric"],
        "local_tensor":review["local_tensor"],
        "proper_clock":review["proper_clock"],
        "conditional_records":records,
        "component_receipts":{directory:{"path":str((HERE/directory/"result.json").relative_to(REPO)),
            "sha256":file_sha(HERE/directory/"result.json")} for directory in ["finite","tensor","clock"]},
        "finite_lapse_probe_response":"CERTIFIED_FOR_ABS_EPSILON_LE_ONE_AND_DECLARED_FUTURE_WEYL_TEST",
        "local_TT_forced_classical_metric":"COMPACT_GAUGE_INVARIANT_TEST_AND_ALL_MODE_QUADRATIC_NOISE",
        "proper_clock_nonlinear_benchmark":"EXACT_CLASSICAL_BRANCH_FAMILY_WITH_CALIBRATED_CLOCK",
        "full_nonlinear_SCE_and_stability":"OPEN",
        "full_quantum_metric_response":"OPEN",
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
    logs=(args.logs or Path(tempfile.mkdtemp(prefix="ueot-metric-response-logs-"))).resolve()
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
        "schema":"ueot-metric-response-verification/1",
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
    print("Reused 26 results with 108 unchanged scientific files; executed 4 new entries.")
    print("Receipt: "+str(output))
    return 0 if passed else 1

if __name__=="__main__":raise SystemExit(main())
