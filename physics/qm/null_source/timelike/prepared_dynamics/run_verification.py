"""Reuse 40 immutable predecessor results; execute the actual-history closure checks."""
from __future__ import annotations
import argparse
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime,timezone
import hashlib
from importlib.metadata import version
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[4]
BASE="d62c9ff9525ebf314f5aae5f674c38c9761de1fa"
PREFIX="physics/qm/null_source/timelike/"
PARENT=PREFIX+"prepared_initial/verification.json"
WORKFLOW=".github/workflows/ueot-physics-source-response.yml"
ROUTES=[WORKFLOW,"physics/qm/README.md","physics/qm/ROADMAP.md",PREFIX+"README.md"]
DIRECTORIES=["continuation","evolution","compatibility","response","instrument","identification",
             "stress_kernel","metric_response","operational_response","overlap_response","prepared_initial"]
RANGES=[PREFIX+d+"/" for d in DIRECTORIES]+[
    "physics/qm/null_source/FINITE_WINDOW.md","physics/qm/status/CURRENT.json",
    "formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/ScientificClosure/SISCFutureResponseCore.lean"]
VERSIONS={"numpy":"2.5.4","scipy":"1.18.1","sympy":"1.14.0","mpmath":"1.3.0"}
ENTRIES=[
    ("new_prepared_modes_257_512","generate_modes.py",["--check"]),
    ("phase_tail_terms_7_8","phase_extension.py",["--check"]),
    ("phase_tail_terms_0_6","phase_quadrature.py",["--check"]),
    ("uniform_all_mode_phase_remainder","phase_bounds.py",["--J","8","--radius","15933/67108864","--output","phase_bounds_uniform.json","--check"]),
    ("actual_history_parameter_sensitivity","phase_sensitivity.py",["--check"]),
    ("all_root_normal_derivative_obstruction","assemble.py",["--check"]),
    ("actual_AE_principal_inverse","principal.py",["--check"]),
    ("true_source_readout_statistics","source_readout.py",["--check"]),
    ("independent_phase_and_scope_review","review.py",["--check"])]

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
    require(len(old)==164,"Unexpected predecessor scientific inventory")
    manifest={}
    for rel in sorted(old):
        path=REPO/rel
        require(path.is_file() and not path.is_symlink(),"Nonregular scientific input")
        expected=sha(git("show",BASE+":"+rel))
        require(file_sha(path)==expected,"Inherited bytes changed: "+rel)
        manifest[rel]=expected
    return manifest

def previous_evidence(inherited):
    parent=json.loads((REPO/PARENT).read_text())
    require(parent["status"]=="PASS" and len(parent["executed_now"])==2
            and all(x["returncode"]==0 for x in parent["executed_now"]),"Parent did not pass")
    require(parent["reused"]["entry_count_reused"]==38,"Parent evidence count changed")
    routes={}
    covered=set()
    for rel,digest in parent["reused"]["inherited_scientific_manifest"].items():
        require(inherited.get(rel)==digest,"Parent inherited source mismatch: "+rel)
        covered.add(rel)
    for rel,digest in parent["current_source_manifest"].items():
        require(sha(git("show",BASE+":"+rel))==digest,"Parent executed source mismatch: "+rel)
        if rel in ROUTES:
            routes[rel]={"executed_predecessor_sha256":digest,
                         "current_sha256":file_sha(REPO/rel),
                         "role":"reading/workflow route; not a scientific input of predecessor checkers"}
        else:
            require(inherited.get(rel)==digest,"Parent scientific input changed: "+rel)
            covered.add(rel)
    covered.add(PARENT)
    require(covered==set(inherited) and set(routes)==set(ROUTES),"Incomplete predecessor source closure")
    ci=json.loads((HERE/"baseline_ci.json").read_text())
    run=ci["run"]
    require(run["id"]==44594485919 and run["head_sha"]==BASE and
            run["path"]==WORKFLOW and run["status"]=="completed"
            and run["conclusion"]=="success","Wrong exact-head baseline CI")
    job=next(j for j in ci["jobs"] if j["name"]=="reproduce")
    require(job["head_sha"]==BASE and job["conclusion"]=="success","Baseline job failed")
    step=next(s for s in job["steps"] if s["name"]=="Reuse 38 predecessor results and verify prepared initial-slice existence")
    require(step["conclusion"]=="success","Baseline science step failed")
    return {"base_commit":BASE,"entry_count_reused":40,
            "inherited_scientific_file_count":len(inherited),
            "inherited_scientific_manifest":inherited,
            "parent_receipt":{"path":PARENT,"sha256":inherited[PARENT],"count":2,
                "entries":[r["entry"] for r in parent["executed_now"]],
                "executed_again_this_run":False,
                "local_git_head_at_execution":parent["git_head_at_execution"]},
            "archived_earlier_local_receipts":parent["reused"]["archived_earlier_local_receipts"]+[parent["reused"]["parent_receipt"]],
            "exact_head_ci_proof_chain":parent["reused"]["exact_head_ci_proof_chain"]+[run],
            "audited_routing_changes":routes,"ci_observation_semantics":ci["semantics"]}

def current_manifest():
    paths=[p for p in HERE.rglob("*") if p.is_file() and p!=HERE/"verification.json"
           and "__pycache__" not in p.parts and p.suffix in {".py",".md",".json"}]
    paths.extend(REPO/rel for rel in ROUTES)
    return {str(p.relative_to(REPO)):file_sha(p) for p in sorted(set(paths))}

def main():
    require(__debug__ and sys.flags.optimize==0,"Assertions must stay enabled")
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output",type=Path,default=HERE/"verification.json")
    ap.add_argument("--logs",type=Path)
    args=ap.parse_args()
    output=args.output.resolve()
    logs=(args.logs or Path(tempfile.mkdtemp(prefix="ueot-prepared-dynamics-logs-"))).resolve()
    require(REPO not in logs.parents and logs!=REPO,"Logs must remain outside repository")
    require(output==HERE/"verification.json" or (REPO not in output.parents and output!=REPO),"Unexpected in-repo output")
    require(sys.version_info[:2]==(3,14),"Use Python 3.14")
    actual={name:version(name) for name in VERSIONS}
    require(actual==VERSIONS,"Scientific dependencies changed")
    logs.mkdir(parents=True,exist_ok=True)
    output.parent.mkdir(parents=True,exist_ok=True)
    inherited=inherited_manifest()
    reused=previous_evidence(inherited)
    sources=current_manifest()
    head=git("rev-parse","HEAD").decode().strip()
    status=git("status","--short").decode()
    env=os.environ.copy()
    env.update({"OPENBLAS_NUM_THREADS":"1","OMP_NUM_THREADS":"1","PYTHONDONTWRITEBYTECODE":"1"})
    def execute(entry):
        name,relative,arguments=entry
        print("RUN: "+name,flush=True)
        start=time.monotonic()
        process=subprocess.run([sys.executable,"-B",str(HERE/relative),*arguments],
                               cwd=REPO,env=env,capture_output=True,timeout=1800)
        stdout,stderr=logs/(name+".stdout.txt"),logs/(name+".stderr.txt")
        stdout.write_bytes(process.stdout);stderr.write_bytes(process.stderr)
        row={"entry":name,"source":str((HERE/relative).relative_to(REPO)),
             "arguments":arguments,"returncode":process.returncode,
             "duration_seconds":round(time.monotonic()-start,3),
             "stdout_path":str(stdout),"stderr_path":str(stderr),
             "stdout_sha256":sha(process.stdout),"stderr_sha256":sha(process.stderr)}
        print(("PASS" if process.returncode==0 else "FAIL")+": "+name,flush=True)
        if process.returncode:
            print(process.stdout.decode(errors="replace"),flush=True)
            print(process.stderr.decode(errors="replace"),flush=True)
        return row
    # All check modes are read-only and consume already generated receipts.
    # Two separate processes have independent numerical contexts and log files.
    with ThreadPoolExecutor(max_workers=2) as pool:
        rows=list(pool.map(execute,ENTRIES))
    require(inherited==inherited_manifest(),"Inherited sources changed during execution")
    require(sources==current_manifest(),"New sources changed during execution")
    passed=all(row["returncode"]==0 for row in rows)
    scientific=json.loads((HERE/"result.json").read_text())
    review=json.loads((HERE/"review.json").read_text())
    require(review["status"]=="PASS" and scientific["status"]=="PASS","Scientific receipt not passed")
    result={"schema":"ueot-prepared-dynamics-verification/1",
        "timestamp_utc":datetime.now(timezone.utc).isoformat(),
        "git_head_at_execution":head,"working_tree_status_before_execution":status,
        "receipt_generated_before_commit_if_worktree_dirty":bool(status),
        "python":sys.version,"dependencies":actual,
        "reused":reused,"executed_now":rows,"current_source_manifest":sources,
        "source_manifests_unchanged_after_execution":True,
        "old_scientific_entries_rerun":0,"new_mode_integrations":256,
        "new_geometry_ODE_integrations":0,"new_parameter_uniform_UV_computations":1,
        "new_phase_preserving_quadratures":2,"read_only_parallel_workers":2,
        "scientific_exit":{"all_root_Qpprime":scientific["Qpprime_all_roots"],
            "normal_spatial_residual_derivative":scientific["lambda5_normal_spatial_Einstein_residual"],
            "root_tightening":scientific["root_tightening"],"scope":scientific["scope"],
            "principal_inverse":json.loads((HERE/"principal.json").read_text())["windows"],
            "true_source_readout_gate":json.loads((HERE/"source_readout.json").read_text())["ideal_stress_risk_outward_gate"],
            "native_review_agents":3,"external_human_peer_review":False,
            "whole_unified_physics_goal":"OPEN"},
        "status":"PASS" if passed else "FAIL"}
    output.write_text(json.dumps(result,indent=2,sort_keys=True,ensure_ascii=False)+"\n")
    print("Reused 40 results with 164 unchanged scientific files; executed 9 new entries.")
    print("Receipt: "+str(output))
    return 0 if passed else 1
if __name__=="__main__":raise SystemExit(main())
