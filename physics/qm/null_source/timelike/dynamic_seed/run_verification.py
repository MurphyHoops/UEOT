"""Reuse 69 immutable results; verify five same-state dynamic/record certificates."""
from __future__ import annotations
import argparse
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime,timezone
import hashlib
from importlib.metadata import version
import json,os
from pathlib import Path
import subprocess,sys,tempfile,time
HERE=Path(__file__).resolve().parent
REPO=HERE.parents[4]
BASE="c8c9e7fa4963ac5fdbad38a8e398dabd6b6e78ea"
PREFIX="physics/qm/null_source/timelike/"
PARENT=PREFIX+"correlated_static/verification.json"
WORKFLOW=".github/workflows/ueot-physics-source-response.yml"
ROUTES=[WORKFLOW,"physics/qm/README.md","physics/qm/ROADMAP.md",PREFIX+"README.md"]
DIRECTORIES=["continuation","evolution","compatibility","response","instrument","identification",
             "stress_kernel","metric_response","operational_response","overlap_response",
             "prepared_initial","prepared_dynamics","compatible_evolution","physical_source","joint_history","correlated_static"]
RANGES=[PREFIX+d+"/" for d in DIRECTORIES]+[
    "physics/qm/null_source/FINITE_WINDOW.md","physics/qm/status/CURRENT.json",
    "formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/ScientificClosure/SISCFutureResponseCore.lean"]
VERSIONS={"numpy":"2.5.4","scipy":"1.18.1","sympy":"1.14.0","mpmath":"1.3.0"}
ENTRIES=[
    ("actual_KG_AE_second_jet","jet.py",["--check"]),
    ("infinite_response_root_and_second_order_bound","bounds.py",["--check"]),
    ("same_state_positive_window_and_normal_derivatives","window.py",["--check"]),
    ("complete_dynamic_records_and_clock","records.py",["--check"]),
    ("independent_conservation_constraint_scope_review","review.py",["--check"])]
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
    require(len(old)==254,"Unexpected predecessor scientific inventory: "+str(len(old)))
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
    require(parent["reused"]["entry_count_reused"]==67,"Parent evidence count changed")
    routes={};covered=set()
    for rel,digest in parent["reused"]["inherited_scientific_manifest"].items():
        require(inherited.get(rel)==digest,"Parent inherited source mismatch: "+rel);covered.add(rel)
    for rel,digest in parent["current_source_manifest"].items():
        require(sha(git("show",BASE+":"+rel))==digest,"Parent executed source mismatch: "+rel)
        if rel in ROUTES:
            routes[rel]={"executed_predecessor_sha256":digest,
                         "current_sha256":file_sha(REPO/rel),
                         "role":"reading/workflow route; not a scientific input of predecessor checkers"}
        else:
            require(inherited.get(rel)==digest,"Parent scientific input changed: "+rel);covered.add(rel)
    covered.add(PARENT)
    require(covered==set(inherited) and set(routes)==set(ROUTES),"Incomplete predecessor source closure")
    ci=json.loads((HERE/"baseline_ci.json").read_text());run=ci["run"]
    require(run["id"]==44673273555 and run["head_sha"]==BASE and run["path"]==WORKFLOW
            and run["status"]=="completed" and run["conclusion"]=="success","Wrong exact-head baseline CI")
    job=next(j for j in ci["jobs"] if j["name"]=="reproduce")
    require(job["head_sha"]==BASE and job["conclusion"]=="success","Baseline job failed")
    step=next(s for s in job["steps"] if s["name"]=="Reuse 67 predecessor results and verify correlated quantum-state residual bounds")
    require(step["conclusion"]=="success","Baseline science step failed")
    return {"base_commit":BASE,"entry_count_reused":69,
            "inherited_scientific_file_count":len(inherited),"inherited_scientific_manifest":inherited,
            "parent_receipt":{"path":PARENT,"sha256":inherited[PARENT],"count":2,
                "entries":[r["entry"] for r in parent["executed_now"]],"executed_again_this_run":False,
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
    args=ap.parse_args();output=args.output.resolve()
    logs=(args.logs or Path(tempfile.mkdtemp(prefix="ueot-dynamic-seed-logs-"))).resolve()
    require(REPO not in logs.parents and logs!=REPO,"Logs must remain outside repository")
    require(output==HERE/"verification.json" or (REPO not in output.parents and output!=REPO),"Unexpected in-repo output")
    require(sys.version_info[:2]==(3,14),"Use Python 3.14")
    actual={name:version(name) for name in VERSIONS}
    require(actual==VERSIONS,"Scientific dependencies changed")
    logs.mkdir(parents=True,exist_ok=True);output.parent.mkdir(parents=True,exist_ok=True)
    inherited=inherited_manifest();reused=previous_evidence(inherited);sources=current_manifest()
    head=git("rev-parse","HEAD").decode().strip();status=git("status","--short").decode()
    env=os.environ.copy()
    env.update({"OPENBLAS_NUM_THREADS":"1","OMP_NUM_THREADS":"1","PYTHONDONTWRITEBYTECODE":"1"})
    def execute(entry):
        name,relative,arguments=entry
        print("RUN: "+name,flush=True);start=time.monotonic()
        process=subprocess.run([sys.executable,"-B",str(HERE/relative),*arguments],
                               cwd=REPO,env=env,capture_output=True,timeout=180)
        stdout,stderr=logs/(name+".stdout.txt"),logs/(name+".stderr.txt")
        stdout.write_bytes(process.stdout);stderr.write_bytes(process.stderr)
        row={"entry":name,"source":str((HERE/relative).relative_to(REPO)),"arguments":arguments,
             "returncode":process.returncode,"duration_seconds":round(time.monotonic()-start,3),
             "stdout_path":str(stdout),"stderr_path":str(stderr),
             "stdout_sha256":sha(process.stdout),"stderr_sha256":sha(process.stderr)}
        print(("PASS" if process.returncode==0 else "FAIL")+": "+name,flush=True)
        if process.returncode:
            print(process.stdout.decode(errors="replace"),flush=True)
            print(process.stderr.decode(errors="replace"),flush=True)
        return row
    with ThreadPoolExecutor(max_workers=2) as pool:rows=list(pool.map(execute,ENTRIES))
    require(inherited==inherited_manifest(),"Inherited sources changed during execution")
    require(sources==current_manifest(),"New sources changed during execution")
    passed=all(row["returncode"]==0 for row in rows)
    science={name:json.loads((HERE/(name+".json")).read_text())
             for name in ["jet","bounds","window","records","review"]}
    require(all(d["status"]=="PASS" for d in science.values()),"Scientific receipt not passed")
    result={"schema":"ueot-dynamic-seed-verification/1",
        "timestamp_utc":datetime.now(timezone.utc).isoformat(),"git_head_at_execution":head,
        "working_tree_status_before_execution":status,"receipt_generated_before_commit_if_worktree_dirty":bool(status),
        "python":sys.version,"dependencies":actual,"reused":reused,"executed_now":rows,
        "current_source_manifest":sources,"source_manifests_unchanged_after_execution":True,
        "old_scientific_entries_rerun":0,"new_mode_ODE_integrations":0,"new_geometry_ODE_integrations":0,
        "new_interval_and_symbolic_certificates":5,"read_only_parallel_workers":2,
        "scientific_exit":{
            "exact_state_KG_AE_second_jet":science["jet"]["second_order_KG_and_Wronskian_coefficients_exact"],
            "growth_root_unique":science["bounds"]["positive_root_unique_in_1_3"],
            "second_order_beta":science["bounds"]["beta"],
            "same_state_positive_window":science["window"]["conformal_time_window"],
            "normal_density_defect_x_bound":science["window"]["x_times_orthonormal_density_defect_upper"],
            "normal_pressure_defect_x_bound":science["window"]["x_times_orthonormal_pressure_defect_upper"],
            "full_AE_conservation_exact":science["review"]["full_AE_local_and_subtraction_conservation_exact"],
            "dynamic_record_equivalence":"Conditional full-joint O(2) theorem, RECORDS.md",
            "ensemble_counterexample_TV":science["records"]["total_variation_distance"],
            "native_review_agents":3,"external_human_peer_review":False,
            "nearby_exact_nonlinear_SCE_solution":"OPEN",
            "full_fluctuating_constraint_and_local_gravity_instrument":"OPEN",
            "whole_unified_physics_goal":"OPEN"},
        "status":"PASS" if passed else "FAIL"}
    output.write_text(json.dumps(result,indent=2,sort_keys=True,ensure_ascii=False)+"\n")
    print("Reused 69 results with 254 unchanged scientific files; executed 5 new entries.")
    print("Receipt: "+str(output))
    return 0 if passed else 1
if __name__=="__main__":raise SystemExit(main())
