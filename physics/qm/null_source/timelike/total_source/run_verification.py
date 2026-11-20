"""Reuse 121 frozen results; verify sixteen new total-source certificates."""
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
BASE="0518a8c4e7986490afdeea1d49f57279da019b7f"
PREFIX="physics/qm/null_source/timelike/"
PARENT=PREFIX+"finite_local/verification.json"
WORKFLOW=".github/workflows/ueot-physics-source-response.yml"
ROUTES=[WORKFLOW,"physics/qm/README.md","physics/qm/ROADMAP.md",PREFIX+"README.md"]
DIRECTORIES=["continuation","evolution","compatibility","response","instrument","identification",
 "stress_kernel","metric_response","operational_response","overlap_response",
 "prepared_initial","prepared_dynamics","compatible_evolution","physical_source","joint_history",
 "correlated_static","dynamic_seed","dynamic_inverse","nonlinear_history","operational_selection","finite_local"]
RANGES=[PREFIX+d+"/" for d in DIRECTORIES]+[
 "physics/qm/null_source/FINITE_WINDOW.md","physics/qm/status/CURRENT.json",
 "formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/ScientificClosure/SISCFutureResponseCore.lean"]
VERSIONS={"numpy":"2.5.4","scipy":"1.18.1","sympy":"1.14.0","mpmath":"1.3.0"}
ENTRIES=["rotation","fieldspace","autonomous","constraints","coherence","pressure_noise",
 "influence","history_witness","preparation","total_future","discrimination","response",
 "initial_correlations","carrier","preparation_causality","review"]
assert len(ENTRIES)==16
def sha(data):return hashlib.sha256(data).hexdigest()
def file_sha(path):return sha(path.read_bytes())
def git(*args):return subprocess.check_output(["git",*args],cwd=REPO)
def require(value,message):
    if not value:raise RuntimeError(message)
def names(*args):return {p.decode() for p in git(*args).split(b"\0") if p}
def inherited_manifest():
    old=names("ls-tree","-rz","--name-only",BASE,"--",*RANGES)
    current=names("ls-files","-z","--cached","--others","--exclude-standard","--",*RANGES)
    require(old==current,"Frozen inventory changed: "+repr(sorted(old^current)))
    require(len(old)==438,"Unexpected frozen inventory: "+str(len(old)))
    manifest={}
    for rel in sorted(old):
        p=REPO/rel
        require(p.is_file() and not p.is_symlink(),"Nonregular frozen input: "+rel)
        expected=sha(git("show",BASE+":"+rel))
        require(file_sha(p)==expected,"Frozen bytes changed: "+rel)
        manifest[rel]=expected
    return manifest
def previous_evidence(inherited):
    parent=json.loads((REPO/PARENT).read_text())
    require(parent["status"]=="PASS" and len(parent["executed_now"])==30
        and all(x["returncode"]==0 for x in parent["executed_now"]),"Parent did not pass")
    require(parent["reused"]["entry_count_reused"]==91,"Wrong inherited result count")
    covered=set();routes={}
    for rel,digest in parent["reused"]["inherited_scientific_manifest"].items():
        require(inherited.get(rel)==digest,"Parent frozen hash mismatch: "+rel);covered.add(rel)
    for rel,digest in parent["current_source_manifest"].items():
        require(sha(git("show",BASE+":"+rel))==digest,"Parent executed source mismatch: "+rel)
        if rel in ROUTES:
            routes[rel]={"executed_predecessor_sha256":digest,"current_sha256":file_sha(REPO/rel),
                "role":"reading/workflow route; not predecessor scientific input"}
        else:
            require(inherited.get(rel)==digest,"Parent input changed: "+rel);covered.add(rel)
    covered.add(PARENT)
    require(covered==set(inherited) and set(routes)==set(ROUTES),"Incomplete predecessor source closure")
    ci=json.loads((HERE/"baseline_ci.json").read_text());run=ci["run"]
    require(run["id"]==44768510217 and run["head_sha"]==BASE and run["path"]==WORKFLOW
        and run["status"]=="completed" and run["conclusion"]=="success","Wrong exact-head baseline CI")
    job=next(j for j in ci["jobs"] if j["name"]=="reproduce")
    require(job["id"]==136399544853 and job["run_id"]==run["id"]
        and job["conclusion"]=="success","Baseline job failed")
    step=next(s for s in job["steps"] if s["name"]=="Reuse 91 predecessor results and verify 30 actual-state and preparation certificates")
    require(step["conclusion"]=="success" and ci["decoded_job_log_observed"]
        and ci["decoded_PASS_count"]==30,"Baseline science step/log failed")
    artifact=next(a for a in ci["artifacts"] if a["id"]==14644014724)
    require(artifact["workflow_run"]["head_sha"]==BASE and not artifact["expired"]
        and artifact["digest"]=="sha256:0e33542ecdf6a30d1341e30b54c53c28977be09f3579b7b85954e6d401f643eb",
        "Wrong baseline artifact")
    return {"base_commit":BASE,"entry_count_reused":121,
      "inherited_scientific_file_count":len(inherited),"inherited_scientific_manifest":inherited,
      "parent_receipt":{"path":PARENT,"sha256":inherited[PARENT],"count":30,
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
    require(__debug__ and sys.flags.optimize==0,"Assertions must remain enabled")
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output",type=Path,default=HERE/"verification.json")
    ap.add_argument("--logs",type=Path)
    args=ap.parse_args();output=args.output.resolve()
    logs=(args.logs or Path(tempfile.mkdtemp(prefix="ueot-total-source-logs-"))).resolve()
    require(REPO not in logs.parents and logs!=REPO,"Logs must remain outside repository")
    require(output==HERE/"verification.json" or (REPO not in output.parents and output!=REPO),"Unexpected output")
    require(sys.version_info[:2]==(3,14),"Use Python 3.14")
    actual={n:version(n) for n in VERSIONS}
    require(actual==VERSIONS,"Scientific dependency versions changed")
    logs.mkdir(parents=True,exist_ok=True);output.parent.mkdir(parents=True,exist_ok=True)
    inherited=inherited_manifest();reused=previous_evidence(inherited);sources=current_manifest()
    head=git("rev-parse","HEAD").decode().strip();status=git("status","--short").decode()
    env=os.environ.copy();env.update(OPENBLAS_NUM_THREADS="1",OMP_NUM_THREADS="1",PYTHONDONTWRITEBYTECODE="1")
    def execute(name):
        print("RUN: "+name,flush=True);start=time.monotonic()
        proc=subprocess.run([sys.executable,"-B",str(HERE/(name+".py")),"--check"],
             cwd=REPO,env=env,capture_output=True,timeout=180)
        out,err=logs/(name+".stdout.txt"),logs/(name+".stderr.txt")
        out.write_bytes(proc.stdout);err.write_bytes(proc.stderr)
        row={"entry":name,"source":str((HERE/(name+".py")).relative_to(REPO)),
          "arguments":["--check"],"returncode":proc.returncode,"duration_seconds":round(time.monotonic()-start,3),
          "stdout_path":str(out),"stderr_path":str(err),
          "stdout_sha256":sha(proc.stdout),"stderr_sha256":sha(proc.stderr)}
        print(("PASS" if proc.returncode==0 else "FAIL")+": "+name,flush=True)
        if proc.returncode:
            print(proc.stdout.decode(errors="replace"),flush=True)
            print(proc.stderr.decode(errors="replace"),flush=True)
        return row
    with ThreadPoolExecutor(max_workers=2) as pool:rows=list(pool.map(execute,ENTRIES))
    require(inherited==inherited_manifest(),"Frozen sources changed during execution")
    require(sources==current_manifest(),"New sources changed during execution")
    passed=all(r["returncode"]==0 for r in rows)
    science={n:json.loads((HERE/(n+".json")).read_text()) for n in ENTRIES}
    require(all(d["status"]=="PASS" for d in science.values()),"Scientific receipt not passed")
    result={"schema":"ueot-total-source-verification/1",
      "timestamp_utc":datetime.now(timezone.utc).isoformat(),"git_head_at_execution":head,
      "working_tree_status_before_execution":status,"receipt_generated_before_commit_if_worktree_dirty":bool(status),
      "python":sys.version,"dependencies":actual,"reused":reused,"executed_now":rows,
      "current_source_manifest":sources,"source_manifests_unchanged_after_execution":True,
      "old_scientific_entries_rerun":0,"new_mode_ODE_integrations":0,"new_geometry_ODE_integrations":0,
      "new_interval_and_symbolic_certificates":len(ENTRIES),"read_only_parallel_workers":2,
      "scientific_exit":{
        "original_density_linear_constraint":"xi_rho_total=0; independent noisy baseline fails",
        "same_W2_energy_law_exact_static_mean_with_new_shell_coherence":True,
        "complete_static_local_noise_difference":"pure pressure, rank two",
        "full_field_smooth_history_contrast_lower":science["history_witness"]["full_field_contrast_strict_lower_c_equals_w"],
        "explicit_pure_memory_dilation_and_real_carrier_future_model":True,
        "classical_autonomous_benchmark_claimed_original_full_QFT":False,
        "old_response_used_as_expanded_carrier_response":False,
        "initial_covariance_nonidentifiability_and_quantum_uncertainty_retained":True,
        "local_preparation_causality_gate":science["preparation_causality"]["necessary_static_cap_conformal_duration"],
        "native_read_only_research_agents":3,"external_human_peer_review":False,
        "common_total_on_shell_preparation_and_calibrated_gravity":"OPEN",
        "whole_unified_physics_goal":"OPEN"},
      "status":"PASS" if passed else "FAIL"}
    output.write_text(json.dumps(result,indent=2,sort_keys=True,ensure_ascii=False)+"\n")
    print("Reused 121 results with 438 unchanged scientific files; executed 16 new entries.")
    print("Receipt: "+str(output))
    return 0 if passed else 1
if __name__=="__main__":raise SystemExit(main())
