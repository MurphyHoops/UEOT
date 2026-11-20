"""Reuse 146 frozen results and verify twelve new finite-stress/original-constraint certificates."""
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
BASE="d61a418a9d748f793979c2eecc2f03a686c5b2fb"
PREFIX="physics/qm/null_source/timelike/"
PARENT=PREFIX+"constraint_states/verification.json"
WORKFLOW=".github/workflows/ueot-physics-source-response.yml"
ROUTES=[WORKFLOW,"physics/qm/README.md","physics/qm/ROADMAP.md",PREFIX+"README.md"]
DIRECTORIES=["continuation","evolution","compatibility","response","instrument","identification",
 "stress_kernel","metric_response","operational_response","overlap_response",
 "prepared_initial","prepared_dynamics","compatible_evolution","physical_source","joint_history",
 "correlated_static","dynamic_seed","dynamic_inverse","nonlinear_history","operational_selection",
 "finite_local","total_source","constraint_states"]
RANGES=[PREFIX+d+"/" for d in DIRECTORIES]+[
 "physics/qm/null_source/FINITE_WINDOW.md","physics/qm/status/CURRENT.json",
 "formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/ScientificClosure/SISCFutureResponseCore.lean"]
VERSIONS={"numpy":"2.5.4","scipy":"1.18.1","sympy":"1.14.0","mpmath":"1.3.0"}
ENTRIES=["model","phase_diagram","critical_state","volume_moments","positive_source",
 "source_observables","dispersion_gap","finite_clock","robustness","original_ctp_gate","boundary_state","review"]
assert len(ENTRIES)==12
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
    require(len(old)==536,"Unexpected frozen inventory: "+str(len(old)))
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
    require(parent["status"]=="PASS" and len(parent["executed_now"])==9
        and all(x["returncode"]==0 for x in parent["executed_now"]),"Parent did not pass")
    require(parent["reused"]["entry_count_reused"]==137,"Wrong inherited result count")
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
    require(run["id"]==44793396821 and run["head_sha"]==BASE and run["path"]==WORKFLOW
        and run["status"]=="completed" and run["conclusion"]=="success","Wrong exact-head baseline CI")
    job=next(j for j in ci["jobs"] if j["name"]=="reproduce")
    require(job["id"]==136486603808 and job["run_id"]==run["id"]
        and job["conclusion"]=="success","Baseline job failed")
    step=next(s for s in job["steps"] if s["name"]=="Reuse 137 predecessor results and verify 9 constraint-state certificates")
    require(step["conclusion"]=="success" and ci["decoded_job_log_observed"]
        and ci["decoded_PASS_count"]==9,"Baseline science step/log failed")
    artifact=next(a for a in ci["artifacts"] if a["id"]==14657912301)
    require(artifact["workflow_run"]["head_sha"]==BASE and not artifact["expired"]
        and artifact["digest"]=="sha256:3e91640d8152a547af674fb5f7d81b5190a691255f59f8f0441fd1fa33bf1d08",
        "Wrong baseline artifact")
    return {"base_commit":BASE,"entry_count_reused":146,
      "inherited_scientific_file_count":len(inherited),"inherited_scientific_manifest":inherited,
      "parent_receipt":{"path":PARENT,"sha256":inherited[PARENT],"count":9,
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
def scope_check():
    changed=names("diff","--name-only","-z",BASE)|names("ls-files","-z","--others","--exclude-standard")
    allowed=lambda p:p in ROUTES or p.startswith(PREFIX+"finite_stress/")
    require(all(allowed(p) for p in changed),"Change outside continuation scope: "+repr(sorted(p for p in changed if not allowed(p))))
def main():
    require(__debug__ and sys.flags.optimize==0,"Assertions must remain enabled")
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output",type=Path,default=HERE/"verification.json")
    ap.add_argument("--logs",type=Path)
    args=ap.parse_args();output=args.output.resolve()
    logs=(args.logs or Path(tempfile.mkdtemp(prefix="ueot-finite-stress-logs-"))).resolve()
    require(REPO not in logs.parents and logs!=REPO,"Logs must remain outside repository")
    require(output==HERE/"verification.json" or (REPO not in output.parents and output!=REPO),"Unexpected output")
    require(sys.version_info[:2]==(3,14),"Use Python 3.14")
    actual={n:version(n) for n in VERSIONS}
    require(actual==VERSIONS,"Scientific dependency versions changed")
    logs.mkdir(parents=True,exist_ok=True);output.parent.mkdir(parents=True,exist_ok=True)
    scope_check()
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
    scope_check()
    passed=all(r["returncode"]==0 for r in rows)
    science={n:json.loads((HERE/(n+".json")).read_text()) for n in ENTRIES}
    require(all(d["status"]=="PASS" for d in science.values()),"Scientific receipt not passed")
    result={"schema":"ueot-finite-stress-verification/1",
      "timestamp_utc":datetime.now(timezone.utc).isoformat(),"git_head_at_execution":head,
      "working_tree_status_before_execution":status,"receipt_generated_before_commit_if_worktree_dirty":bool(status),
      "python":sys.version,"dependencies":actual,"reused":reused,"executed_now":rows,
      "current_source_manifest":sources,"source_manifests_unchanged_after_execution":True,
      "old_scientific_entries_rerun":0,"new_mode_ODE_integrations":0,"new_geometry_ODE_integrations":0,
      "new_interval_and_symbolic_certificates":len(ENTRIES),"read_only_parallel_workers":2,
      "scientific_exit":{
        "declared_K_inspired_model_has_unique_self_adjoint_Jacobi_family":True,
        "subcritical_finite_positive_volume_moment":"EXCLUDED_IN_DECLARED_FAMILY",
        "supercritical_exact_original_P_law":"EXCLUDED_IN_DECLARED_FAMILY",
        "critical_normal_joint_state_and_fixed_history":True,
        "critical_all_required_volume_H_graph_moments_finite":True,
        "physical_total_positive_energy_variance_finite":True,
        "normal_clock_total_positive_energy_variance_finite":True,
        "clock_constraint_RMS_upper":science["finite_clock"]["full_constraint_RMS_strict_upper"],
        "principal_reference_P_weighted_relative_gap_lower":science["dispersion_gap"]["P_probability_weighted_relative_polymer_gap_lower"],
        "finite_error_critical_uniqueness":False,
        "original_SO4_singlet_projection_gate":"CONDITIONAL_THEOREM_WITH_EXPLICIT_DOMAIN_AND_WARD",
        "original_absolute_density_RMS":science["original_ctp_gate"]["finite_window_density_RMS_if_no_new_boundary_column"],
        "normal_quantum_original_boundary_state_constructed":False,
        "new_normal_matter_only_boundary_family":True,
        "new_source_preserves_original_complete_marginal":False,
        "new_global_density_relative_RMS_upper":science["boundary_state"]["example_global_density_relative_RMS_strict_upper"],
        "new_complete_homogeneous_source_noise_budget":True,
        "actual_autonomous_new_source_preparation":False,
        "same_bare_state_and_old_normal_derivatives_claimed":False,
        "classical_symmetric_work_law_automatic":False,
        "strong_positive_dust_is_required_by_original_mean_SCE_goal":False,
        "native_read_only_research_agents":3,"external_human_peer_review":False,
        "original_full_AE_NOON_gravity_claimed_closed":False,
        "common_total_preparation_and_calibrated_gravity":"OPEN",
        "whole_unified_physics_goal":"OPEN"},
      "status":"PASS" if passed else "FAIL"}
    output.write_text(json.dumps(result,indent=2,sort_keys=True,ensure_ascii=False)+"\n")
    print("Reused 146 results with 536 unchanged scientific files; executed 12 new entries.")
    print("Receipt: "+str(output))
    return 0 if passed else 1
if __name__=="__main__":raise SystemExit(main())
