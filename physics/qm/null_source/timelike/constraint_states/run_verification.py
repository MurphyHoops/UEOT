"""Reuse 137 frozen results and verify nine new constraint-state certificates."""
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
BASE="cb93991a0782ab97d2ff84c4d5c5a7ca8a8433fb"
PREFIX="physics/qm/null_source/timelike/"
PARENT=PREFIX+"total_source/verification.json"
WORKFLOW=".github/workflows/ueot-physics-source-response.yml"
ROUTES=[WORKFLOW,"physics/qm/README.md","physics/qm/ROADMAP.md",PREFIX+"README.md"]
DIRECTORIES=["continuation","evolution","compatibility","response","instrument","identification",
 "stress_kernel","metric_response","operational_response","overlap_response",
 "prepared_initial","prepared_dynamics","compatible_evolution","physical_source","joint_history",
 "correlated_static","dynamic_seed","dynamic_inverse","nonlinear_history","operational_selection",
 "finite_local","total_source"]
RANGES=[PREFIX+d+"/" for d in DIRECTORIES]+[
 "physics/qm/null_source/FINITE_WINDOW.md","physics/qm/status/CURRENT.json",
 "formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/ScientificClosure/SISCFutureResponseCore.lean"]
VERSIONS={"numpy":"2.5.4","scipy":"1.18.1","sympy":"1.14.0","mpmath":"1.3.0"}
ENTRIES=["static_bound","compensation","quantum_floor","zero_virial","relational",
 "positive_clock","gravity_contract","dust_regularity","review"]
assert len(ENTRIES)==9
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
    require(len(old)==498,"Unexpected frozen inventory: "+str(len(old)))
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
    require(parent["status"]=="PASS" and len(parent["executed_now"])==16
        and all(x["returncode"]==0 for x in parent["executed_now"]),"Parent did not pass")
    require(parent["reused"]["entry_count_reused"]==121,"Wrong inherited result count")
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
    require(run["id"]==44782177328 and run["head_sha"]==BASE and run["path"]==WORKFLOW
        and run["status"]=="completed" and run["conclusion"]=="success","Wrong exact-head baseline CI")
    job=next(j for j in ci["jobs"] if j["name"]=="reproduce")
    require(job["id"]==136447467693 and job["run_id"]==run["id"]
        and job["conclusion"]=="success","Baseline job failed")
    step=next(s for s in job["steps"] if s["name"]=="Reuse 121 predecessor results and verify 16 total-source certificates")
    require(step["conclusion"]=="success" and ci["decoded_job_log_observed"]
        and ci["decoded_PASS_count"]==16,"Baseline science step/log failed")
    artifact=next(a for a in ci["artifacts"] if a["id"]==14652468316)
    require(artifact["workflow_run"]["head_sha"]==BASE and not artifact["expired"]
        and artifact["digest"]=="sha256:233ed4a8203b20a480ae95138fef5cea8aafb6913b0377c6f10774665439ffd7",
        "Wrong baseline artifact")
    return {"base_commit":BASE,"entry_count_reused":137,
      "inherited_scientific_file_count":len(inherited),"inherited_scientific_manifest":inherited,
      "parent_receipt":{"path":PARENT,"sha256":inherited[PARENT],"count":16,
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
    allowed=lambda p:p in ROUTES or p.startswith(PREFIX+"constraint_states/")
    require(all(allowed(p) for p in changed),"Change outside continuation scope: "+repr(sorted(p for p in changed if not allowed(p))))
def main():
    require(__debug__ and sys.flags.optimize==0,"Assertions must remain enabled")
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output",type=Path,default=HERE/"verification.json")
    ap.add_argument("--logs",type=Path)
    args=ap.parse_args();output=args.output.resolve()
    logs=(args.logs or Path(tempfile.mkdtemp(prefix="ueot-constraint-state-logs-"))).resolve()
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
    result={"schema":"ueot-constraint-states-verification/1",
      "timestamp_utc":datetime.now(timezone.utc).isoformat(),"git_head_at_execution":head,
      "working_tree_status_before_execution":status,"receipt_generated_before_commit_if_worktree_dirty":bool(status),
      "python":sys.version,"dependencies":actual,"reused":reused,"executed_now":rows,
      "current_source_manifest":sources,"source_manifests_unchanged_after_execution":True,
      "old_scientific_entries_rerun":0,"new_mode_ODE_integrations":0,"new_geometry_ODE_integrations":0,
      "new_interval_and_symbolic_certificates":len(ENTRIES),"read_only_parallel_workers":2,
      "scientific_exit":{
        "correlated_static_strict_RMS_lower":science["static_bound"]["strict_record_weighted_relative_RMS_lower"],
        "fixed_actual_zero_marginal_energy_constraint_floor":science["zero_virial"]["proper_energy_constraint_RMS_lower"],
        "new_normal_source_stress_and_defined_influence_equivalence":True,
        "finite_positive_clock_conditional_trace_distance":science["positive_clock"]["conditional_trace_distance_upper"],
        "finite_positive_clock_full_constraint_RMS_upper":science["positive_clock"]["full_constraint_RMS_upper"],
        "clock_source_energy_retained":True,
        "separate_two_zero_mode_dust_self_adjoint_physical_model":True,
        "original_source_finite_stress_dust_embedding": "EXCLUDED_IN_DECLARED_MODEL",
        "full_minisuperspace_LB_same_exclusion":science["dust_regularity"]["full_minisuperspace_LB_unitarily_equivalent_to_flat"],
        "finite_constant_weight_exact_original_P_law_embedding": "EXCLUDED_IN_DECLARED_FAMILY",
        "dust_allowed_original_momentum_probability_upper":science["dust_regularity"]["original_subcritical_probability_upper"],
        "dust_original_source_trace_distance_lower":science["dust_regularity"]["original_vs_any_admissible_source_trace_distance_lower"],
        "original_full_AE_NOON_gravity_claimed_closed":False,
        "native_read_only_research_agents":3,"external_human_peer_review":False,
        "common_total_preparation_and_calibrated_gravity":"OPEN","whole_unified_physics_goal":"OPEN"},
      "status":"PASS" if passed else "FAIL"}
    output.write_text(json.dumps(result,indent=2,sort_keys=True,ensure_ascii=False)+"\n")
    print("Reused 137 results with 498 unchanged scientific files; executed 9 new entries.")
    print("Receipt: "+str(output))
    return 0 if passed else 1
if __name__=="__main__":raise SystemExit(main())
