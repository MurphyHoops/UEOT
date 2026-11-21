"""Reuse 163 frozen results; execute only the new lapse-boundary science and scope checks."""
from __future__ import annotations
import argparse,hashlib,json,os,subprocess,sys,tempfile,time
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime,timezone
from importlib.metadata import version
from pathlib import Path
HERE=Path(__file__).resolve().parent
REPO=HERE.parents[5]
BASE="eae6769b97393b310054c21b804d7ed03a1371dc"
PREFIX="physics/qm/null_source/timelike/"
NEW=PREFIX+"finite_stress/lapse_boundary/"
PARENT=PREFIX+"finite_stress/verification.json"
WORKFLOW=".github/workflows/ueot-physics-source-response.yml"
ROUTES=[WORKFLOW,"physics/qm/README.md","physics/qm/ROADMAP.md",PREFIX+"README.md"]
ENTRIES=["action_boundary","endpoint_domain","tensor_noise","dynamic_witness","source_ctp",
         "smooth_preparation","operational_state","retarded_response","quiet_window",
         "causal_domain","finite_causal","finite_source_domain","action_response","covariant_response",
         "actual_inverse","prepared_readout","constraint_residual","action_lift",
         "mixed_boundary","readout_witness","canonical_preparation","hadamard_gate","prepared_mean","incoming_preparation","quantum_endpoint","review"]
VERSIONS={"numpy":"2.5.4","scipy":"1.18.1","sympy":"1.14.0","mpmath":"1.3.0"}
def require(ok,msg):
    if not ok:raise RuntimeError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def git(*args):return subprocess.check_output(["git",*args],cwd=REPO)
def names(*args):return {p.decode() for p in git(*args).split(b"\0") if p}
def frozen():
    parent=json.loads((REPO/PARENT).read_text())
    manifest=dict(parent["reused"]["inherited_scientific_manifest"])
    require(len(manifest)==536 and parent["reused"]["entry_count_reused"]==146,"Inherited chain")
    require(parent["status"]=="PASS" and len(parent["executed_now"])==17 and
            all(x["returncode"]==0 for x in parent["executed_now"]),"Parent not passed")
    routes={}
    for rel,digest in parent["current_source_manifest"].items():
        require(sha(git("show",BASE+":"+rel))==digest,"Parent exact-base source mismatch: "+rel)
        if rel in ROUTES:routes[rel]=digest
        else:
            require(rel not in manifest,"Unexpected duplicate predecessor source")
            manifest[rel]=digest
    require(set(routes)==set(ROUTES),"Missing route evidence")
    manifest[PARENT]=sha(git("show",BASE+":"+PARENT))
    require(len(manifest)==600,"Frozen file count")
    # Exact inventory of the scientific directories, not just selected named files.
    dirs={PREFIX+rel[len(PREFIX):].split("/")[0]+"/" for rel in manifest if rel.startswith(PREFIX)}
    files={rel for rel in manifest if not rel.startswith(PREFIX)}
    ranges=sorted(dirs|files)
    old=names("ls-tree","-rz","--name-only",BASE,"--",*ranges)
    now=names("ls-files","-z","--cached","--others","--exclude-standard","--",*ranges)
    now={p for p in now if not p.startswith(NEW)}
    require(old==now==set(manifest),"Frozen inventory changed")
    for rel,digest in manifest.items():
        p=REPO/rel
        require(p.is_file() and not p.is_symlink() and sha(p.read_bytes())==digest,"Frozen bytes changed: "+rel)
        require(sha(git("show",BASE+":"+rel))==digest,"Frozen baseline identity: "+rel)
    ci=json.loads((HERE/"baseline_ci.json").read_text())
    run=ci["run"]
    require(run["id"]==44821925199 and run["head_sha"]==BASE and run["path"]==WORKFLOW
            and run["status"]=="completed" and run["conclusion"]=="success","Exact-head CI proof")
    job=next(j for j in ci["jobs"] if j["name"]=="reproduce")
    require(job["id"]==136584681224 and job["conclusion"]=="success","Parent job")
    require(ci["decoded_job_log_observed"] and ci["decoded_PASS_count"]==17
            and ci["decoded_log_head_sha_observed"],"Parent decoded log")
    artifact=next(a for a in ci["artifacts"] if a["id"]==14670838115)
    require(artifact["digest"]=="sha256:9043a8cee76b456ad1b97d27ffbce6f1288db582597daab624d272e8565747c7"
            and artifact["workflow_run"]["head_sha"]==BASE,"Parent artifact")
    return {"entry_count_reused":163,"base_commit":BASE,
      "inherited_scientific_file_count":len(manifest),"inherited_scientific_manifest":manifest,
      "parent_receipt":{"path":PARENT,"sha256":manifest[PARENT],"count":17,
        "executed_again_this_run":False,"git_head_at_original_execution":parent["git_head_at_execution"]},
      "earlier_ci_chain_reused":parent["reused"]["exact_head_ci_proof_chain"],
      "exact_head_ci_run":run,"exact_head_ci_job":job["id"],
      "decoded_parent_PASS_entries":ci["decoded_PASS_entries"],
      "decoded_parent_log_sha256":ci["decoded_job_log_sha256"],"routing_baseline":routes}
def current_manifest():
    paths=[p for p in HERE.rglob("*") if p.is_file() and p!=HERE/"verification.json"
           and "__pycache__" not in p.parts and (p.suffix in {".py",".md",".json"} or p.name==".gitignore")]
    paths += [REPO/p for p in ROUTES]
    return {str(p.relative_to(REPO)):sha(p.read_bytes()) for p in sorted(paths)}
def scope():
    changed=names("diff","--name-only","-z",BASE)|names("ls-files","-z","--others","--exclude-standard")
    require(all(p in ROUTES or p.startswith(NEW) for p in changed),"Change outside authorized cohort")
def main():
    require(__debug__ and sys.flags.optimize==0,"Assertions enabled")
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output",type=Path,default=HERE/"verification.json")
    ap.add_argument("--logs",type=Path)
    args=ap.parse_args();output=args.output.resolve()
    logs=(args.logs or Path(tempfile.mkdtemp(prefix="ueot-lapse-boundary-logs-"))).resolve()
    require(REPO not in logs.parents and logs!=REPO,"Logs outside repository")
    require(output==HERE/"verification.json" or REPO not in output.parents,"Unexpected receipt path")
    require(sys.version_info[:2]==(3,14),"Python 3.14 required")
    actual={n:version(n) for n in VERSIONS};require(actual==VERSIONS,"Dependency drift")
    logs.mkdir(parents=True,exist_ok=True);output.parent.mkdir(parents=True,exist_ok=True)
    scope();reused=frozen();sources=current_manifest()
    head=git("rev-parse","HEAD").decode().strip();status=git("status","--short").decode()
    env=os.environ.copy();env.update(OPENBLAS_NUM_THREADS="1",OMP_NUM_THREADS="1",PYTHONDONTWRITEBYTECODE="1")
    def execute(name):
        start=time.monotonic();print("RUN: "+name,flush=True)
        p=subprocess.run([sys.executable,"-B",str(HERE/(name+".py")),"--check"],cwd=REPO,
                         env=env,capture_output=True,timeout=180)
        out=logs/(name+".stdout.txt");err=logs/(name+".stderr.txt")
        out.write_bytes(p.stdout);err.write_bytes(p.stderr)
        print(("PASS: " if p.returncode==0 else "FAIL: ")+name,flush=True)
        if p.returncode:print(p.stdout.decode()+p.stderr.decode(),flush=True)
        return {"entry":name,"returncode":p.returncode,"duration_seconds":round(time.monotonic()-start,3),
                "source":str((HERE/(name+".py")).relative_to(REPO)),"arguments":["--check"],
                "stdout_sha256":sha(p.stdout),"stderr_sha256":sha(p.stderr),
                "stdout_path":str(out),"stderr_path":str(err)}
    with ThreadPoolExecutor(max_workers=2) as pool:rows=list(pool.map(execute,ENTRIES))
    require(reused==frozen(),"Predecessor changed during execution")
    require(sources==current_manifest(),"Current source changed during execution");scope()
    ok=all(r["returncode"]==0 for r in rows)
    result={"schema":"ueot-lapse-boundary-verification/1","timestamp_utc":datetime.now(timezone.utc).isoformat(),
      "git_head_at_execution":head,"working_tree_status_before_execution":status,
      "receipt_generated_before_commit_if_worktree_dirty":bool(status),
      "python":sys.version,"dependencies":actual,"reused":reused,"executed_now":rows,
      "current_source_manifest":sources,"source_manifests_unchanged_after_execution":True,
      "old_scientific_entries_rerun":0,"old_scientific_modules_imported":0,
      "new_mode_ODE_integrations":0,"new_geometry_ODE_integrations":0,
      "new_scientific_entries":len(ENTRIES)-1,"new_scope_binding_entries":1,
      "native_read_only_research_agents":3,"external_human_peer_review":False,
      "scientific_exit":{"full_absolute_source_tensor_noise":True,
       "actual_homogeneous_retarded_RSET_response":True,"source_charge_and_Killing_mixed_blocks":True,
       "actual_full_field_homogeneous_causal_and_advanced_inverse":True,
       "source_GNS_two_constraint_weak_solution":True,
       "controlled_weak_metric_fluctuation_candidate":False,
       "normal_finite_mode_Hadamard_canonical_comparator":True,
       "normal_finite_smooth_memory_comparator":True,
       "full_tensor_retarded_Hessian":False,"normal_geometry_boundary_state":False,
       "physical_total_preparation_and_calibrated_gravity":"OPEN",
       "whole_unified_physics_goal":"OPEN"},"status":"PASS" if ok else "FAIL"}
    output.write_text(json.dumps(result,indent=2,ensure_ascii=False,sort_keys=True)+"\n")
    print("Reused 163 results with 600 unchanged scientific files; executed "+str(len(ENTRIES))+" new entries.")
    print("Receipt: "+str(output));return 0 if ok else 1
if __name__=="__main__":raise SystemExit(main())
