"""Reuse 319 accepted entries; execute only the renormalized-continuum cohort."""
from __future__ import annotations
import argparse,hashlib,json,os,subprocess,sys,tempfile,time
from pathlib import Path
from datetime import datetime,timezone
from concurrent.futures import ThreadPoolExecutor
from importlib.metadata import version
HERE=Path(__file__).resolve().parent;REPO=HERE.parents[6]
BASE="3cd6f7ead5743782173e44ab3344b8129c01c899"
PREFIX="physics/qm/null_source/timelike/"
NEW=PREFIX+"finite_stress/lapse_boundary/renormalized_continuum/"
PARENT=PREFIX+"finite_stress/lapse_boundary/joint_constraints/verification.json"
WORKFLOW=".github/workflows/ueot-physics-source-response.yml"
ROUTES=[WORKFLOW,"physics/qm/README.md","physics/qm/ROADMAP.md",PREFIX+"README.md"]
ENTRIES=["geodesic_cap_kernel","continuum_clock_composite","continuum_tadpole_columns","review"]
VERSIONS={"numpy":"2.5.4","scipy":"1.18.1","sympy":"1.14.0","mpmath":"1.3.0"}
def require(ok,msg):
    if not ok:raise RuntimeError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def git(*args):return subprocess.check_output(["git",*args],cwd=REPO)
def names(*args):return {p.decode() for p in git(*args).split(b"\0") if p}
def git_blobs_sha(commit,rels):
    rels=list(rels)
    inp="".join(f"{commit}:{r}\n" for r in rels).encode()
    out=subprocess.check_output(["git","cat-file","--batch"],cwd=REPO,input=inp)
    pos=0;res={}
    for r in rels:
        nl=out.index(b"\n",pos);hdr=out[pos:nl].decode().split()
        require(len(hdr)==3 and hdr[1]=="blob","Missing git blob "+r)
        sz=int(hdr[2]);start=nl+1;end=start+sz
        res[r]=sha(out[start:end]);pos=end+1
    return res
def frozen():
    parent=json.loads((REPO/PARENT).read_text())
    manifest=dict(parent["reused"]["inherited_scientific_manifest"])
    require(len(manifest)==1090 and parent["reused"]["entry_count_reused"]==294,"Parent reuse chain")
    require(parent["status"]=="PASS" and len(parent["executed_now"])==25 and all(r["returncode"]==0 for r in parent["executed_now"]),"Parent execution receipt")
    parent_blobs=git_blobs_sha(BASE,list(parent["current_source_manifest"])+[PARENT])
    routes={}
    for rel,digest in parent["current_source_manifest"].items():
        require(parent_blobs[rel]==digest,"Parent source does not match BASE: "+rel)
        if rel in ROUTES:routes[rel]=digest
        else:
            require(rel not in manifest,"Duplicate inherited source")
            manifest[rel]=digest
    require(set(routes)==set(ROUTES),"Routing evidence missing")
    manifest[PARENT]=parent_blobs[PARENT]
    require(len(manifest)==1178,"Inherited file inventory count")
    dirs={PREFIX+r[len(PREFIX):].split("/")[0]+"/" for r in manifest if r.startswith(PREFIX)}
    files={r for r in manifest if not r.startswith(PREFIX)}
    ranges=sorted(dirs|files)
    old=names("ls-tree","-rz","--name-only",BASE,"--",*ranges)
    now=names("ls-files","-z","--cached","--others","--exclude-standard","--",*ranges)
    now={r for r in now if not r.startswith(NEW)}
    require(old==now==set(manifest),"Inherited exact inventory changed")
    all_blobs=git_blobs_sha(BASE,manifest.keys())
    for rel,digest in manifest.items():
        p=REPO/rel
        require(p.is_file() and not p.is_symlink() and sha(p.read_bytes())==digest,"Frozen bytes changed: "+rel)
        require(all_blobs[rel]==digest,"Frozen Git identity changed: "+rel)
    ci=json.loads((HERE/"baseline_ci.json").read_text())
    run=ci["run"]
    require(run["id"]==44993707266 and run["head_sha"]==BASE and run["path"]==WORKFLOW and run["status"]=="completed" and run["conclusion"]=="success","Exact-head prior CI")
    job=next(j for j in ci["jobs"] if j["name"]=="reproduce")
    require(job["id"]==137120103830 and job["conclusion"]=="success","Prior CI job")
    require(ci["decoded_PASS_count"]==25 and ci["decoded_head_observed"] and ci["decoded_log_observed"],"Prior decoded log")
    require(ci["decoded_log_sha256"]=="35a7cddb50e246b745bc1528c0201915fdda4a1232a20cfbd0cf9d093a576b53","Prior decoded identity")
    art=next(a for a in ci["artifacts"] if a["id"]==14743200549)
    require(art["digest"]=="sha256:9fa85eaa28f47b1cc629ee183982e6fc28c11c68fc3f036111cfc4bb8ce67078" and art["workflow_run"]["head_sha"]==BASE,"Prior artifact identity")
    return {"entry_count_reused":319,"base_commit":BASE,
      "inherited_scientific_file_count":len(manifest),"inherited_scientific_manifest":manifest,
      "parent_receipt":{"path":PARENT,"sha256":manifest[PARENT],"count":25,"executed_again_this_run":False,
        "git_head_at_original_execution":parent["git_head_at_execution"]},
      "exact_head_ci_run":run,"exact_head_ci_job":job["id"],
      "decoded_parent_PASS_entries":ci["decoded_PASS_entries"],"decoded_parent_log_sha256":ci["decoded_log_sha256"],
      "routing_baseline":routes,"earlier_chain_preserved_in_parent_receipt":True}
def manifest_now():
    ps=[p for p in HERE.rglob("*") if p.is_file() and p!=HERE/"verification.json" and "__pycache__" not in p.parts and (p.suffix in {".py",".md",".json"} or p.name==".gitignore")]
    ps += [REPO/r for r in ROUTES]
    return {str(p.relative_to(REPO)):sha(p.read_bytes()) for p in sorted(ps)}
def scope():
    changed=names("diff","--name-only","-z",BASE)|names("ls-files","-z","--others","--exclude-standard")
    require(all(r in ROUTES or r.startswith(NEW) for r in changed),"Outside authorized new cohort/routes")
def main():
    require(__debug__ and sys.flags.optimize==0,"Assertions enabled")
    ap=argparse.ArgumentParser();ap.add_argument("--output",type=Path,default=HERE/"verification.json");ap.add_argument("--logs",type=Path)
    args=ap.parse_args();out=args.output.resolve()
    logs=(args.logs or Path(tempfile.mkdtemp(prefix="ueot-renormalized-continuum-"))).resolve()
    require(REPO not in logs.parents and logs!=REPO,"Logs must be outside repository")
    require(out==HERE/"verification.json" or REPO not in out.parents,"Unexpected receipt destination")
    require(sys.version_info[:2]==(3,14),"Python 3.14 required")
    deps={n:version(n) for n in VERSIONS};require(deps==VERSIONS,"Dependency versions changed")
    logs.mkdir(parents=True,exist_ok=True);out.parent.mkdir(parents=True,exist_ok=True)
    scope();reuse=frozen();sources=manifest_now()
    head=git("rev-parse","HEAD").decode().strip();status=git("status","--short").decode()
    env=os.environ.copy();env.update(OPENBLAS_NUM_THREADS="1",OMP_NUM_THREADS="1",PYTHONDONTWRITEBYTECODE="1")
    def execute(name):
        start=time.monotonic();print("RUN: "+name,flush=True)
        p=subprocess.run([sys.executable,"-B",str(HERE/(name+".py")),"--check"],cwd=REPO,env=env,capture_output=True,timeout=180)
        op=logs/(name+".stdout.txt");ep=logs/(name+".stderr.txt");op.write_bytes(p.stdout);ep.write_bytes(p.stderr)
        print(("PASS: " if p.returncode==0 else "FAIL: ")+name,flush=True)
        if p.returncode:print(p.stdout.decode()+p.stderr.decode(),flush=True)
        return {"entry":name,"returncode":p.returncode,"duration_seconds":round(time.monotonic()-start,3),
          "source":str((HERE/(name+".py")).relative_to(REPO)),"arguments":["--check"],
          "stdout_sha256":sha(p.stdout),"stderr_sha256":sha(p.stderr),"stdout_path":str(op),"stderr_path":str(ep)}
    with ThreadPoolExecutor(max_workers=2) as pool:rows=list(pool.map(execute,ENTRIES))
    require(reuse==frozen(),"Inherited sources changed during run")
    require(sources==manifest_now(),"Current sources changed during run");scope()
    ok=all(r["returncode"]==0 for r in rows)
    result={"schema":"ueot-renormalized-continuum-verification/1","status":"PASS" if ok else "FAIL",
      "timestamp_utc":datetime.now(timezone.utc).isoformat(),"git_head_at_execution":head,
      "working_tree_status_before_execution":status,"receipt_generated_before_commit_if_worktree_dirty":bool(status),
      "python":sys.version,"dependencies":deps,"reused":reuse,"executed_now":rows,
      "current_source_manifest":sources,"source_manifests_unchanged_after_execution":True,
      "predecessor_scientific_entries_rerun":0,"predecessor_scientific_modules_imported":0,
      "mode_ODE_integrations":0,"geometry_ODE_integrations":0,
      "new_scientific_entries":len(ENTRIES)-1,"new_scope_binding_entries":1,
      "native_read_only_research_agents":3,"external_human_peer_review":False,"machine_formal_proof":False,
      "scientific_exit":{
        "continuum_cap_smeared_autonomous_apparatus":"CONSTRUCTED_WITH_UNIFORM_FRIEDRICHS_LOWER_BOUND_AT_FINITE_SENSOR_RADIUS",
        "controller_spatial_quadrupole_and_subcritical_bounce_FRW":"SOLVED_WITH_6_CHANNEL_CONFORMAL_PARSEVAL_FRAME_AND_TAYLOR_PICARD_BOUNCE",
        "local_autonomous_pointer_and_coupled_CTP_kernel":"DERIVED_WITH_SMEARED_STRESS_VARIANCE_AND_CUTOFF_WARD_DECAY",
        "pointlike_apparatus_and_operator_quantum_Einstein":"OPEN",
        "physical_unification":"OPEN"}}
    out.write_text(json.dumps(result,indent=2,ensure_ascii=False,sort_keys=True)+"\n")
    print("Reused 319 results with 1178 unchanged scientific files; executed "+str(len(ENTRIES))+" new entries.")
    print("Receipt: "+str(out));return 0 if ok else 1
if __name__=="__main__":raise SystemExit(main())
