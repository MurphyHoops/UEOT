#!/usr/bin/env python3
"""Run scoped v31.13 gates and preserve actual execution/source identities."""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import zipfile

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[2]


def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def ident(p):
    try:path=str(p.relative_to(REPO))
    except ValueError:path=str(p)
    return {'path':path,'sha256':digest(p),'bytes':p.stat().st_size}
def context():
    g=os.getenv('GITHUB_ACTIONS')=='true'
    ctx={'provider':'github_actions' if g else 'local_python_process',
      'observed_git_head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=REPO,text=True).strip(),
      'worktree_has_changes':bool(subprocess.check_output(['git','status','--porcelain'],cwd=REPO,text=True).strip()),
      'authority':'input hashes identify executed bytes, including a dirty worktree; checker authorship is not executor identity'}
    if g:ctx['github']={k:os.getenv(k) for k in ['GITHUB_REPOSITORY','GITHUB_RUN_ID','GITHUB_RUN_ATTEMPT','GITHUB_WORKFLOW','GITHUB_JOB','GITHUB_SHA','GITHUB_REF','GITHUB_EVENT_NAME']}
    return ctx


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output-dir',type=Path,required=True)
    a=ap.parse_args();out=a.output_dir.resolve()
    if out.exists() and any(out.iterdir()):raise ValueError('use an empty output directory; preserve prior executions separately')
    out.mkdir(parents=True,exist_ok=True)
    source=sorted(p for p in HERE.iterdir() if p.suffix in {'.py','.json','.md'} and p.is_file())
    source += [HERE.parent/'conditioning/finite_conditioning.py',
               HERE.parent/'audits/SIMULTANEOUS_CUTOFF_v31.13/SHARED_MODEL.md']
    before=[ident(p) for p in source]
    raw=out/'synthetic';plan=HERE/'FROZEN_CERTIFICATE_PLAN.json';model=HERE/'frozen_model.json'
    executor='github_actions_runtime_process' if os.getenv('GITHUB_ACTIONS')=='true' else 'local_python_process'
    commands=[
      ('source-integration',['verify_integration.py','--output',out/'integration.json']),
      ('independent-operational',['check_full_cq_stability.py','--output',out/'operational.json']),
      ('independent-microscopic',['check_simultaneous_galerkin.py','--model',model,'--output',out/'micro.json']),
      ('synthetic-generation',['generate_synthetic.py','--plan',plan,'--output-dir',raw]),
      ('truth-blind-calibration',['certify_from_records.py','--plan',plan,'--raw-dir',raw,'--output',out/'calibration.json']),
      ('independent-rational-calibration',['independent_certificate_check.py','--plan',plan,'--raw-dir',raw,
         '--report',out/'calibration.json','--shared-model',model,'--executor',executor,'--output',out/'independent-calibration.json']),
      ('integer-interval-prediction',['interval_predictor.py','--calibration',out/'calibration.json','--output',out/'interval-prediction.json']),
      ('independent-interval-output',['verify_interval_output.py','--artifact',out/'interval-prediction.json',
         '--predictor',HERE/'interval_predictor.py','--output',out/'independent-interval.json']),
      ('end-to-end-binding',['verify_end_to_end.py','--directory',out,'--output',out/'end-to-end.json']),
    ]
    runs=[]
    for label,argv in commands:
        cmd=[sys.executable,str(HERE/argv[0]),*[str(x) for x in argv[1:]]]
        start=datetime.now(timezone.utc).isoformat()
        result=subprocess.run(cmd,cwd=REPO,text=True,capture_output=True)
        log=out/(label+'.log');log.write_text(result.stdout+result.stderr)
        runs.append({'label':label,'argv':cmd,'cwd':str(REPO),'started_at_utc':start,
          'finished_at_utc':datetime.now(timezone.utc).isoformat(),'exit_code':result.returncode,
          'log':{**ident(log),'artifact_path':str(log.relative_to(out))}})
        print(json.dumps({'gate':label,'exit_code':result.returncode}),flush=True)
        if result.returncode:break
    members=[]
    if raw.exists():
        archive=out/'synthetic_raw.zip'
        with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
            for p in sorted(raw.iterdir()):
                if not p.is_file():continue
                info=zipfile.ZipInfo(p.name,date_time=(2026,11,12,0,0,0));info.compress_type=zipfile.ZIP_DEFLATED
                z.writestr(info,p.read_bytes(),compresslevel=9)
                members.append({'archive':'synthetic_raw.zip','member':p.name,'sha256':digest(p),'bytes':p.stat().st_size})
        # Only this runner's generated temporary raw directory is removed.
        # The lossless archive contains every ordered stream and provenance.
        shutil.rmtree(raw)
    after=[ident(p) for p in source]
    passed=len(runs)==len(commands) and all(x['exit_code']==0 for x in runs) and before==after
    outputs=[{**ident(p),'artifact_path':str(p.relative_to(out))} for p in sorted(out.iterdir()) if p.is_file()]
    receipt={'schema':'ueot-qm.simultaneous-cutoff-runtime/1','version':'v31.13',
      'status':'PASS' if passed else 'FAIL','created_at_utc':datetime.now(timezone.utc).isoformat(),
      'research_baseline':'cb17211653fde30aa50e0e9848798a6a5b3b3f12','execution_context':context(),
      'python':sys.version,'platform':platform.platform(),'commands':runs,'inputs':before,
      'inputs_stable_during_execution':before==after,'outputs':outputs,'raw_archive_members':members,
      'evidence_classes':['paper proofs separately reviewed','finite floating diagnostics','exact rational checks',
         'directed integer numerical output for a specified input','explicit synthetic complete streams'],
      'new_lean_execution':False,'historical_heavy_suites_reexecuted':False,'new_hardware_data':False,
      'universal_quantifiers_not_inferred_from_samples':True}
    (out/'execution_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'status':receipt['status'],'commands':len(runs),'inputs':len(source),'raw_members':len(members)}))
    if not passed:raise SystemExit(1)


if __name__=='__main__':main()
