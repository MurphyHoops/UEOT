#!/usr/bin/env python3
"""Execute only the four new growing-carrier gates and bind their actual bytes."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[2]


def ident(path):
    raw=path.read_bytes()
    try:name=str(path.relative_to(REPO))
    except ValueError:name=str(path)
    return {"path":name,"sha256":hashlib.sha256(raw).hexdigest(),"bytes":len(raw)}


def context():
    head=subprocess.check_output(["git","rev-parse","HEAD"],cwd=REPO,text=True).strip()
    dirty=bool(subprocess.check_output(["git","status","--porcelain"],cwd=REPO,text=True).strip())
    out={"provider":"github_actions" if os.getenv("GITHUB_ACTIONS")=="true" else "local_python_process",
         "observed_git_head":head,"worktree_has_changes":dirty,
         "identity_authority":"input hashes bind the executed bytes; a checkout SHA alone does not identify a dirty worktree"}
    if os.getenv("GITHUB_ACTIONS")=="true":
        out["github"]={k:os.getenv(k) for k in ["GITHUB_REPOSITORY","GITHUB_RUN_ID","GITHUB_RUN_ATTEMPT",
                         "GITHUB_WORKFLOW","GITHUB_JOB","GITHUB_SHA","GITHUB_REF","GITHUB_EVENT_NAME"]}
    return out


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir",type=Path,default=HERE.parent/"kernel/evidence/v31.12/runtime")
    args=parser.parse_args();out=args.output_dir.resolve();out.mkdir(parents=True,exist_ok=True)
    sources=sorted([p for p in HERE.iterdir() if p.suffix in {".py",".json",".md"} and p.is_file()])
    sources += [HERE.parent/"conditioning/finite_conditioning.py",
                HERE.parent/"audits/GROWING_CUTOFF_v31.12/SHARED_MODEL.md"]
    before=[ident(p) for p in sources]
    commands=[
      ("source-integration",["verify_integration.py","--model",str(HERE/"frozen_model.json"),"--output",str(out/"integration.json")]),
      ("independent-operational",["check_operational_growth.py","--output",str(out/"operational.json")]),
      ("independent-microscopic",["check_micro_growth.py","--output",str(out/"micro-growth.json")]),
      ("independent-exact-certificate",["exact_checker.py","--model",str(HERE/"frozen_model.json"),"--output",str(out/"exact-certificate.json")]),
    ]
    actual=[]
    for label,argv in commands:
        command=[sys.executable,str(HERE/argv[0]),*argv[1:]]
        started=datetime.now(timezone.utc).isoformat()
        result=subprocess.run(command,cwd=REPO,text=True,capture_output=True)
        log=out/(label+".log");log.write_text(result.stdout+result.stderr)
        actual.append({"label":label,"argv":command,"cwd":str(REPO),"started_at_utc":started,
                       "finished_at_utc":datetime.now(timezone.utc).isoformat(),
                       "exit_code":result.returncode,"log":ident(log)})
        print(json.dumps({"gate":label,"exit_code":result.returncode}),flush=True)
        if result.returncode:break
    after=[ident(p) for p in sources]
    passed=len(actual)==len(commands) and all(x["exit_code"]==0 for x in actual) and before==after
    outputs=[ident(p) for p in sorted(out.iterdir()) if p.is_file() and p.name!="execution_receipt.json"]
    receipt={"schema":"ueot-qm.growing-cutoff-runtime/1","version":"v31.12",
             "status":"PASS" if passed else "FAIL","created_at_utc":datetime.now(timezone.utc).isoformat(),
             "research_baseline":"aea2fceef3c62cc8dc749b6cbb1b40a7d89df80d",
             "execution_context":context(),"python":sys.version,"platform":platform.platform(),
             "commands":actual,"inputs":before,"inputs_stable_during_execution":before==after,"outputs":outputs,
             "evidence_classes":["exact rational identities and radical enclosures","finite floating matrix controls"],
             "universal_analytic_proofs_are_not_inferred_from_samples":True,
             "historical_heavy_suites_reexecuted":False,"new_lean_execution":False,"new_hardware_data":False,
             "recovery":"new reconstructed-source execution, not a recovered interrupted v31.12 receipt"}
    (out/"execution_receipt.json").write_text(json.dumps(receipt,indent=2)+"\n")
    print(json.dumps({"status":receipt["status"],"gates":len(actual),"inputs":len(before)}))
    if not passed:raise SystemExit(1)


if __name__=="__main__":main()
