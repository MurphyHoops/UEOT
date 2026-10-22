#!/usr/bin/env python3
from pathlib import Path
import subprocess,json,time,os,signal,hashlib
ROOT=Path('/Users/murphyhoops/Documents/ueotlean-worktrees/core-books-handoff-20261020')
REPO=ROOT/'path-realization-20261022';OUT=ROOT/'path-realization-evidence-20261022/native-pair-reverse-01';OUT.mkdir(exist_ok=False)
code="""import UEOT
import Lean.Elab.Command
open Lean Elab Command Meta
set_option maxHeartbeats 0
run_cmd do
  let a ← getConstInfo `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMemorySafetyWitness.safe_source_all_times_mass_one
  let b ← getConstInfo `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMemorySafetyWitness.unsafe_transition_time_one_mass_zero
  liftIO <| IO.println "REVERSE_PAIR_ENTER"
  let eq ← liftTermElabM do Meta.isDefEq b.type a.type
  liftIO <| IO.println s!"REVERSE_PAIR_COMPLETE {eq}"
"""
src=OUT/'PairReverse.lean';src.write_text(code)
cmd=['/Users/murphyhoops/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lake','env','/Users/murphyhoops/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean',str(src)]
start=time.monotonic();interrupted=False
with (OUT/'run.log').open('wb') as f:
 p=subprocess.Popen(cmd,cwd=REPO/'formalization/ueot-core',stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
 try:exit=p.wait(timeout=25)
 except subprocess.TimeoutExpired:
  interrupted=True;os.killpg(p.pid,signal.SIGINT);exit=p.wait(timeout=10)
r={'state':'ISOLATED_DIAGNOSTIC_NOT_ACCEPTANCE','command':cmd,'exit_code':exit,'seconds':time.monotonic()-start,'interrupted_after_25_seconds':interrupted,'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'log_sha256':hashlib.sha256((OUT/'run.log').read_bytes()).hexdigest(),'production_source_changed':False}
(OUT/'RECEIPT.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r));print((OUT/'run.log').read_text())
