#!/usr/bin/env python3
from pathlib import Path
import subprocess,hashlib,json,time,os,signal,datetime
ROOT=Path('/Users/murphyhoops/Documents/ueotlean-worktrees/core-books-handoff-20261020')
REPO=ROOT/'path-realization-20261022'; E=ROOT/'path-realization-evidence-20261022'
OUT=E/'native-diagnostic-01'; OUT.mkdir(exist_ok=False)
src=E/'native-01/PATH_REALIZATION_NATIVE_EXPORT.lean'
old=src.read_text(); s=old
anchor='  let env ← getEnv'
assert s.count(anchor)==1
s=s.replace(anchor,anchor+'\n  let progress ← liftIO <| IO.FS.Handle.mk "'+str(OUT/'progress.log')+'" .write')
for anchor, before, after in [
 ('      let eq ← liftTermElabM do Meta.isDefEq decl.type oldInfo.type','      liftIO <| progress.putStrLn s!"CROSS_ENTER|{name}|{old}"\n      liftIO <| progress.flush','      liftIO <| progress.putStrLn s!"CROSS_DONE|{name}|{old}|{eq}"\n      liftIO <| progress.flush'),
 ('      let eq ← liftTermElabM do Meta.isDefEq ci.type cj.type','      liftIO <| progress.putStrLn s!"INTERNAL_ENTER|{ni}|{nj}"\n      liftIO <| progress.flush','      liftIO <| progress.putStrLn s!"INTERNAL_DONE|{ni}|{nj}|{eq}"\n      liftIO <| progress.flush')]:
 assert s.count(anchor)==1
 s=s.replace(anchor,before+'\n'+anchor+'\n'+after)
source=OUT/'DIAGNOSTIC_PROGRESS.lean';source.write_text(s)
command=['/Users/murphyhoops/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lake','env','/Users/murphyhoops/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean',str(source)]
beg=time.monotonic();last=None;last_change=beg;reason=None;observations=[]
with (OUT/'diagnostic.log').open('wb') as stream:
 p=subprocess.Popen(command,cwd=REPO/'formalization/ueot-core',stdout=stream,stderr=subprocess.STDOUT,start_new_session=True)
 while p.poll() is None:
  time.sleep(0.5)
  progress=OUT/'progress.log'
  tail=''
  if progress.exists():
   with progress.open('rb') as st:
    st.seek(max(0,progress.stat().st_size-4096));lines=st.read().decode(errors='replace').splitlines()
   tail=lines[-1] if lines else ''
  if tail!=last:last=tail;last_change=time.monotonic()
  elapsed=time.monotonic()-beg;idle=time.monotonic()-last_change
  if (tail and idle>20) or elapsed>120:
   reason='PAIR_PROGRESS_UNCHANGED_20_SECONDS' if tail and idle>20 else 'DIAGNOSTIC_WALL_LIMIT_120_SECONDS'
   observations.append({'at_seconds':elapsed,'unchanged_seconds':idle,'latest_trace':tail})
   os.killpg(p.pid,signal.SIGINT)
   break
 try:code=p.wait(timeout=10)
 except subprocess.TimeoutExpired:
  os.killpg(p.pid,signal.SIGTERM);code=p.wait(timeout=10)
r={'schema':'PATH_REALIZATION_NATIVE_DIAGNOSTIC_V1','state':'DIAGNOSTIC_ONLY_NOT_PROOF_ACCEPTANCE','original_exporter_sha256':hashlib.sha256(old.encode()).hexdigest(),'diagnostic_source_sha256':hashlib.sha256(s.encode()).hexdigest(),'command':command,'exit_code':code,'seconds':time.monotonic()-beg,'interruption_reason':reason,'observations':observations,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'proof_sources_changed':False}
(OUT/'RECEIPT.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r))
if (OUT/'progress.log').exists():
 with (OUT/'progress.log').open('rb') as st:st.seek(max(0,(OUT/'progress.log').stat().st_size-2048));print(st.read().decode(errors='replace'))
print((OUT/'diagnostic.log').read_text(errors='replace')[-3000:])
