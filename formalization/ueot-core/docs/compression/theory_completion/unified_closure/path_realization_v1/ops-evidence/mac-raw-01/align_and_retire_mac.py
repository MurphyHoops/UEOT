#!/usr/bin/env python3
from pathlib import Path
import subprocess, hashlib, json, datetime, time
ROOT=Path('/Users/murphyhoops/Documents/ueotlean-worktrees/core-books-handoff-20261020')
REPO=ROOT/'path-realization-20261022'
OUT=ROOT/'path-realization-evidence-20261022'/'ops-main-retirement-01'
OUT.mkdir(exist_ok=False)
BASE='50a91fb9c81e0f5e698ce2cc02ec1a44c9583b04'
MAIN='d503586107974c56e0773b4ea106b41a7d144b43'
HEAD='91366e9cf38815788978aeaf010f3016942d31dd'
TREE='08e1f9869bdad2c8b1d2a95a602711ffaa1eb92b'
REF='refs/heads/ops/compression-tc-path-realization-evidence'
COMMANDS=[]
def run(args):
 t=time.monotonic();p=subprocess.run(args,cwd=REPO,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 COMMANDS.append({'args':args,'exit_code':p.returncode,'seconds':time.monotonic()-t,'output':p.stdout.decode(errors='replace')})
 (OUT/'COMMANDS.json').write_text(json.dumps(COMMANDS,indent=2)+'\n')
 assert p.returncode==0,(args,p.stdout.decode(errors='replace'))
 return p.stdout

def source():
 core=REPO/'formalization/ueot-core'
 paths=[core/'UEOT.lean',*(core/'UEOT').rglob('*.lean')]
 return {str(p.relative_to(REPO)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}

assert run(['git','branch','--show-current']).decode().strip()=='compression/theory-completion-path-realization'
assert run(['git','rev-parse','HEAD']).decode().strip()==BASE
before_source=source()
run(['git','fetch','--prune','origin'])
assert run(['git','rev-parse','origin/main']).decode().strip()==MAIN
assert run(['git','rev-parse',MAIN+'^{tree}']).decode().strip()==TREE
assert run(['git','diff','--name-only',BASE,MAIN]).decode().strip()=='formalization/ueot-core/docs/compression/COMPRESSION_RESEARCH_TRACKS.json'
assert HEAD in run(['git','rev-list','--parents','-n','1',MAIN]).decode().split()[1:]
run(['git','merge','--ff-only',MAIN])
assert run(['git','rev-parse','HEAD']).decode().strip()==MAIN
assert source()==before_source
before_raw=run(['git','ls-remote','--heads','origin']);(OUT/'REMOTE_BEFORE.txt').write_bytes(before_raw)
before=dict((s.split()[1],s.split()[0]) for s in before_raw.decode().splitlines())
assert before['refs/heads/main']==MAIN
assert before.get(REF) in (None,HEAD)
# Root observed all open PRs = [] after PR366 merged; required resulting-main
# classification/governance succeeded and the separate proof job was skipped.
if REF in before:
 run(['git','push','--porcelain','--force-with-lease='+REF+':'+HEAD,'origin',':'+REF])
after_raw=run(['git','ls-remote','--heads','origin']);(OUT/'REMOTE_AFTER.txt').write_bytes(after_raw)
after=dict((s.split()[1],s.split()[0]) for s in after_raw.decode().splitlines())
assert REF not in after and after=={k:v for k,v in before.items() if k!=REF}
r={'schema':'PATH_REALIZATION_OPS_MAIN_MAC_ACCEPTANCE_V1','state':'PASS_MAC_BASE_ALIGNED_AND_EXACT_OWNED_OPS_REF_RETIRED','main':MAIN,'tree':TREE,'ops_head':HEAD,'ops_ref':REF,'other_remote_refs_unchanged':True,'science_source_bytes_unchanged_by_policy_fast_forward':True,'science_modules':len(before_source),'main_guard_run':39707704830,'main_governance_job':119591556922,'main_proof_job':119591803537,'main_proof':'SKIPPED_NOT_LEAN_EVIDENCE','root_observed_open_prs_before_retirement':[],'before_refs_sha256':hashlib.sha256(before_raw).hexdigest(),'after_refs_sha256':hashlib.sha256(after_raw).hexdigest(),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
(OUT/'ACCEPTED.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))

