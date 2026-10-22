#!/usr/bin/env python3
from pathlib import Path
import subprocess, json, hashlib, datetime, time
ROOT = Path('/Users/murphyhoops/Documents/ueotlean-worktrees/core-books-handoff-20261020')
REPO = ROOT / 'path-realization-20261022'
OUT = ROOT / 'path-realization-evidence-20261022' / 'publication'
META = json.loads((OUT/'CANDIDATE.json').read_bytes())
assert META['schema']=='PATH_REALIZATION_PUBLICATION_CANDIDATE_V1' and META['state']=='PASS_EXACT_CANDIDATE_REVIEW'
HEAD = META['candidate']; TREE = META['tree']
BASE = 'd503586107974c56e0773b4ea106b41a7d144b43'
assert META['baseline']==BASE
REF = 'refs/heads/compression/theory-completion-path-realization'
def run(args):
    p = subprocess.run(args, cwd=REPO, capture_output=True)
    assert p.returncode == 0, (args, p.returncode, p.stderr.decode(errors='replace'))
    return p.stdout
def refs():
    raw = run(['git', 'ls-remote', '--heads', 'origin'])
    return raw, {line.split()[1]: line.split()[0] for line in raw.decode().splitlines()}
assert run(['git','rev-parse',HEAD+'^{tree}']).decode().strip() == TREE
assert run(['git','rev-parse','HEAD']).decode().strip() == HEAD
aligned=json.loads((OUT/'MAC_CANDIDATE_ALIGNED.json').read_bytes())
assert aligned['state']=='PASS_EXACT_CANDIDATE_TRACKED_CLEAN_AND_PROOF_IDENTITY' and aligned['candidate']==HEAD and aligned['tree']==TREE
assert aligned['source_tree_sha256']==META['source_tree_sha256']=='de7c7e287bd1b351ed3f790de58bfd71edf18df4013f7e5aaf2af55a6b3f6379'
before_raw, before = refs()
assert before['refs/heads/main'] == BASE
assert REF not in before, 'Our branch unexpectedly already exists; inspect before retry'
(OUT/'PUSH_REMOTE_BEFORE.txt').write_bytes(before_raw)
cmd = ['git','push','--porcelain','--force-with-lease='+REF+':','origin',HEAD+':'+REF]
start = time.monotonic()
utc = datetime.datetime.now(datetime.timezone.utc).isoformat()
p = subprocess.run(cmd, cwd=REPO, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
(OUT/'PUSH.log').write_bytes(p.stdout)
record = {'schema':'PATH_REALIZATION_CANDIDATE_PUSH_V1','started_at_utc':utc,'command':cmd,'cwd':str(REPO),'elapsed_seconds':time.monotonic()-start,'exit_code':p.returncode,'candidate':HEAD,'tree':TREE,'baseline':BASE,'log_sha256':hashlib.sha256(p.stdout).hexdigest(),'state':'PUSH_RETURNED_PENDING_REMOTE_VERIFICATION'}
(OUT/'PUSH_EXECUTION.json').write_text(json.dumps(record,indent=2)+'\n')
assert p.returncode == 0, p.stdout.decode(errors='replace')
after_raw, after = refs()
(OUT/'PUSH_REMOTE_AFTER.txt').write_bytes(after_raw)
assert after[REF] == HEAD
assert {k:v for k,v in after.items() if k != REF} == before
accepted = {**record,'state':'PASS_PUSH_EXACT_HEAD_ONLY','remote_other_refs_unchanged':True,'remote_main':after['refs/heads/main'],'before_refs_sha256':hashlib.sha256(before_raw).hexdigest(),'after_refs_sha256':hashlib.sha256(after_raw).hexdigest()}
(OUT/'PUSH_ACCEPTED.json').write_text(json.dumps(accepted,indent=2)+'\n')
print(json.dumps(accepted))
