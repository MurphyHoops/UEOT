#!/usr/bin/env python3
from pathlib import Path
import subprocess, json, hashlib, datetime, gzip, base64, importlib.util, sys
sys.dont_write_bytecode = True
ROOT=Path('/Users/murphyhoops/Documents/ueotlean-worktrees/core-books-handoff-20261020')
REPO=ROOT/'path-realization-20261022'
OUT=ROOT/'path-realization-evidence-20261022'/'publication'
META=json.loads((OUT/'CANDIDATE.json').read_bytes())
assert META['schema']=='PATH_REALIZATION_PUBLICATION_CANDIDATE_V1' and META['state']=='PASS_EXACT_CANDIDATE_REVIEW'
HEAD=META['candidate'];TREE=META['tree']
BASE='d503586107974c56e0773b4ea106b41a7d144b43'
assert META['baseline']==BASE
BRANCH='compression/theory-completion-path-realization'
def run(a):
    p=subprocess.run(a,cwd=REPO,capture_output=True)
    assert p.returncode==0,(a,p.returncode,p.stderr.decode(errors='replace'))
    return p.stdout
def paths(a):
    return [s.decode() for s in run(a).split(b'\0') if s]
assert run(['git','rev-parse','HEAD']).decode().strip()==BASE
assert run(['git','branch','--show-current']).decode().strip()==BRANCH
assert run(['git','rev-parse',HEAD+'^{tree}']).decode().strip()==TREE
changed=paths(['git','diff','--name-only','-z',BASE,HEAD])
assert sorted(changed)==META['changed_paths']
untracked=paths(['git','ls-files','--others','--exclude-standard','-z'])
cache_prefix='formalization/ueot-core/.lake/'
cache_paths=sorted(p for p in untracked if p.startswith(cache_prefix))
(OUT/'MAC_PRESERVED_BUILD_CACHE_PATHS.json').write_text(json.dumps(cache_paths,indent=2)+'\n')
modified=sorted(set(paths(['git','diff','--name-only','-z'])+paths(['git','diff','--cached','--name-only','-z'])+[p for p in untracked if not p.startswith(cache_prefix)]))
unexpected=sorted(set(modified)-set(changed))
(OUT/'MAC_UNEXPECTED_OUTSIDE_CACHE.json').write_text(json.dumps(unexpected,indent=2)+'\n')
assert not unexpected,('UNEXPECTED_WORKTREE_PATHS_OUTSIDE_BUILD_CACHE',len(unexpected),unexpected[:10])
records=[]
for rel in changed:
    p=REPO/rel
    if p.exists():
        assert p.is_file() and not p.is_symlink(),rel
        raw=p.read_bytes()
        records.append({'path':rel,'sha256':hashlib.sha256(raw).hexdigest(),'data64':base64.b64encode(raw).decode()})
backup=gzip.compress(json.dumps({'baseline':BASE,'candidate':HEAD,'modified_paths':modified,'existing_candidate_paths':records},sort_keys=True).encode(),mtime=0)
(OUT/'MAC_PRE_ALIGNMENT_CHECKPOINT.json.gz').write_bytes(backup)
run(['git','restore','--source='+HEAD,'--staged','--worktree','--',*changed])
assert run(['git','write-tree']).decode().strip()==TREE
run(['git','reset','--soft',HEAD])
assert run(['git','rev-parse','HEAD']).decode().strip()==HEAD
assert run(['git','diff','--name-only','-z'])==b''
assert run(['git','diff','--cached','--name-only','-z'])==b''
assert sorted(paths(['git','ls-files','--others','--exclude-standard','-z']))==cache_paths
relative='formalization/ueot-core/docs/compression/theory_completion/unified_closure/'
build=json.loads((REPO/relative/'path_realization_v1/actual-execution/full-build-02/FULL_BUILD_RECEIPT.json').read_text())
helper=REPO/relative/'registered_interfaces/native_protocol/build_identity.py'
spec=importlib.util.spec_from_file_location('accepted_build_identity',helper)
mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
runtime=Path('/Users/murphyhoops/.elan/toolchains/leanprover--lean4---v4.33.1/bin')
identity=mod.capture(REPO,lake=runtime/'lake',lean=runtime/'lean',expected=build['identity'],expected_module_count=691)
assert identity['source_tree_sha256']==META['source_tree_sha256']=='de7c7e287bd1b351ed3f790de58bfd71edf18df4013f7e5aaf2af55a6b3f6379'
identity_raw=(json.dumps(identity,indent=2,sort_keys=True)+'\n').encode()
(OUT/'MAC_CANDIDATE_BUILD_IDENTITY.json').write_bytes(identity_raw)
receipt={'schema':'PATH_REALIZATION_MAC_CANDIDATE_ALIGNMENT_V1','state':'PASS_EXACT_CANDIDATE_TRACKED_CLEAN_AND_PROOF_IDENTITY','at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'candidate':HEAD,'tree':TREE,'previous_head':BASE,'complete_source_modules':691,'source_tree_sha256':identity['source_tree_sha256'],'runtime_and_nine_dependencies_equal_accepted_build':True,'tracked_worktree_clean':True,'untracked_outside_build_cache':[],'preserved_untracked_cache_path_count':len(cache_paths),'owned_paths_restored':len(changed),'preexisting_modified_paths':modified,'checkpoint_sha256':hashlib.sha256(backup).hexdigest(),'identity_sha256':hashlib.sha256(identity_raw).hexdigest()}
(OUT/'MAC_CANDIDATE_ALIGNED.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
