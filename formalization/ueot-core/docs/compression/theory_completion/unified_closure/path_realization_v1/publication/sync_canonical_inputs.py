#!/usr/bin/env python3
"""Install the exact reviewed ten consumer/audit inputs on the existing Mac worktree."""
from pathlib import Path
import base64,hashlib,importlib.util,json,subprocess,sys

ROOT=Path('/Users/murphyhoops/Documents/ueotlean-worktrees/core-books-handoff-20261020')
REPO=ROOT/'path-realization-20261022'
EVIDENCE=ROOT/'path-realization-evidence-20261022'
OUT=EVIDENCE/'canonical-sync-01'
PAYLOAD=EVIDENCE/'CANONICAL_SYNC_01.json'
assert not OUT.exists()
payload=json.loads(PAYLOAD.read_bytes())
assert payload['schema']=='PATH_REALIZATION_CANONICAL_INPUT_SYNC_V1'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=REPO).decode().strip()==payload['base_ref']=='d503586107974c56e0773b4ea106b41a7d144b43'
prefix='formalization/ueot-core/docs/compression/theory_completion/'
expected={prefix+x for x in (
 'unified_closure/UMC_GLOBAL_MODULE_DAG_V4.json',
 'knowledge/README.md','knowledge/reuse/fkrg_reuse.py',
 'knowledge/reuse/test_fkrg_reuse.py','knowledge/reuse/README.md',
 'knowledge/reuse/REBUILD_CLONE_CANDIDATES.py',
 'knowledge/reuse/PATH_REALIZATION_NATIVE_V1.json',
 'knowledge/reuse/PATH_REALIZATION_REUSE_OVERLAY_V1.json',
 'knowledge/reuse/VERIFY_PATH_REALIZATION_OVERLAY_TYPES.lean',
 'unified_closure/path_realization_v1/publication/run_canonical_umc.py')}
assert len(payload['files'])==10 and {r['path'] for r in payload['files']}==expected
build=json.loads((EVIDENCE/'full-build-02/FULL_BUILD_RECEIPT.json').read_bytes())
assert build['state']=='PASS' and build['identity']['source_tree_sha256']==payload['source_tree_sha256']=='de7c7e287bd1b351ed3f790de58bfd71edf18df4013f7e5aaf2af55a6b3f6379'
helper=REPO/(prefix+'unified_closure/registered_interfaces/native_protocol/build_identity.py')
assert hashlib.sha256(helper.read_bytes()).hexdigest()==build['identity_helper_sha256']
spec=importlib.util.spec_from_file_location('path_sync_identity',helper)
module=importlib.util.module_from_spec(spec);sys.modules[spec.name]=module;spec.loader.exec_module(module)
runtime=build['identity']['runtime_tools']
def identity():return module.capture(REPO,lake=runtime['lake']['executable'],lean=runtime['lean']['executable'],expected=build['identity'])
identity()
decoded=[]
for row in payload['files']:
    path=REPO/row['path'];raw=base64.b64decode(row['data_b64'],validate=True)
    assert path.resolve().is_relative_to(REPO) and not path.is_symlink()
    assert hashlib.sha256(raw).hexdigest()==row['sha256'] and len(raw)==row['bytes']
    before=hashlib.sha256(path.read_bytes()).hexdigest() if path.exists() else None
    assert before in {row['before_sha256'],row['sha256']},(row['path'],before)
    decoded.append((row,path,raw,before))
OUT.mkdir()
(OUT/'driver.py').write_bytes(Path(__file__).read_bytes())
(OUT/'PAYLOAD.json').write_bytes(PAYLOAD.read_bytes())
rows=[]
for row,path,raw,before in decoded:
    if path.exists():
        old=OUT/'before'/row['path'];old.parent.mkdir(parents=True,exist_ok=True);old.write_bytes(path.read_bytes())
    path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)
    assert path.read_bytes()==raw
    rows.append({'path':row['path'],'before_sha256':before,'sha256':row['sha256'],'bytes':len(raw)})
identity()
receipt={'schema':'PATH_REALIZATION_CANONICAL_INPUT_SYNC_RECEIPT_V1','state':'PASS_EXACT_INPUTS_SOURCE_RUNTIME_DEPENDENCIES_UNCHANGED','base_ref':payload['base_ref'],'source_tree_sha256':payload['source_tree_sha256'],'files':rows,'payload_sha256':hashlib.sha256(PAYLOAD.read_bytes()).hexdigest(),'driver_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(OUT/'RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
