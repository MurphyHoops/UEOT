#!/usr/bin/env python3
from pathlib import Path
import datetime,hashlib,json
REPO=Path('/workspace/scratch/534b0448126c/ueot-core-next')
CORE=REPO/'formalization/ueot-core'
PACKET=CORE/'docs/compression/theory_completion/unified_closure/path_realization_v1'
BASE='d503586107974c56e0773b4ea106b41a7d144b43'
SOURCE='de7c7e287bd1b351ed3f790de58bfd71edf18df4013f7e5aaf2af55a6b3f6379'
build=json.loads((PACKET/'actual-execution/full-build-02/FULL_BUILD_RECEIPT.json').read_bytes())
assert build['state']=='PASS' and build['baseline_ref']==BASE
source_rows=[];h=hashlib.sha256()
source_paths=[CORE/'UEOT.lean',*(CORE/'UEOT').rglob('*.lean')]
by_module={p.relative_to(CORE).with_suffix('').as_posix().replace('/','.'):p for p in source_paths}
for module,p in sorted(by_module.items()):
    assert p.is_file() and not p.is_symlink();raw=p.read_bytes()
    h.update(module.encode()+b'\0'+raw+b'\0')
    source_rows.append({'module':module,'path':p.relative_to(REPO).as_posix(),'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()})
assert len(source_rows)==691 and h.hexdigest()==SOURCE
assert source_rows==build['identity']['source_files']
checks={
 'independent/ACTUAL_EXECUTION_REVIEW.json':'CLEAR',
 'independent/registration-consumer-review/REGISTRATION_REVIEW.json':'CLEAR_METADATA_ONLY_REGISTRATION_AND_EXACT_BYTE_PRESERVATION',
 'independent/registration-consumer-review/CONSUMER_DAG_REVIEW.json':'CLEAR_SIX_CONSUMERS_DAG_OLD_TEN_PRESERVATION_AND_ACTUAL_LOCAL_GATES',
 'independent/CANONICAL_UMC_EXECUTION_REVIEW.json':'ACTUAL_CANONICAL_UMC_FULL_CLEAR',
 'local-gates/LOCAL_GATE_SUMMARY.json':'REQUIRED_LOCAL_GATES_PASS'}
for p,state in checks.items():assert json.loads((PACKET/p).read_bytes())['state']==state,p
paths=set()
for d in ('native_protocol','independent','local-gates','actual-execution/native-02','actual-execution/full-build-02','actual-execution/umc-full-01','actual-execution/registration-execution-01'):
    paths.update(p for p in (PACKET/d).rglob('*') if p.is_file() and '__pycache__' not in p.parts)
for p in ('ORIGINAL_SOURCE_BINDING.json','consumer-plan/APPLIED_SIX_PATHS_01.json','actual-execution/import-01/ARCHIVE_MANIFEST.json','actual-execution/canonical-import-01/IMPORT_RECEIPT.json','actual-execution/canonical-sync-01/RECEIPT.json','actual-execution/native-01/STATUS.json','publication/align_mac_candidate.py','publication/push_candidate.py','publication/run_canonical_umc.py'):
    paths.add(PACKET/p)
six=json.loads((PACKET/'consumer-plan/APPLIED_SIX_PATHS_01.json').read_bytes())
for row in six['paths']:
    p=REPO/row['path'];assert hashlib.sha256(p.read_bytes()).hexdigest()==row['after_sha256'];paths.add(p)
reuse=CORE/'docs/compression/theory_completion/knowledge/reuse'
for n in ('PATH_REALIZATION_NATIVE_V1.json','PATH_REALIZATION_REUSE_OVERLAY_V1.json','VERIFY_PATH_REALIZATION_OVERLAY_TYPES.lean'):paths.add(reuse/n)
paths.add(CORE/'docs/compression/theory_completion/unified_closure/audit_umc_local.py')
paths.add(CORE/'docs/compression/COMPRESSION_RESEARCH_TRACKS.json')
rows=[]
for p in sorted(paths):
    assert p.is_file() and not p.is_symlink();raw=p.read_bytes()
    rows.append({'path':p.relative_to(REPO).as_posix(),'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()})
native=json.loads((reuse/'PATH_REALIZATION_NATIVE_V1.json').read_bytes())
assert len(native['public_source_theorems'])==73 and len(native['all_native_theorem_constants'])==249
canonical=json.loads((PACKET/'actual-execution/umc-full-01/UMC_FULL_AUDIT.json').read_bytes())
assert canonical['global_bundled_Lean_modules']==691 and canonical['full_Lean']=='PASS' and canonical['global_strong_unified_closure']=='NOT_ESTABLISHED'
result={'schema':'PATH_REALIZATION_ACCEPTED_PROOF_INPUTS_V1','state':'FROZEN_ACTUAL_PROOF_INPUTS_ALL_LOCAL_GATES_CLEAR','created_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'baseline_ref':BASE,'source_tree_sha256':SOURCE,'module_count':691,'source_files':source_rows,'bound_repository_files':rows,'new_public_source_theorems':73,'native_owned_theorem_constants':249,'new_registered_direct_edges':114,'current_registered_public_theorems':4345,'current_registered_direct_edges':5728,'overlay_count':11,'actual_gate_review_states':checks,'canonical_scope':canonical,'global_strong_unified_closure':'NOT_ESTABLISHED','frozen_authority':{'pids':106,'generated':11,'adapters':89,'boundaries':6,'counted_generators':4},'not_claimed':'This source-bound local acceptance is not a committed-object preflight, PR/main CI result, merge, remote-ref retirement, or new empirical evidence.'}
out=PACKET/'ACCEPTED_PROOF_INPUTS.json';assert not out.exists();raw=(json.dumps(result,indent=2)+'\n').encode();out.write_bytes(raw)
print(json.dumps({'state':result['state'],'source_files':len(source_rows),'bound_repository_files':len(rows),'sha256':hashlib.sha256(raw).hexdigest()}))
