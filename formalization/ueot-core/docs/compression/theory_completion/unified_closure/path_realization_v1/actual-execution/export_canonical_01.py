#!/usr/bin/env python3
from pathlib import Path
import base64,hashlib,json,lzma
ROOT=Path('/Users/murphyhoops/Documents/ueotlean-worktrees/core-books-handoff-20261020')
EVIDENCE=ROOT/'path-realization-evidence-20261022'
REPO=ROOT/'path-realization-20261022'
OUT=EVIDENCE/'transfer-canonical-01'
assert not OUT.exists()
assert json.loads((EVIDENCE/'umc-full-01/EXECUTION.json').read_bytes())['state']=='PASS'
assert json.loads((EVIDENCE/'canonical-sync-01/RECEIPT.json').read_bytes())['state']=='PASS_EXACT_INPUTS_SOURCE_RUNTIME_DEPENDENCIES_UNCHANGED'
auditor=REPO/'formalization/ueot-core/docs/compression/theory_completion/unified_closure/audit_umc_local.py'
target=EVIDENCE/'umc-full-01/auditor.py'
assert not target.exists() or target.read_bytes()==auditor.read_bytes()
target.write_bytes(auditor.read_bytes())
files=[]
for directory in ('umc-full-01','canonical-sync-01'):
    files.extend(p for p in (EVIDENCE/directory).rglob('*') if p.is_file())
files.extend(EVIDENCE/n for n in ('sync_canonical_inputs.py','unpack_and_sync_canonical.py','export_canonical_01.py'))
records=[]
for p in sorted(files):
    assert not p.is_symlink()
    raw=p.read_bytes()
    records.append({'path':p.relative_to(EVIDENCE).as_posix(),'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest(),'data_b64':base64.b64encode(raw).decode()})
raw=json.dumps({'schema':'PATH_REALIZATION_CANONICAL_EXACT_BYTE_EXPORT_V1','source_root':str(EVIDENCE),'files':records},separators=(',',':')).encode()
packed=lzma.compress(raw,preset=6);encoded=base64.b64encode(packed).decode()+'\n'
OUT.mkdir();(OUT/'payload.b64').write_text(encoded)
manifest={'schema':'PATH_REALIZATION_CANONICAL_BYTE_TRANSFER_V1','state':'EXPORTED_EXACT_BYTES','files':len(records),'raw_file_bytes':sum(r['bytes'] for r in records),'payload_bytes':len(raw),'payload_sha256':hashlib.sha256(raw).hexdigest(),'compressed_bytes':len(packed),'compressed_sha256':hashlib.sha256(packed).hexdigest(),'encoded_bytes':len(encoded),'encoded_sha256':hashlib.sha256(encoded.encode()).hexdigest(),'inventory':[{k:v for k,v in r.items() if k!='data_b64'} for r in records]}
(OUT/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({k:v for k,v in manifest.items() if k!='inventory'}))
