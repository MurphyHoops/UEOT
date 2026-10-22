#!/usr/bin/env python3
from pathlib import Path
import base64, datetime, hashlib, json, lzma

ROOT = Path('/Users/murphyhoops/Documents/ueotlean-worktrees/core-books-handoff-20261020/path-realization-evidence-20261022')
OUT = ROOT / 'transfer-execution-01'
assert json.loads((ROOT/'full-build-01/FULL_BUILD_RECEIPT.json').read_text())['state'] == 'PASS'
assert json.loads((ROOT/'native-01/STATUS.json').read_text())['state'] == 'PASS_PENDING_INDEPENDENT_REVIEW_AND_REGISTRATION'
assert not OUT.exists()
records = []
for path in sorted(ROOT.rglob('*')):
    relative = path.relative_to(ROOT)
    if any(part.startswith('transfer-') or part == '__pycache__' or part.startswith('.') for part in relative.parts):
        continue
    if not path.is_file():
        continue
    assert not path.is_symlink()
    raw = path.read_bytes()
    records.append({'path':relative.as_posix(),'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest(),'data_b64':base64.b64encode(raw).decode()})
payload = json.dumps({'schema':'PATH_REALIZATION_MAC_EXECUTION_BYTE_EXPORT_V1','source_root':str(ROOT),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':records},separators=(',',':')).encode()
packed = lzma.compress(payload,preset=6)
text = base64.b64encode(packed).decode()
OUT.mkdir()
parts=[]
for index,start in enumerate(range(0,len(text),60000)):
    part=text[start:start+60000]
    name='part-%03d.b64'%index
    (OUT/name).write_text(part+'\n')
    parts.append({'name':name,'characters':len(part),'sha256':hashlib.sha256((part+'\n').encode()).hexdigest()})
receipt={'schema':'PATH_REALIZATION_MAC_EXECUTION_TRANSFER_V1','state':'EXPORTED_EXACT_BYTES','files':len(records),'raw_file_bytes':sum(x['bytes'] for x in records),'payload_bytes':len(payload),'compressed_bytes':len(packed),'payload_sha256':hashlib.sha256(payload).hexdigest(),'compressed_sha256':hashlib.sha256(packed).hexdigest(),'parts':parts,'inventory':[ {k:v for k,v in x.items() if k!='data_b64'} for x in records]}
(OUT/'MANIFEST.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k!='inventory'}))
