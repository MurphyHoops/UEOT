#!/usr/bin/env python3
from pathlib import Path,PurePosixPath
import base64,hashlib,json,lzma

ROOT=Path('/workspace/scratch/534b0448126c/tmp/core-path-realization-20261022')
TRANSFER=ROOT/'transfer-execution-02'
OUT=ROOT/'mac-import-01'
manifest=json.loads((TRANSFER/'MANIFEST.json').read_text())
assert manifest['state']=='EXPORTED_EXACT_BYTES' and not OUT.exists()
chunks=[]
for row in manifest['parts']:
    path=TRANSFER/row['name'];raw=path.read_bytes()
    assert hashlib.sha256(raw).hexdigest()==row['sha256']
    assert len(raw.decode().strip())==row['characters']
    chunks.append(raw.decode().strip())
packed=base64.b64decode(''.join(chunks),validate=True)
assert len(packed)==manifest['compressed_bytes'] and hashlib.sha256(packed).hexdigest()==manifest['compressed_sha256']
payload=lzma.decompress(packed)
assert len(payload)==manifest['payload_bytes'] and hashlib.sha256(payload).hexdigest()==manifest['payload_sha256']
data=json.loads(payload)
assert data['schema']=='PATH_REALIZATION_MAC_EXECUTION_BYTE_EXPORT_V1'
rows=data['files'];assert len(rows)==manifest['files'] and len({r['path'] for r in rows})==len(rows)
assert [{k:v for k,v in r.items() if k!='data_b64'} for r in rows]==manifest['inventory']
decoded=[]
for r in rows:
    p=PurePosixPath(r['path']);assert not p.is_absolute() and '..' not in p.parts
    raw=base64.b64decode(r['data_b64'],validate=True)
    assert len(raw)==r['bytes'] and hashlib.sha256(raw).hexdigest()==r['sha256']
    decoded.append((OUT/str(p),raw))
OUT.mkdir()
for p,raw in decoded:
    p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw)
    assert p.read_bytes()==raw
receipt={'schema':'PATH_REALIZATION_MAC_EXECUTION_CLOUD_IMPORT_V1','state':'PASS_EXACT_RAW_BYTES_IMPORTED','source_root':data['source_root'],'files':len(rows),'raw_file_bytes':sum(r['bytes'] for r in rows),'payload_sha256':manifest['payload_sha256'],'compressed_sha256':manifest['compressed_sha256'],'manifest_sha256':hashlib.sha256((TRANSFER/'MANIFEST.json').read_bytes()).hexdigest(),'files_verified':manifest['inventory']}
(ROOT/'MAC_EXECUTION_IMPORT_RECEIPT_02.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k!='files_verified'}))
