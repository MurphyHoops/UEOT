#!/usr/bin/env python3
from pathlib import Path,PurePosixPath
import base64,hashlib,json,lzma
ROOT=Path('/workspace/scratch/534b0448126c/tmp/core-path-realization-20261022')
REPO=Path('/workspace/scratch/534b0448126c/ueot-core-next')
PACKET=REPO/'formalization/ueot-core/docs/compression/theory_completion/unified_closure/path_realization_v1'
TRANSFER=ROOT/'transfer-canonical-01';OUT=ROOT/'mac-canonical-import-01'
assert not OUT.exists()
manifest=json.loads((TRANSFER/'MANIFEST.json').read_bytes());encoded=(TRANSFER/'payload.b64').read_bytes()
assert manifest['state']=='EXPORTED_EXACT_BYTES'
assert len(encoded)==manifest['encoded_bytes'] and hashlib.sha256(encoded).hexdigest()==manifest['encoded_sha256']
packed=base64.b64decode(encoded.strip(),validate=True)
assert len(packed)==manifest['compressed_bytes'] and hashlib.sha256(packed).hexdigest()==manifest['compressed_sha256']
raw=lzma.decompress(packed)
assert len(raw)==manifest['payload_bytes'] and hashlib.sha256(raw).hexdigest()==manifest['payload_sha256']
data=json.loads(raw);rows=data['files']
assert data['schema']=='PATH_REALIZATION_CANONICAL_EXACT_BYTE_EXPORT_V1' and len(rows)==manifest['files']
assert [{k:v for k,v in r.items() if k!='data_b64'} for r in rows]==manifest['inventory']
assert len({r['path'] for r in rows})==len(rows)
records=[]
for row in rows:
    rel=PurePosixPath(row['path']);assert not rel.is_absolute() and '..' not in rel.parts
    content=base64.b64decode(row['data_b64'],validate=True)
    assert len(content)==row['bytes'] and hashlib.sha256(content).hexdigest()==row['sha256']
    for path in (OUT/str(rel),PACKET/'actual-execution'/str(rel)):
        assert not path.exists() or path.read_bytes()==content
        path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(content)
        assert path.read_bytes()==content
    records.append({**{k:v for k,v in row.items() if k!='data_b64'},'archived_path':str((PACKET/'actual-execution'/str(rel)).relative_to(REPO))})
receipt={'schema':'PATH_REALIZATION_CANONICAL_EXACT_IMPORT_V1','state':'PASS_EXACT_RAW_BYTES_IMPORTED_AND_ARCHIVED','files':len(rows),'raw_file_bytes':manifest['raw_file_bytes'],'payload_sha256':manifest['payload_sha256'],'encoded_sha256':manifest['encoded_sha256'],'source_root':data['source_root'],'records':records}
text=(json.dumps(receipt,indent=2)+'\n').encode()
(ROOT/'MAC_CANONICAL_IMPORT_RECEIPT_01.json').write_bytes(text)
archive=PACKET/'actual-execution/canonical-import-01';archive.mkdir()
(archive/'IMPORT_RECEIPT.json').write_bytes(text)
for name in ('import_canonical_01.py','CANONICAL_SYNC_TRANSPORT_01.json'):(archive/name).write_bytes((ROOT/name).read_bytes())
for name in ('CANONICAL_01_TOOL_OUTPUT.json','CANONICAL_SYNC_01_TOOL_OUTPUT.json'):
    (PACKET/'actual-execution/tool-observations'/name).write_bytes((ROOT/name).read_bytes())
print(json.dumps({k:v for k,v in receipt.items() if k!='records'}))
