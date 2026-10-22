#!/usr/bin/env python3
"""Archive imported actual execution bytes without upgrading original statuses."""
from pathlib import Path
import hashlib,json,lzma

ROOT=Path('/workspace/scratch/534b0448126c/tmp/core-path-realization-20261022')
REPO=Path('/workspace/scratch/534b0448126c/ueot-core-next')
PACKET=REPO/'formalization/ueot-core/docs/compression/theory_completion/unified_closure/path_realization_v1'
SOURCE=ROOT/'mac-import-01'
receipt_path=ROOT/'MAC_EXECUTION_IMPORT_RECEIPT_02.json'
receipt=json.loads(receipt_path.read_bytes())
assert receipt['state']=='PASS_EXACT_RAW_BYTES_IMPORTED'
records=[]
def put(source,target,role):
    raw=source.read_bytes()
    assert not target.exists() or target.read_bytes()==raw, str(target)
    target.parent.mkdir(parents=True,exist_ok=True)
    if not target.exists():target.write_bytes(raw)
    assert target.read_bytes()==raw
    records.append({'role':role,'source':str(source),'path':str(target.relative_to(REPO)),
                    'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()})
for row in receipt['files_verified']:
    rel=Path(row['path']); source=SOURCE/rel
    raw=source.read_bytes()
    assert len(raw)==row['bytes'] and hashlib.sha256(raw).hexdigest()==row['sha256']
    if rel.parts[0].startswith('ops-') or rel.name in {'push_mac_ops.py','align_and_retire_mac.py'}:
        target=PACKET/'ops-evidence/mac-raw-01'/rel
    else:target=PACKET/'actual-execution'/rel
    put(source,target,'actual_mac_file')
for path in sorted(ROOT.glob('*TOOL_OUTPUT.*')):
    put(path,PACKET/'actual-execution/tool-observations'/path.name,'actual_tool_observation')
put(ROOT/'FOCUS_03_LAUNCH_FAILURE.txt',PACKET/'actual-execution/tool-observations/FOCUS_03_LAUNCH_FAILURE.txt','actual_failed_launch')
put(receipt_path,PACKET/'actual-execution/import-01'/receipt_path.name,'verified_import_receipt')
for name in ('export_mac_execution_v2.py','import_mac_execution_v2.py'):
    put(ROOT/name,PACKET/'actual-execution/import-01'/name,'transport_driver')
for rel in ('native-diagnostic-01/progress.log','native-runtime-observation-01/sample.txt'):
    p=SOURCE/rel
    info=json.loads(p.with_name(p.name+'.compression.json').read_bytes())
    decoded=lzma.decompress(p.with_name(p.name+'.xz').read_bytes())
    # The exact original digest is recorded in the original compression receipt.
    assert hashlib.sha256(decoded).hexdigest() in json.dumps(info)
manifest={'schema':'PATH_REALIZATION_ACTUAL_EXECUTION_ARCHIVE_V1',
          'state':'PASS_EXACT_BYTES_ARCHIVED_NO_STATUS_REWRITE',
          'mac_files':len(receipt['files_verified']),'records':records,
          'current_frozen_source':'de7c7e287bd1b351ed3f790de58bfd71edf18df4013f7e5aaf2af55a6b3f6379',
          'acceptance':'SEPARATE_INDEPENDENT_EXECUTION_REGISTRATION_CANONICAL_AND_PUBLICATION_GATES',
          'historical_native01':'INTERRUPTED_FAIL_RETAINED_NOT_A_PASS',
          'large_diagnostic_files':'LOSSLESS_XZ_ORIGINAL_DIGEST_AND_DECOMPRESSION_VERIFIED'}
out=PACKET/'actual-execution/import-01/ARCHIVE_MANIFEST.json'
raw=(json.dumps(manifest,indent=2)+'\n').encode()
assert not out.exists() or out.read_bytes()==raw
out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(raw)
print(json.dumps({'state':manifest['state'],'mac_files':manifest['mac_files'],'archived_records':len(records),'manifest_sha256':hashlib.sha256(raw).hexdigest()}))
