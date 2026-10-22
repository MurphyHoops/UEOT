#!/usr/bin/env python3
from pathlib import Path
import argparse,datetime,hashlib,json,subprocess,time
parser=argparse.ArgumentParser();parser.add_argument('--execute',action='store_true');args=parser.parse_args()
repo=Path('/workspace/scratch/534b0448126c/ueot-core-next')
tmp=Path('/workspace/scratch/534b0448126c/tmp/core-path-realization-20261022')
packet='formalization/ueot-core/docs/compression/theory_completion/unified_closure/path_realization_v1'
out=tmp/('registration-execution-01' if args.execute else 'registration-check-01')
assert not out.exists()
if args.execute:
    review=json.loads((repo/packet/'independent/ACTUAL_EXECUTION_REVIEW.json').read_bytes())
    assert review['state']=='CLEAR' and review['scope']=='FROZEN02_ACTUAL_FULL_BUILD_NATIVE_TWO_PASS_AND_EXACT_ARCHIVE'
    assert review['binding']['source_tree_sha256']=='de7c7e287bd1b351ed3f790de58bfd71edf18df4013f7e5aaf2af55a6b3f6379'
cmd=['python3','-B',str(repo/packet/'native_protocol/register_overlay.py'),
 '--repo',str(repo),'--base-ref','d503586107974c56e0773b4ea106b41a7d144b43',
 '--frozen-inputs',str(tmp/'FROZEN_INPUTS_FINAL_02.json'),
 '--native-output',str(tmp/'mac-import-01/native-02'),
 '--build-receipt',str(tmp/'mac-import-01/full-build-02/FULL_BUILD_RECEIPT.json'),
 '--archive-relative',packet+'/actual-execution/native-02']
if not args.execute:cmd.append('--check-only')
out.mkdir();(out/'driver.py').write_bytes(Path(__file__).read_bytes())
started=datetime.datetime.now(datetime.timezone.utc).isoformat();begin=time.monotonic()
result=subprocess.run(cmd,cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(out/'run.log').write_bytes(result.stdout)
receipt={'state':'PASS' if result.returncode==0 else 'FAIL','command':cmd,'cwd':str(repo),'started_at':started,'seconds':time.monotonic()-begin,'exit_code':result.returncode,'log_sha256':hashlib.sha256(result.stdout).hexdigest(),'mode':'REGISTER_METADATA' if args.execute else 'CHECK_ONLY_NO_WRITES'}
if result.returncode==0:receipt['result']=json.loads(result.stdout)
(out/'RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
if result.returncode:print(result.stdout.decode(errors='replace'))
raise SystemExit(result.returncode)
