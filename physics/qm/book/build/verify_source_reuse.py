#!/usr/bin/env python3
"""Bind reused v31.10 receipts to executed and publication bytes; no heavy rerun."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess

REPO = Path(__file__).resolve().parents[4]
SOURCE = '4e5de046ad59eaa37856027af6547ca26bdea1c2'
TESTED_MAIN = 'dee9bfa68c5fc60bed2853356c28011b0d3c53a0'
PUBLICATION_BASE = '925e3a8a411c0b1bab99dd9150bf005893656140'
INITIAL_BASE = '3d443ec29eb17af1fc00699a74e2d42d73516d81'


def git(*args):
    return subprocess.check_output(['git',*args],cwd=REPO)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def identity(path):
    data=(REPO/path).read_bytes()
    return {'path':path,'sha256':sha(data),'bytes':len(data)}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    proof_path='physics/qm/kernel/evidence/v31.10/source-manifest.json'
    runtime_path='physics/qm/kernel/evidence/v31.10/runtime/execution_receipt.json'
    integration_path='physics/qm/kernel/evidence/v31.10/integration-verification.json'
    manifest=json.loads((REPO/proof_path).read_text())
    runtime=json.loads((REPO/runtime_path).read_text())
    entries=[dict(x,kind='proof_or_configuration') for x in manifest['sources']]
    entries += [{'path':'physics/qm/conditioning/'+name,'sha256':value,'kind':'runtime'}
                 for name,value in runtime['source_sha256'].items()]
    assert len(manifest['sources'])==155 and len(runtime['source_sha256'])==9
    stages={'scientific_source':SOURCE,'tested_main':TESTED_MAIN,'publication_base':PUBLICATION_BASE}
    checks=[]
    for entry in entries:
        path=entry['path']
        actual={name:sha(git('show',f'{ref}:{path}')) for name,ref in stages.items()}
        actual['worktree']=sha((REPO/path).read_bytes())
        assert all(x==entry['sha256'] for x in actual.values()), (path,actual)
        checks.append({'path':path,'kind':entry['kind'],'expected_sha256':entry['sha256'],
                       'actual_sha256':actual,'status':'PASS'})
    trees={name:git('rev-parse',ref+'^{tree}').decode().strip() for name,ref in stages.items()}
    assert trees['scientific_source']==trees['tested_main']
    core={name:git('ls-tree','-r',ref,'--','formalization/ueot-core')
          for name,ref in {**stages,'initial_base':INITIAL_BASE}.items()}
    assert len(set(core.values()))==1
    tracked_core_count=len(core['initial_base'].splitlines())
    assert tracked_core_count==5033
    protected_changes=git('diff',PUBLICATION_BASE,'--name-only','--','.',
                          ':(exclude)physics/qm/book/**').decode().splitlines()
    assert not protected_changes, protected_changes
    receipt={'schema':'ueot_physics.scientific_source_reuse.v2','status':'PASS',
             'checked_at_utc':datetime.now(timezone.utc).isoformat(),
             'scientific_release':'v31.10','publication_edition':'3.7',
             'commits':stages,'trees':trees,'initial_authoring_base':INITIAL_BASE,
             'proof_input_count':155,'runtime_input_count':9,'distinct_input_count':len({x['path'] for x in entries}),
             'source_set_sha256':manifest['source_set_sha256'],
             'tracked_core_blob_count_unchanged':tracked_core_count,
             'consumed_core_sources':sum(x['path'].startswith('formalization/ueot-core/') for x in manifest['sources']),
             'protected_paths_modified':protected_changes,
             'reused_receipts':[identity(x) for x in [proof_path,runtime_path,integration_path,
                 'physics/qm/kernel/evidence/v31.10/lean-verification.json',
                 'physics/qm/kernel/evidence/v31.10/ci/pr-42966223125/verification.json',
                 'physics/qm/kernel/evidence/v31.10/ci/main-42967294067/verification.json']],
             'source_checks':checks,'lean_or_kernel_rerun':False,'new_hardware_data':False,
             'scope':'Exact input identity plus existing execution evidence. No new heavy proof or kernel build is run locally. Automatic repository CI is separately reported when actually observed.'}
    args.output.write_text(json.dumps(receipt,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({k:receipt[k] for k in ['status','proof_input_count','runtime_input_count','distinct_input_count','tracked_core_blob_count_unchanged','protected_paths_modified']}))


if __name__=='__main__':
    main()
