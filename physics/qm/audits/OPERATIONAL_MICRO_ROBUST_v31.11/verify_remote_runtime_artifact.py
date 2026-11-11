#!/usr/bin/env python3
"""Read-only verification of downloaded CI artifacts against an existing Git commit.

The Git commit must already be available locally. This verifies archive/source
identity and observed execution metadata, not the truth of paper theorems.
"""
from pathlib import Path
import argparse,zipfile,hashlib,json,subprocess,datetime,sys
p=argparse.ArgumentParser();p.add_argument('--zip',required=True);p.add_argument('--sha256',required=True);p.add_argument('--head',required=True);p.add_argument('--run',required=True,type=int);p.add_argument('--artifact',required=True,type=int);p.add_argument('--output',required=True);a=p.parse_args();root=Path(__file__).resolve().parents[4];src=Path(a.zip);sha=hashlib.sha256(src.read_bytes()).hexdigest();assert sha==a.sha256
z=zipfile.ZipFile(src);prefix='ueot-qm-operational-micro-robust/';r=json.loads(z.read(prefix+'execution_receipt.json'))
def at_commit(path):return subprocess.check_output(['git','show',a.head+':'+path],cwd=root)
for x in r['inputs']:assert hashlib.sha256(at_commit(x['path'])).hexdigest()==x['sha256'],x['path']
for x in r['outputs']+[c['log'] for c in r['commands']]:
 archive=x['path'].removeprefix('/tmp/');assert hashlib.sha256(z.read(archive)).hexdigest()==x['sha256'],archive
assert r['status']=='PASS' and len(r['commands'])==7 and all(c['exit_code']==0 for c in r['commands'])
assert r['schema']=='ueot-qm.runtime-increment/2' and r['execution_actor']=='GitHub Actions runner'
ctx=r['execution_context'];assert ctx['provider']=='github_actions' and ctx['observed_git_head']==a.head and ctx['workflow']['GITHUB_RUN_ID']==str(a.run) and ctx['workflow']['GITHUB_JOB']=='runtime' and ctx['workflow']['GITHUB_REPOSITORY']=='MurphyHoops/UEOT'
b=json.loads(z.read('ueot-qm-book3.8-increment.json'));assert b['status']=='PASS'
for path,expected in b['consumed_sha256'].items():assert hashlib.sha256(at_commit(path)).hexdigest()==expected,path
old=json.loads(z.read('ueot-qm-finite-conditioning/execution_receipt.json'));assert old['status']=='PASS'
for name,expected in old['source_sha256'].items():assert hashlib.sha256(at_commit('physics/qm/conditioning/'+name)).hexdigest()==expected,name
for gate in old['gates']:assert gate['returncode']==0 and hashlib.sha256(z.read('ueot-qm-finite-conditioning/'+gate['log'])).hexdigest()==gate['log_sha256']
k=json.loads(z.read('ueot-qm-runtime-verification.json'));assert k['status']=='PASS' and not k['failures'] and not k['errors']
for x in k['sources']:assert hashlib.sha256(at_commit('physics/qm/kernel/'+x['path'])).hexdigest()==x['sha256'],x['path']
d={'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'command':sys.argv,'schema':'ueot-qm.remote-runtime-inspection/2','observed_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','run_id':a.run,'artifact_id':a.artifact,'workflow_url':'https://github.com/MurphyHoops/UEOT/actions/runs/'+str(a.run),'scientific_head':a.head,'artifact_sha256':sha,'runtime_receipt_sha256':hashlib.sha256(z.read(prefix+'execution_receipt.json')).hexdigest(),'execution_context':ctx,'input_hashes_matched_to_exact_remote_commit':len(r['inputs']),'output_hashes_matched_in_archive':len(r['outputs']),'command_logs_matched':len(r['commands']),'all_seven_commands_passed':True,'bilingual_increment_status':b['status'],'bilingual_increment_inputs_matched':len(b['consumed_sha256']),'inherited_conditioning_status':old['status'],'inherited_kernel_test_methods':k['test_methods_run'],'inherited_kernel_status':k['status'],'new_hardware_data':False,'scope':'Actual archived runtime outputs, logs, source bytes and GitHub execution identity; does not infer paper theorems or device evidence'}
Path(a.output).write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d))
