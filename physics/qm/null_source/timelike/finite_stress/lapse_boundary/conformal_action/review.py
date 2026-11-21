"""Check new-cohort boundaries, certificates, immutable audit identities and timing."""
import ast,json,re,subprocess,sys
from datetime import datetime
from pathlib import Path
from common import HERE,REPO,BASE,sha,require,finish
tree=ast.parse((HERE/'run_verification.py').read_text())
entries=None
for node in tree.body:
    if isinstance(node,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='ENTRIES' for x in node.targets):
        entries=ast.literal_eval(node.value)
require(entries and entries[-1]=='review','entrypoint list')
allowed={'__future__','common','model','ast','json','re','subprocess','sys','datetime','pathlib','argparse','hashlib','math','os','tempfile','time','concurrent','numpy','scipy','sympy','mpmath','fractions','functools','itertools'}
for p in HERE.glob('*.py'):
    if p.name in {'run_verification.py'}:continue
    for node in ast.walk(ast.parse(p.read_text())):
        if isinstance(node,ast.Import):
            for alias in node.names:require(alias.name.split('.')[0] in allowed,'forbidden import '+alias.name)
        if isinstance(node,ast.ImportFrom):
            require(node.level==0 and (node.module or '').split('.')[0] in allowed,
                    'forbidden relative/from import '+str(node.module))
        if isinstance(node,ast.Call) and isinstance(node.func,ast.Name):
            require(node.func.id not in {'eval','exec','__import__'},'dynamic execution forbidden')
for name in entries[:-1]:
    d=json.loads((HERE/(name+'.json')).read_text())
    require(d['status']=='PASS' and d['physical_unification']=='OPEN','science scope '+name)
    require(d['predecessor_scientific_modules_imported_or_executed']==0,'old execution')
    for rel,h in d['source_sha256'].items():
        p=REPO/rel
        require(p.is_file() and not p.is_symlink() and sha(p.read_bytes())==h,'stale binding '+rel)
audit=json.loads((HERE/'source_audits.json').read_text())
expected={'/root/a_joint_propagation','/root/b_constraint_kernel','/root/c_prepared_record'}
require(set(audit['reviewers'])==expected and audit['native_read_only_agents']==3,'reviewer contract')
seen=set();identities=0
for row in audit['records']:
    require(row['reviewer'] in expected and re.fullmatch('[0-9a-f]{40}',row['commit']),'audit identity')
    require(row['status'] in {'PASS','FINDINGS','RESOLVED'},'audit status')
    for rel,h in row['files'].items():
        b=subprocess.check_output(['git','show',row['commit']+':'+rel],cwd=REPO)
        require(sha(b)==h,'immutable audit file mismatch '+rel)
        identities+=1
    if row['status'] in {'PASS','RESOLVED'}:seen.add(row['reviewer'])
if audit['final_audit_complete']:
    require(seen==expected,'final review missing a reviewer')
    require(all(x['status']=='RESOLVED' for x in audit.get('findings',[])),
            'unresolved final source finding')
timing=json.loads((HERE/'session_timing.json').read_text())
require(timing['start_utc']=='2026-11-21T18:02:22Z' and not timing['prior_session_time_counted'],'session origin')
if timing['end_utc'] is not None:
    parse=lambda x:datetime.fromisoformat(x.replace('Z','+00:00'))
    elapsed=(parse(timing['end_utc'])-parse(timing['start_utc'])).total_seconds()
    require(elapsed==timing['elapsed_seconds'] and timing['minimum_duration_met']==(elapsed>=10800),'timing arithmetic')
if timing['status']=='COMPLETE':require(timing['minimum_duration_met'] and audit['final_audit_complete'],'final session gates')
finish('review.py',{'source_bindings_verified':len(entries)-1,'native_agents':3,
 'immutable_review_records':len(audit['records']),'immutable_file_identities':identities,
 'final_audit_complete':audit['final_audit_complete'],'session_status':timing['status'],
 'external_human_peer_review':False,'machine_formal_proof':False},
 inputs=[str((HERE/'source_audits.json').relative_to(REPO)),str((HERE/'session_timing.json').relative_to(REPO))])
