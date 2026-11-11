#!/usr/bin/env python3
"""Read-only source/receipt identity comparison; executes no Lean or cached proof code."""
import argparse,datetime,hashlib,importlib.util,json,re,subprocess,sys
sys.dont_write_bytecode = True  # Do not create caches beside frozen source-audit helpers.
from pathlib import Path
ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--repo',type=Path,default=Path(__file__).resolve().parents[2]);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--evidence-dir',type=Path);a=ap.parse_args();R=a.repo.resolve();C=R/'formalization/ueot-core';U=C/'docs/compression/theory_completion/unified_closure';W=(a.evidence_dir or R/'mathematics/review/BILINGUAL_EDITION_2026-11-11').resolve()
sha=lambda b:hashlib.sha256(b).hexdigest()
def file_sha(p):return sha(p.read_bytes()) if p.is_file() else None
def git(*args):return subprocess.run(['git',*args],cwd=R,capture_output=True)
def normalized_path(p):
 p=str(p)
 if 'formalization/ueot-core/' in p:return p[p.index('formalization/ueot-core/'):]
 if p.startswith(('UEOT/','UEOT.lean','docs/','lean-toolchain','lake-','lakefile.lean')):return 'formalization/ueot-core/'+p
 if '/' not in p and p.endswith('.lean'):
  candidates=list((C/'UEOT').rglob(p))
  if len(candidates)!=1:raise ValueError('Ambiguous production basename '+p)
  return candidates[0].relative_to(R).as_posix()
 return p
def compare(path,expected):
 path=normalized_path(path);got=file_sha(R/path)
 return {'path':path,'recorded_sha256':expected,'actual_sha256':got,'matches':got==expected}
head=git('rev-parse','HEAD').stdout.decode().strip();baseline='1e2a3924ef31b5dca589dca69c3838fc355b8850'
# Reuse the audited lexical helpers only; the historical EXPECTED_FILES is not changed.
helper=U/'core_theory_closure_v1/checks/inspect_public_source_v2.py';spec=importlib.util.spec_from_file_location('legacy_source_parser',helper);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
paths=[C/'UEOT.lean',*sorted((C/'UEOT').rglob('*.lean'))];graph={};prod=[]
for p in paths:
 rel=p.relative_to(C).as_posix();module=rel[:-5].replace('/','.');data=p.read_bytes();graph[module]=m.imports(m.mask(data.decode()));prod.append({'module':module,'path':rel,'bytes':len(data),'sha256':sha(data)})
def closure(seeds):
 todo=list(seeds);seen=set()
 while todo:
  x=todo.pop()
  if x in seen:continue
  if x not in graph:raise ValueError('Missing internal module '+x)
  seen.add(x);todo.extend(y for y in graph[x] if y=='UEOT' or y.startswith('UEOT.'))
 return seen
recs=json.loads((W/'LEAN_DECLARATION_EVIDENCE.json').read_text());definition_paths=sorted({x['candidates'][0]['path'] for x in recs});seeds=[p.removeprefix('formalization/ueot-core/')[:-5].replace('/','.') for p in definition_paths];dep=closure(seeds);baseline_rows=[]
for x in sorted(dep):
 p='formalization/ueot-core/'+x.replace('.','/')+'.lean';old=git('show',baseline+':'+p)
 baseline_rows.append({'path':p,'source_definition':p in definition_paths,'promotion_sha256':sha(old.stdout) if old.returncode==0 else None,'actual_sha256':file_sha(R/p),'matches':old.returncode==0 and old.stdout==(R/p).read_bytes()})
oldp=U/'core_theory_closure_v1/checks/PUBLIC_SOURCE_AUDIT.v2.json';old=json.loads(oldp.read_text());old_rows=[compare(x['path'],x['sha256']) for x in old['files']];oldset={x['path'] for x in old['files']};curset={x['path'] for x in prod}
buildp=U/'core_theory_closure_v1/checks/INTEGRATION_BUILD.json';build=json.loads(buildp.read_text());buildlog=buildp.with_suffix('.log');delivery=json.loads((U/'core_theory_closure_v1/DELIVERY.json').read_text());delivery_by={x['path']:x for x in delivery['files']}
reusep=U/'core_theory_closure_v1/review/EXISTING_RECEIPT_REUSE_REVIEW.json';reuse=json.loads(reusep.read_text());module_receipts=[]
for x in reuse['existing_module_compile_receipts']:
 p=U/'core_theory_closure_v1'/x['existing_receipt'];j=json.loads(p.read_text());s=compare('formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/'+x['file'],x['source_sha256']);s.update({'receipt':p.relative_to(R).as_posix(),'receipt_hash_matches_prior_review':file_sha(p)==x['receipt_sha256'],'recorded_returncode':j.get('returncode'),'recorded_source_matches_receipt':j.get('sha256')==x['source_sha256'],'log_exists':(p.with_suffix('.log')).is_file()});module_receipts.append(s)
gp=U/'core_growth_classification_v1';growth=json.loads((gp/'LEAN_VALIDATION.json').read_text());grows=[]
for x in growth['checked_modules']:
 s=compare(x['source'],x['source_sha256']);rp=gp/x['receipt'];j=json.loads(rp.read_text());lp=gp/x['log'];s.update({'module':x['module'],'receipt':rp.relative_to(R).as_posix(),'receipt_sha256':file_sha(rp),'log':lp.relative_to(R).as_posix(),'log_sha256_current':file_sha(lp),'log_exists':lp.is_file(),'recorded_exit_code':j.get('exit_code'),'receipt_matches_source':j.get('source_sha256')==x['source_sha256']});grows.append(s)
bind=json.loads((gp/'SOURCE_BINDING.json').read_text());bindrows=[compare(p,s) for field in ['old_execution_sources_byte_identical','unchanged_dependency_toolchain_and_book_builder_files'] for p,s in bind[field].items()]
# Direct hashes in all package SOURCE_VALIDATION records are source identity evidence,
# independently of their historical OPEN/PENDING stage labels.
packs=[]
for p in sorted(U.glob('*/SOURCE_VALIDATION.json')):
 j=json.loads(p.read_text());pairs={}
 v=j.get('source_sha256',{})
 if isinstance(v,dict):
  for path,h in v.items():
   if path.endswith('.lean') and isinstance(h,str) and re.fullmatch('[0-9a-f]{64}',h):pairs[path]=h
 v=j.get('proof_bytes_verified',[])
 if isinstance(v,list):
  for x in v:
   if isinstance(x,dict) and str(x.get('path','')).endswith('.lean') and re.fullmatch('[0-9a-f]{64}',str(x.get('sha256',''))):pairs[x['path']]=x['sha256']
 if pairs:
  rows=[compare(path,h) for path,h in sorted(pairs.items())];packs.append({'package':p.parent.name,'receipt':p.relative_to(R).as_posix(),'receipt_sha256':file_sha(p),'source_files':len(rows),'matched':sum(x['matches'] for x in rows),'historical_state':{k:j[k] for k in ['whole_theory','whole_goal','public_main_adoption','scientific_scope'] if k in j},'files':rows})
# Three later decision packages have different identity-record formats.
extras=[]
for name,rel in [('joint_decision_closure_v1','actual-execution/lean-cached-final-01/SOURCE_AFTER.json'),('joint_decision_closure_v1','actual-execution/lean-final-02/SOURCE_AFTER.json'),('decision_representation_closure_v1','checks/CORE_SOURCE_IDENTITY.json'),('mechanism_decision_closure_v1','checks/CORE_SOURCE_IDENTITY.json')]:
 p=U/name/rel;j=json.loads(p.read_text());raw=j.get('files',j);pairs=raw if isinstance(raw,dict) else {x['path']:x['sha256'] for x in raw};rows=[compare(path,h) for path,h in pairs.items() if path.endswith('.lean')];extras.append({'package':name,'receipt':p.relative_to(R).as_posix(),'source_files':len(rows),'matched':sum(x['matches'] for x in rows),'files':rows})
joint_compile=json.loads((U/'joint_decision_closure_v1/checks/FINAL_MODULE_COMPILE.json').read_text())
joint_compile_rows=[]
for x in joint_compile:
 row=compare(x['module']+'.lean',x['source_sha256']);row['recorded_exit_code']=x['exit_code'];joint_compile_rows.append(row)
axiom_log=(gp/growth['checked_modules'][-1]['log']).read_text()
axiom_rows={name:[v.strip() for v in vals.split(',') if v.strip()] for name,vals in re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]",axiom_log,re.S)}
config=[compare(p,bind['unchanged_dependency_toolchain_and_book_builder_files'][p]) for p in ['formalization/ueot-core/lean-toolchain','formalization/ueot-core/lake-manifest.json','formalization/ueot-core/lakefile.lean']]
lm=json.loads((C/'lake-manifest.json').read_text());mathlib=next(x for x in lm['packages'] if x['name']=='mathlib')
for x in config:
 config_old=git('show',baseline+':'+x['path']);x['promotion_sha256']=sha(config_old.stdout) if config_old.returncode==0 else None;x['matches_promotion']=config_old.returncode==0 and config_old.stdout==(R/x['path']).read_bytes()
result={
 'scope':'READ_ONLY_SOURCE_HASH_AND_RECORDED_RECEIPT_REUSE_NOT_NEW_LEAN_EXECUTION',
 'observed_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'snapshot_commit':head,
 'new_Lean_execution':False,'new_CI_execution':False,
 'protected_worktree_diff':git('diff','--name-only','HEAD','--','formalization/ueot-core','mathematics/source/core-v3.0','core/specifications').stdout.decode().splitlines(),
 'frozen_source':compare('mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md','ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303'),
 'toolchain':(C/'lean-toolchain').read_text().strip(),'mathlib_commit':mathlib['rev'],'config_identity':config,
 'frozen_106':{'promotion_commit':baseline,'promotion_ci_run_recorded_in_ledger':'36249418600','promotion_is_ancestor':git('merge-base','--is-ancestor',baseline,head).returncode==0,'P_count':len({x['pid'] for x in recs}),'declaration_count':len(recs),'definition_files':len(definition_paths),'transitive_UEOT_source_files':len(dep),'all_definition_and_transitive_files_identical_to_promotion':all(x['matches'] for x in baseline_rows),'files':baseline_rows},
 'PR444':{'receipt':buildp.relative_to(R).as_posix(),'recorded_exit_code':build['exit_code'],'recorded_mode':build['build_mode'],'recorded_jobs':build['reported_jobs'],'recorded_observed_at':build['completed_observed_at'],'build_receipt_matches_delivery':file_sha(buildp)==delivery_by[buildp.relative_to(R).as_posix()]['sha256'],'build_log_matches_recorded_hash':file_sha(buildlog)==build['log_sha256'],'static_receipt_matches_delivery':file_sha(oldp)==delivery_by[oldp.relative_to(R).as_posix()]['sha256'],'static_manifest_digest_matches':sha(json.dumps(old['files'],sort_keys=True,separators=(',',':')).encode())==old['source_manifest_sha256'],'historical_source_count':len(old_rows),'matched_historical_sources':sum(x['matches'] for x in old_rows),'mismatches':[x for x in old_rows if not x['matches']],'new_production_paths':sorted(curset-oldset),'removed_production_paths':sorted(oldset-curset),'files':old_rows,'individual_module_receipts':module_receipts},
 'PR447':{'recorded_lean_version':growth['lean_version'],'recorded_full_historical_build_rerun':growth['full_historical_build_rerun'],'axiom_endpoint_count':len(growth['checked_axiom_endpoints']),'recorded_all_listed_axioms_standard':growth['all_listed_axioms_standard'],'checks':grows,'raw_axiom_log_matches_structured':axiom_rows==growth['checked_axiom_endpoints'],'unchanged_source_and_configuration_binding':bindrows},
 'historical_source_packages':packs,'decision_package_identity_records':extras,'PR441_final_module_compile':joint_compile_rows,
 'current_production':{'files':len(prod),'bytes':sum(x['bytes'] for x in prod),'public_UEOT_reachable':len(closure(['UEOT'])),'manifest_sha256':sha(json.dumps(prod,sort_keys=True,separators=(',',':')).encode())},
 'limits':['Recorded exit codes are historical facts read from repository receipts, not fresh kernel execution.','SHA equality binds source bytes; it does not by itself prove a theorem or execute a build.','The PR444 whole graph is superseded by three PR447 modules and one changed entry; the historical full-build receipt is not an exact graph receipt for the current whole graph.','Axiom print conclusions remain confined to their listed endpoints; the two disclosed PR443 native_decide endpoints retain their original scope.','No historical PDF or source-book receipt certifies the new bilingual PDFs.']
}
a.output.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'source_commit':head,'frozen106_definition_files':len(definition_paths),'frozen106_transitive_files':len(dep),'frozen106_all_bytes_match':result['frozen_106']['all_definition_and_transitive_files_identical_to_promotion'],'PR444_matched':result['PR444']['matched_historical_sources'],'PR444_changed':len(result['PR444']['mismatches']),'PR447_checked_sources':len(grows),'PR447_all_match':all(x['matches'] and x['receipt_matches_source'] and x['recorded_exit_code']==0 and x['log_exists'] for x in grows),'historical_packages':len(packs),'historical_package_sources':sum(x['source_files'] for x in packs),'historical_package_mismatches':sum(x['source_files']-x['matched'] for x in packs),'current_production':result['current_production'],'protected_worktree_diff':result['protected_worktree_diff']},ensure_ascii=False))
