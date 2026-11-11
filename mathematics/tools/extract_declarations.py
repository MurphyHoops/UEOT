"""Reproduce the static P-ID declaration inventory. No Lean compilation is performed."""
import argparse,json,re,subprocess
from pathlib import Path
BASE='3d443ec29eb17af1fc00699a74e2d42d73516d81'
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--repo',type=Path,default=Path(__file__).resolve().parents[2])
parser.add_argument('--base',default=BASE,help='Git snapshot used for the source-registration document')
parser.add_argument('--output-dir',type=Path)
args=parser.parse_args()
ROOT=args.repo.resolve()
OUT=(args.output_dir or ROOT/'mathematics/review/BILINGUAL_EDITION_2026-11-11').resolve()
OUT.mkdir(parents=True,exist_ok=True)
sources=subprocess.check_output(['git','show',args.base+':mathematics/UEOT_MATHEMATICS_SOURCES.md'],cwd=ROOT).decode('utf-8')
links=dict(re.findall(r'\[(UEOT\.[^\]]+)\]\((\.\./formalization/[^)]+\.lean)\)',sources))
ledger=json.loads((ROOT/'formalization/ueot-core/docs/compression/COMPRESSION_LEDGER.yaml').read_text())
paths=list((ROOT/'formalization/ueot-core/UEOT').rglob('*.lean'))
cache={p:p.read_text().splitlines() for p in paths}
def candidates(path,leaf):
 result=[]
 for i,line in enumerate(cache[path]):
  if re.search(r'\b(?:theorem|lemma|def|abbrev)\s+(?:[\w.]+\.)?'+re.escape(leaf)+r'(?=\s|\{|\[|\(|:|$)',line):
   block='\n'.join(cache[path][i:i+200]);depth=0;cut=None
   for j,ch in enumerate(block):
    if ch in '([{⦃':depth+=1
    if ch in ')]}⦄':depth-=1
    if block[j:j+2]==':=' and depth==0 and not re.search(r'\b(?:let|letI|have)\s+[^\n]*$', block[:j]):cut=j;break
   result.append({'path':str(path.relative_to(ROOT)),'line':i+1,'header':block[:cut].rstrip() if cut is not None else block})
 return result
records=[]
for pid,rec in ledger['audit_records'].items():
 for name in rec['lean_theorems']:
  entry=(ROOT/'mathematics'/links[name]).resolve();leaf=name.split('.')[-1]
  found=candidates(entry,leaf)
  if not found:
   found=[c for p in paths for c in candidates(p,leaf)]
  if name=='UEOT.V3.DiffusionHJBVerification.p_ctl_03':found=found[-1:]
  assert len(found)==1,(pid,name,len(found))
  records.append({'pid':pid,'name':name,'entry_path':str(entry.relative_to(ROOT)),'candidates':found})
(OUT/'LEAN_DECLARATION_EVIDENCE.json').write_text(json.dumps(records,ensure_ascii=False,indent=2)+'\n')
md=['# Static Lean declaration evidence','',f'Registry snapshot: `{args.base}`. Current unchanged Lean source is read from the repository; see SOURCE_IDENTITY_REUSE_AUDIT.md for byte identity.','',f'{len(records)} registrations / {len(set(r["name"] for r in records))} distinct endpoints. Static source extraction only; namespace and section variables and structure fields are part of the full type. This document is not a new Lean elaboration or build receipt. Source-facing entry modules may re-export declarations; the actual defining file is recorded.','']
for r in records:
 md.extend([f'## {r["pid"]}: `{r["name"]}`','',f'Entry module: `{r["entry_path"]}`',''])
 for c in r['candidates']:md.extend([f'Defining file: `{c["path"]}`, source line {c["line"]}.','```lean',c['header'],'```',''])
(OUT/'LEAN_DECLARATION_EVIDENCE.md').write_text('\n'.join(md)+'\n')
print({'registrations':len(records),'distinct_endpoints':len(set(r['name'] for r in records)),'missing':[r['name'] for r in records if not r['candidates']],'multiple_candidates':[(r['name'],len(r['candidates'])) for r in records if len(r['candidates'])>1]})
