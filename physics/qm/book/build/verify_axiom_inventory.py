#!/usr/bin/env python3
"""Read-only verification of the book's historical/new named-axiom inventories.
This checks names and order, not the outcome of executing #print axioms.
"""
import argparse,hashlib,json,pathlib,re,subprocess
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--book-dir',required=True);p.add_argument('--repo',required=True)
p.add_argument('--commit',default='925e3a8a411c0b1bab99dd9150bf005893656140')
p.add_argument('--initial-commit',default='3d443ec29eb17af1fc00699a74e2d42d73516d81')
p.add_argument('--output',required=True);a=p.parse_args()
rel='formalization/ueot-qm/scripts/AxiomAudit.lean'
def read(c):return subprocess.check_output(['git','-C',a.repo,'show',c+':'+rel])
def sha(b):return hashlib.sha256(b).hexdigest()
def script_names(b):return re.findall(r'^#print axioms\s+(\S+)\s*$',b.decode(),re.M)
def section(text,n):
 m=re.search(r'^## F\.'+str(n)+r'\b.*$',text,re.M)
 if not m:raise ValueError('missing F.'+str(n))
 tail=text[m.end():];end=re.search(r'^## ',tail,re.M)
 return tail[:end.start()] if end else tail

def book_names(text,n):
 part=section(text,n)
 ast=json.loads(subprocess.check_output(['pandoc','-f','markdown+tex_math_dollars','-t','json'],input=part.encode()))
 # F.3 and F.5 contain text fences consisting only of fully qualified names.
 names=[]
 for block in ast['blocks']:
  if block['t']=='CodeBlock':
   for line in block['c'][1].splitlines():
    if not line.strip():continue
    if not re.fullmatch(r'\w[\w.\u2032\u0027]*',line) or '.' not in line:raise ValueError('unexpected inventory code line '+repr(line))
    names.append(line)
 return names
raw=read(a.commit);initial=read(a.initial_commit);current_names=script_names(raw);old_names=script_names(initial);books={}
for lang,fn in [('zh','UEOT_PHYSICS.md'),('en','UEOT_PHYSICS.en.md')]:
 path=pathlib.Path(a.book_dir).resolve()/fn;data=path.read_bytes();txt=data.decode();old=book_names(txt,3);new=book_names(txt,5);names=old+new
 books[lang]={'path':str(path),'sha256':sha(data),'count':len(names),'unique':len(set(names)),'source_order_equal':names==current_names,'old_prefix_count':len(old),'old_prefix_equal':old==old_names,'new_f5_count':len(new),'new_f5_exact_suffix':new==current_names[len(old_names):],'names':names}
ok=len(current_names)==1285 and len(old_names)==1123 and all(b['count']==1285 and b['unique']==1285 and b['source_order_equal'] and b['old_prefix_equal'] and b['new_f5_count']==162 and b['new_f5_exact_suffix'] for b in books.values())
r={'schema':'ueot_physics.named_axiom_inventory_identity.v1','scope':'Static identity/order of printed named axiom requests, not execution of those requests or a new proof receipt','commit':a.commit,'initial_commit':a.initial_commit,'source':{'path':rel,'sha256':sha(raw),'count':len(current_names),'names':current_names},'initial_source':{'sha256':sha(initial),'count':len(old_names)},'books':books,'status':'PASS' if ok else 'FAIL'}
pathlib.Path(a.output).write_text(json.dumps(r,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':r['status'],'source_count':len(current_names),'books':{k:{kk:vv for kk,vv in v.items() if kk!='names'} for k,v in books.items()}},indent=2))
raise SystemExit(0 if ok else 1)
