"""Independent autonomous-preparation utilities; predecessor inputs are JSON/text only."""
from __future__ import annotations
import argparse,hashlib,json,math,sys
from pathlib import Path
from mpmath import iv
HERE=Path(__file__).resolve().parent
REPO=HERE.parents[6]
TIMELIKE=HERE.parents[2]
BASE="8bdeec29495bf5db2819704dee4e3daf58e6d135"
iv.dps=100
def require(ok,msg):
    if not ok:raise RuntimeError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def exact(v):
    if isinstance(v,float):
        n,d=v.as_integer_ratio();return iv.mpf(n)/d
    return iv.mpf(v)
def box(v):return iv.mpf([exact(v[0]).a,exact(v[1]).b])
def interval(a,b):return iv.mpf([exact(a).a,exact(b).b])
def above(x,v=0):return bool(x.a>exact(v))
def below(x,v):return bool(x.b<exact(v))
def outward(x):
    return [math.nextafter(float(x.a),-math.inf),math.nextafter(float(x.b),math.inf)]
def load(rel):
    d=json.loads((REPO/rel).read_text())
    require(d.get("status")=="PASS","Unaccepted frozen input: "+rel)
    return d
def finish(script,payload,inputs=(),proof=None):
    require(__debug__ and sys.flags.optimize==0,"Assertions enabled")
    ap=argparse.ArgumentParser();group=ap.add_mutually_exclusive_group(required=True)
    group.add_argument("--write",action="store_true");group.add_argument("--check",action="store_true")
    args=ap.parse_args();name=Path(script).stem
    paths=[HERE/script,HERE/"common.py",HERE/(proof or name.upper()+".md")]
    paths += [REPO/p for p in inputs]
    if (HERE/"model.py").exists():paths.append(HERE/"model.py")
    require(all(p.is_file() and not p.is_symlink() for p in paths),"Source file missing")
    payload.update(schema="ueot-autonomous-preparation-"+name+"/1",status="PASS",
      source_sha256={str(p.relative_to(REPO)):sha(p.read_bytes()) for p in sorted(set(paths))},
      verification_kind="exact algebra, outward interval checks, or explicitly tolerance-based floating-point regressions; analytic proofs stated separately",
      predecessor_scientific_modules_imported_or_executed=0,
      mode_ODE_integrations=0,geometry_ODE_integrations=0,
      full_field_Einstein_CTP_device_solution=False,physical_unification="OPEN")
    out=HERE/(name+".json")
    if args.write:out.write_text(json.dumps(payload,indent=2,ensure_ascii=False,sort_keys=True)+"\n")
    else:
        expected=json.loads(out.read_text())
        if expected!=payload:
            differences=[]
            def compare(a,b,path=""):
                if len(differences)>=10:return
                if isinstance(a,dict) and isinstance(b,dict):
                    for key in sorted(set(a)|set(b)):
                        if key not in a or key not in b:
                            differences.append({"path":path+"/"+key,"expected":a.get(key),"actual":b.get(key)})
                        else:compare(a[key],b[key],path+"/"+key)
                elif isinstance(a,list) and isinstance(b,list) and len(a)==len(b):
                    for i,(x,y) in enumerate(zip(a,b)):compare(x,y,path+"/"+str(i))
                elif a!=b:differences.append({"path":path,"expected":a,"actual":b})
            compare(expected,payload)
            print(json.dumps({"result_mismatches":differences},ensure_ascii=False),file=sys.stderr)
            raise RuntimeError("Source-bound result differs: "+name)
    print("PASS: "+name)
