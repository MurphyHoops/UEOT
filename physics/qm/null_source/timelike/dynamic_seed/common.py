"""New second-jet inputs only; inherited scientific programs are never imported."""
from __future__ import annotations
import argparse,hashlib,json,math
from pathlib import Path
from mpmath import iv
HERE=Path(__file__).resolve().parent
TIMELIKE=HERE.parent
REPO=HERE.parents[4]
iv.dps=90
INPUTS=[TIMELIKE/"joint_history/history.json",TIMELIKE/"joint_history/response.json",
        TIMELIKE/"physical_source/static_source.json",TIMELIKE/"correlated_static/correlations.json"]
DATA=[json.loads(p.read_text()) for p in INPUTS]
assert all(d["status"]=="PASS" for d in DATA)
HISTORY,RESPONSE,STATIC,CORRELATED=DATA
CASE=HISTORY["cases"]["unfiltered"]
def exact(v):
    if isinstance(v,float):
        n,d=v.as_integer_ratio()
        return iv.mpf(n)/d
    return iv.mpf(v)
def interval(lo,hi):return iv.mpf([exact(lo).a,exact(hi).b])
def box(v):return interval(v[0],v[1])
def outward(v):return [math.nextafter(float(v.a),-math.inf),math.nextafter(float(v.b),math.inf)]
def above(v,b=0):return bool(v.a>exact(b))
def below(v,b):return bool(v.b<exact(b))
X=box(CASE["x"])
A=box(CASE["A"])
N=box(CASE["thermal_occupation_per_oscillator"])
SPECTRAL=box(STATIC["reused_spectral_constant"])
D0=3/(32*iv.pi**2)
JN=4*iv.sqrt(3)*N/iv.pi**2
def B(x):return (SPECTRAL/4-iv.mpf(3)/160-(iv.log(x/4)+2*iv.euler)/64)/iv.pi**2
def CA(x):return 19+15*(iv.log(x/4)+2*iv.euler)
def manifest(script,extra=()):
    paths=INPUTS+[HERE/"common.py",HERE/script]+[HERE/p for p in extra]
    return {str(p.relative_to(REPO)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
def finish(script,payload,extra=()):
    assert __debug__,"Scientific assertions must remain enabled"
    ap=argparse.ArgumentParser(description=__doc__)
    group=ap.add_mutually_exclusive_group(required=True)
    group.add_argument("--write",action="store_true")
    group.add_argument("--check",action="store_true")
    args=ap.parse_args()
    payload.update(schema="ueot-dynamic-seed-"+Path(script).stem+"/1",status="PASS",
        source_sha256=manifest(script,extra),old_checkers_executed=0,
        mode_ODE_integrations=0,geometry_ODE_integrations=0)
    path=HERE/(Path(script).stem+".json")
    if args.write:path.write_text(json.dumps(payload,indent=2,sort_keys=True,ensure_ascii=False)+"\n")
    else:assert json.loads(path.read_text())==payload,"Certificate differs from saved result"
    print("PASS: "+Path(script).stem)
