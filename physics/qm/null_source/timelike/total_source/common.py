"""New total-source certificates; only frozen JSON inputs are read."""
from __future__ import annotations
import argparse,hashlib,json,math
from pathlib import Path
from mpmath import iv
HERE=Path(__file__).resolve().parent
TIMELIKE=HERE.parent
REPO=HERE.parents[4]
iv.dps=120
INPUTS=[
 TIMELIKE/"joint_history/history.json",
 TIMELIKE/"physical_source/static_source.json",
 TIMELIKE/"nonlinear_history/kernels.json",
 TIMELIKE/"dynamic_inverse/causal_inverse.json",
 TIMELIKE/"finite_local/invariant_preparation.json"]
HISTORY,STATIC,KERNELS,CAUSAL,PREPARATION=[json.loads(p.read_text()) for p in INPUTS]
assert all(d["status"]=="PASS" for d in [HISTORY,STATIC,KERNELS,CAUSAL,PREPARATION])
CASE=HISTORY["cases"]["unfiltered"]
def exact(v):
    if isinstance(v,float):
        n,d=v.as_integer_ratio();return iv.mpf(n)/d
    return iv.mpf(v)
def interval(lo,hi):return iv.mpf([exact(lo).a,exact(hi).b])
def box(v):return interval(*v)
def outward(v):return [math.nextafter(float(v.a),-math.inf),math.nextafter(float(v.b),math.inf)]
def above(v,b=0):return bool(v.a>exact(b))
def below(v,b):return bool(v.b<exact(b))
A=box(CASE["A"]);X=box(CASE["x"])
M2=box(STATIC["fixed_original_M2"]);MU=box(CASE["mu"])
U0=box(HISTORY["fixed_U0"]);N=box(CASE["thermal_occupation_per_oscillator"])
V0=2*iv.pi**2
OMEGA=iv.sqrt(3);D=4
THERMAL_Q=N/(1+N)
WEIGHT=N**2/(1+N)**10
SOURCE_C=2*iv.pi**2*M2
R=(box(HISTORY["x0"])/4)/SOURCE_C
L=1+iv.sqrt(3)/4
def manifest(script,extra=()):
    paths=INPUTS+[HERE/"common.py",HERE/script]+[HERE/p for p in extra]
    return {str(p.relative_to(REPO)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
def finish(script,payload,extra=()):
    assert __debug__
    ap=argparse.ArgumentParser(description=__doc__)
    g=ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--write",action="store_true");g.add_argument("--check",action="store_true")
    args=ap.parse_args()
    payload.update(schema="ueot-total-source-"+Path(script).stem+"/1",status="PASS",
        source_sha256=manifest(script,extra),old_checkers_executed=0,
        mode_ODE_integrations=0,geometry_ODE_integrations=0)
    path=HERE/(Path(script).stem+".json")
    if args.write:path.write_text(json.dumps(payload,indent=2,sort_keys=True,ensure_ascii=False)+"\n")
    else:assert json.loads(path.read_text())==payload,"Certificate differs from saved result"
    print("PASS: "+Path(script).stem)
