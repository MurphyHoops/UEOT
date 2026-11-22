"""Fresh finite-initial and local-field certificates; frozen data only."""
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
 TIMELIKE/"operational_selection/instrument.json",
 TIMELIKE/"operational_selection/fluctuations.json",
 TIMELIKE/"nonlinear_history/kernels.json"]
HISTORY,STATIC,INSTRUMENT,FLUCTUATIONS,KERNELS=[json.loads(p.read_text()) for p in INPUTS]
assert all(x["status"]=="PASS" for x in [HISTORY,STATIC,INSTRUMENT,FLUCTUATIONS,KERNELS])
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
X=box(CASE["x"]);X0=box(HISTORY["x0"]);A=box(CASE["A"])
M2=box(STATIC["fixed_original_M2"]);MU=box(CASE["mu"])
U0=box(HISTORY["fixed_U0"]);NTHERMAL=box(CASE["thermal_occupation_per_oscillator"])
C=2*iv.pi**2*M2
VP=X0/4
LAMBDA2=2*U0/3
XC=1/LAMBDA2
BETA=M2*MU/(3*XC**2)
VOLUME=iv.pi**2/3-iv.pi*iv.sqrt(3)/2
TIME_TV=8/iv.pi
VM_FIELD=1/(2*iv.pi**2*X)
BETA_FIELD2=1/(2*iv.pi**2*X**2)
W_POINTER=X
W_HIGH_UPPER=iv.pi**2*X*(1+2*NTHERMAL)*TIME_TV/VOLUME
W_UPPER=W_POINTER+W_HIGH_UPPER
LOCAL_MSE_UPPER=4*W_UPPER*MU/C+4*W_UPPER**2/C**2
def manifest(script,extra=()):
    paths=INPUTS+[HERE/"common.py",HERE/script]+[HERE/p for p in extra]
    return {str(p.relative_to(REPO)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
def finish(script,payload,extra=()):
    assert __debug__,"Scientific assertions must remain enabled"
    ap=argparse.ArgumentParser(description=__doc__)
    g=ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--write",action="store_true");g.add_argument("--check",action="store_true")
    args=ap.parse_args()
    payload.update(schema="ueot-finite-local-"+Path(script).stem+"/1",status="PASS",
        source_sha256=manifest(script,extra),old_checkers_executed=0,
        mode_ODE_integrations=0,geometry_ODE_integrations=0)
    path=HERE/(Path(script).stem+".json")
    if args.write:path.write_text(json.dumps(payload,indent=2,sort_keys=True,ensure_ascii=False)+"\n")
    else:assert json.loads(path.read_text())==payload,"Certificate differs from saved result"
    print("PASS: "+Path(script).stem)
