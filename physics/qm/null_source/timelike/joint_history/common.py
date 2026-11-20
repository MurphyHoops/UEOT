"""Shared new certificate inputs; inherited checkers are never imported or run."""
from __future__ import annotations
import argparse,hashlib,json,math
from pathlib import Path
from mpmath import iv
HERE=Path(__file__).resolve().parent
TIMELIKE=HERE.parent
REPO=HERE.parents[4]
iv.dps=90
INPUTS=[TIMELIKE/"physical_source/static_source.json",TIMELIKE/"physical_source/stability.json"]
OLD=json.loads(INPUTS[0].read_text())
OLD_RESPONSE=json.loads(INPUTS[1].read_text())
SEED=OLD["replacement_mean_history"]["cases"]["minimum_equal_law"]
assert OLD["status"]==OLD_RESPONSE["status"]=="PASS"
def exact_float(v):
    n,d=v.as_integer_ratio()
    return iv.mpf(n)/d
def interval(lo,hi):return iv.mpf([lo.a,hi.b])
def box(values):
    def exact(v):return exact_float(v) if isinstance(v,float) else iv.mpf(v)
    return interval(exact(values[0]),exact(values[1]))
def outward(v):
    return [math.nextafter(float(v.a),-math.inf),math.nextafter(float(v.b),math.inf)]
def above(v,b=0):return bool(v.a>iv.mpf(b))
def below(v,b):return bool(v.b<iv.mpf(b))
S=box(OLD["reused_spectral_constant"])
M=box(OLD["fixed_original_M2"])
X0=box(SEED["A_squared"])
NU0=box(SEED["nu"])
NU=2*NU0
D=iv.sqrt(3)/2
L=1+D/2
K=1/(16*iv.pi**2)
D0=3/(32*iv.pi**2)
J=4*iv.sqrt(3)/iv.pi**2
T=iv.mpf("1e-12")
Q=iv.mpf(1)/2
def B(x):return (S/4-iv.mpf(3)/160-(iv.log(x/4)+2*iv.euler)/64)/iv.pi**2
def E(x):return 4*B(x)/3+D0
def F(x):return 2*B(x)/3-D0
U0X0=1-F(X0)/X0
MU_OLD=L+2/NU0
MU=L+2/NU
VAR=D**2/4+4*L/NU+4/NU**2
def filter_data(t=T):
    """Stable exact posterior formulas; no subtraction of nearly equal means."""
    z=2*t/NU
    c=1+z
    alpha=t/c
    em=iv.exp(D*alpha)-1
    w=1/(2+em)
    Z=iv.exp(-alpha)*(1+iv.exp(-D*alpha))/(2*c)
    p=Q*Z
    delta=(D*em/(2*(2+em))+L*z*(2+z))/c**2+2*z/(NU*c)
    vs=D**2*w*(1-w)/c**4+4*(1+D*w)/(NU*c**3)+4/(NU**2*c**2)
    pf=1-p
    df=p*delta/pf
    vf=(VAR-p*vs-p*delta**2/pf)/pf
    return {"c":c,"alpha":alpha,"radial_high_weight":w,"Z":Z,
            "success_probability":p,"failure_probability":pf,
            "success_mean_drop":delta,"failure_mean_rise":df,
            "success_mean":MU-delta,"failure_mean":MU+df,
            "success_variance":vs,"failure_variance":vf}
def shifted_phi(h):
    u=U0X0
    return (12*u-6-K/X0)*h-(12*u-3)*h**2/X0+4*u*h**3/X0**2
def shifted_thermal(h):
    u=U0X0
    return (6*u-3)*h-3*u*h**2/X0+iv.log(1-h/X0)/(32*iv.pi**2)
def source_manifest(script,extra=()):
    paths=INPUTS+[HERE/"common.py",HERE/script]+[HERE/p for p in extra]
    return {str(p.relative_to(REPO)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
def finish(script,payload,extra=()):
    ap=argparse.ArgumentParser(description=__doc__)
    group=ap.add_mutually_exclusive_group(required=True)
    group.add_argument("--write",action="store_true")
    group.add_argument("--check",action="store_true")
    args=ap.parse_args()
    payload.update(schema="ueot-joint-history-"+Path(script).stem+"/1",status="PASS",
                   source_sha256=source_manifest(script,extra),
                   old_checkers_executed=0,mode_ODE_integrations=0,geometry_ODE_integrations=0)
    path=HERE/(Path(script).stem+".json")
    if args.write:path.write_text(json.dumps(payload,indent=2,sort_keys=True,ensure_ascii=False)+"\n")
    else:assert json.loads(path.read_text())==payload,"New certificate differs from saved result"
    print("PASS: "+Path(script).stem)
