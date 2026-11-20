"""New algebra/interval certificates; predecessor data are read, never executed."""
from __future__ import annotations
import argparse,hashlib,json,math
from pathlib import Path
from mpmath import iv
HERE=Path(__file__).resolve().parent
TIMELIKE=HERE.parent
REPO=HERE.parents[4]
iv.dps=70
INPUTS=[TIMELIKE/"continuation/quantum/result.json",TIMELIKE/"prepared_initial/result.json"]
SEED=json.loads(INPUTS[0].read_text())["static_absolute_seed"]
PREP=json.loads(INPUTS[1].read_text())
LAM=PREP["physical_prescription"]["lambda"]
QR=PREP["absolute_stress"]["Qrho_absolute_integer_bound"]
assert LAM==32768 and QR==508
assert SEED["last_mode"]==1024 and SEED["zero_mode_zeta"]==1
assert PREP["physical_prescription"]["mu"]==1
assert PREP["physical_prescription"]["extra_finite_terms"]==0
def exact_float(v):
    n,d=v.as_integer_ratio()
    return iv.mpf(n)/d
def interval(lo,hi):
    return iv.mpf([lo.a,hi.b])
S=interval(*[exact_float(v) for v in SEED["finite_residual_sum_plus_certified_tail"]])
MLO=27*LAM**4-54*LAM**2*QR
MHI=27*LAM**4+54*LAM**2*QR
M=iv.mpf([MLO,MHI])
D=iv.sqrt(3)/2
D0=iv.mpf(3)/(32*iv.pi**2)
def outward(v):
    return [math.nextafter(float(v.a),-math.inf),math.nextafter(float(v.b),math.inf)]
def above(v,b=0):return bool(v.a>iv.mpf(b))
def below(v,b):return bool(v.b<iv.mpf(b))
def B(x):return (S/4-iv.mpf(3)/160-(iv.log(x/4)+2*iv.euler)/64)/iv.pi**2
def E(x):return 4*B(x)/3+D0
def C(x):return 19+15*(iv.log(x/4)+2*iv.euler)
def F(x,b):return x*x-2*x*E(x)-(1+b)*M
def root_box(b):
    """Exact monotonicity plus an interval fixed-point enclosure, no ODE."""
    lo,hi=iv.mpf(4*LAM**2),iv.mpf(9*LAM**2)
    assert below(F(lo,b),0) and above(F(hi,b))
    x=interval(lo,hi)
    for _ in range(4):
        ex=E(x)
        box=ex+iv.sqrt(ex*ex+(1+b)*M)
        assert above(box,4*LAM**2) and below(box,9*LAM**2)
        x=box
    return x
def source_manifest(script):
    paths=INPUTS+[HERE/"common.py",HERE/script]
    return {str(p.relative_to(REPO)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
def finish(script,payload):
    ap=argparse.ArgumentParser(description=__doc__)
    group=ap.add_mutually_exclusive_group(required=True)
    group.add_argument("--write",action="store_true")
    group.add_argument("--check",action="store_true")
    args=ap.parse_args()
    payload.update(schema="ueot-physical-source-"+Path(script).stem+"/1",
                   status="PASS",source_sha256=source_manifest(script),
                   old_checkers_executed=0,mode_ODE_integrations=0)
    path=HERE/(Path(script).stem+".json")
    if args.write:path.write_text(json.dumps(payload,indent=2,sort_keys=True,ensure_ascii=False)+"\n")
    else:
        assert json.loads(path.read_text())==payload,"New certificate differs from saved result"
    print("PASS: "+Path(script).stem)
