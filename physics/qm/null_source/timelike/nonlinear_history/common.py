"""New nonlinear certificates; immutable JSON inputs only, no old program imports."""
from __future__ import annotations
import argparse, hashlib, json, math
from pathlib import Path
from mpmath import iv
HERE=Path(__file__).resolve().parent
TIMELIKE=HERE.parent
REPO=HERE.parents[4]
iv.dps=90
INPUTS=[TIMELIKE/"joint_history/history.json",
        TIMELIKE/"physical_source/static_source.json",
        TIMELIKE/"dynamic_seed/bounds.json",
        TIMELIKE/"dynamic_inverse/fast_root.json",
        TIMELIKE/"dynamic_inverse/harmonics.json"]
HISTORY,STATIC,SEED,FAST,HARMONICS=[json.loads(p.read_text()) for p in INPUTS]
assert all(d["status"]=="PASS" for d in [HISTORY,STATIC,SEED,FAST,HARMONICS])
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
X=box(CASE["x"]); A=box(CASE["A"])
OCCUPATION=box(CASE["thermal_occupation_per_oscillator"])
SLOW=box(SEED["positive_root_s"])
SIGMA=box(FAST["fast_conformal_growth_rate"])
KAPPA=box(FAST["fast_kappa_sigma_over_A"])
M2=box(STATIC["fixed_original_M2"]); MU=box(CASE["mu"])
U0=box(HISTORY["fixed_U0"])
RHOZ=M2*MU/(2*X**3)
def weight(lam,p=4):return (1+lam)**p*iv.log(iv.e+lam)
def manifest(script,extra=()):
    paths=INPUTS+[HERE/"common.py",HERE/script]+[HERE/p for p in extra]
    return {str(p.relative_to(REPO)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
def finish(script,payload,extra=()):
    assert __debug__,"Scientific assertions must remain enabled"
    ap=argparse.ArgumentParser(description=__doc__)
    g=ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--write",action="store_true");g.add_argument("--check",action="store_true")
    args=ap.parse_args()
    payload.update(schema="ueot-nonlinear-history-"+Path(script).stem+"/1",status="PASS",
        source_sha256=manifest(script,extra),old_checkers_executed=0,
        mode_ODE_integrations=0,geometry_ODE_integrations=0)
    path=HERE/(Path(script).stem+".json")
    if args.write:path.write_text(json.dumps(payload,indent=2,sort_keys=True,ensure_ascii=False)+"\n")
    else:assert json.loads(path.read_text())==payload,"Certificate differs from saved result"
    print("PASS: "+Path(script).stem)
