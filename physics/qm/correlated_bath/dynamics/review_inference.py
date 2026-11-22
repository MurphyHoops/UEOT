"""Read-only review of C's synthetic dataset, sealed settings, frames and decisions."""
import argparse
import hashlib
import itertools
import json
import os
import sys
from fractions import Fraction as F
from pathlib import Path

import numpy as np
from mpmath import iv
from scipy.sparse.linalg import expm_multiply

from correlated_cq import RECORDS, events_from_blocks
from fock import _hamiltonians, _thermal_factor, galerkin_blocks

HERE = Path(__file__).resolve().parent
INFERENCE = HERE.parent/"inference"
sys.path.insert(0,str(INFERENCE))
import shared


def read(name):
    return json.loads((INFERENCE/name).read_text())


def sha(name):
    return hashlib.sha256((INFERENCE/name).read_bytes()).hexdigest()


def edge(x, upper=False):
    sign, m, e, _ = x._mpi_[int(upper)]
    return (-1)**sign*F(m)*F(2)**e


def path(times, signs, lam):
    # Interaction picture. Each displacement starts in the preparation frame.
    alpha = [iv.mpc(0), iv.mpc(0)]
    phase, clock = q(0), q(0)
    for t, sign in zip(times,signs):
        for j,(w,g) in enumerate(((q(1),q(1)),(q("3/2"),q("3/5")))):
            step = sign*lam*g/w*iv.exp(I*w*clock)*(1-iv.exp(I*w*t))
            phase += (H.conj(alpha[j])*step).imag
            alpha[j] += step
        clock += t
    return alpha, phase


def overlap(left, right, n, c):
    a, phase = left
    b, phase2 = right
    d = [ai-bi for ai,bi in zip(a,b)]
    return iv.exp(I*(phase-phase2+H.inner(b,a).imag)
                  -(n+q("1/2"))*H.inner(d,d).real-2*c*(H.conj(d[0])*d[1]).real)


def bell_moments(times, lam, n, c, names):
    moments = {obs: [] for obs in names}
    for record in RECORDS:
        ts = times[:len(record)]
        hs = []
        for bits in itertools.product((0,1),repeat=len(record)):
            op = H.IDENT
            for j,bit in enumerate(bits):
                gate = H.FAIL if record[j]=="f" else H.mm(H.ROTATIONS[j],H.PASS)
                op = H.mm(H.mm(gate,H.PROJECT[bit]),op)
            hs.append((sum(op,[]),path(ts,[1-2*i for i in bits],lam)))
        for obs in names:
            m = H.kron(*(H.PAULI[x] for x in obs))
            weight, moment = q(0),q(0)
            for v, left in hs:
                mv = H.mv(m,v)
                for vp,right in hs:
                    influence = overlap(left,right,n,c)/2
                    weight += (H.inner(vp,v)*influence).real
                    moment += (H.inner(vp,mv)*influence).real
            moments[obs].append((weight,moment))
    return moments


def break_values(lam, n, c, eta, offset, gain, key):
    if key.startswith("R"):
        ts = [q({"R0":"0","Rshort":"3/4","Rlong":"3/2"}[key])]
        return eta*overlap(path(ts,[1],lam),path(ts,[-1],lam),n,c).real
    s = 1 if key.endswith("p") else -1
    ts = [q(1 if key.startswith("H") else "2/3"),q("3/4")]
    z = eta*iv.exp(I*offset)*overlap(path(ts,[s,1],lam),path(ts,[s,-1],lam),n,c)
    return z.real if key.startswith("X") else -gain*z.imag


def fock_phase(a, s):
    hp, hm = _hamiltonians(20, .3)
    factor = _thermal_factor(20, .5,.25)
    reset = expm_multiply((-1j*a)*(hp if s==1 else hm),factor)
    plus, minus = (expm_multiply((-1j*.75)*h,reset) for h in (hp,hm))
    return np.vdot(minus,plus)


def main(repo, receipt_path):
    global H, q, I
    shared.REPO = repo  # runtime location for the frozen in-memory blob loader
    H = shared.historic("interval_source")
    q, I = H.q, H.I
    iv.dps = 55
    cfg, truth = read("protocol.json"), read("truth.json")
    preds, fit, archived = read("predictions.json"),read("calibration_fit.json"),read("holdout_results.json")
    freeze = read("freeze.json")
    assert all(sha(k)==v for k,v in freeze["files"].items())
    assert sha("source_snapshot.py")==hashlib.sha256((HERE/"correlated_cq.py").read_bytes()).hexdigest()
    assert preds["calibration_hash"]==sha("calibration.npz") and preds["fit_hash"]==sha("calibration_fit.json")
    lam,n,c,eta,off,gain,challenge = [q(truth[k]) for k in
                    ("lambda","n","c","eta","break_offset","Y_relative_gain","challenge_eta")]
    grid = 2**cfg["grid_bits"]
    cuts_checked, maxerr, fails, examples = 0,F(0),[],{}
    phase_gaps, finite_max = {},0.
    for a,t in (("2/3",2/3),("1",1.)):
        for s in (1,-1):
            z = fock_phase(t,s)
            ts = [q(a), q("3/4")]
            ideal = overlap(path(ts,[s,1],lam),path(ts,[s,-1],lam),n,c)
            oracle = complex(float(ideal.real.mid),float(ideal.imag.mid))
            assert abs(z-oracle)<2e-7 and s*z.imag>0
            phase_gaps[f"{a},s={s}"] = {"Fock_phase":float(np.angle(z)),"Fock_vs_Weyl_coherence":abs(z-oracle)}
    cells=100
    bell = {}
    for family in cfg["holdout_families"]:
        swap = family=="swap"
        e = challenge if family=="readout_challenge" else eta
        ts = list(map(q,cfg["swap" if swap else "original"]))
        m = bell_moments(ts,lam,n,c,cfg["bell_tests"])
        fock = galerkin_blocks(.3,.5,.25,20,timing="changed_intervals" if swap else "deployment")
        for obs in cfg["bell_tests"]:
            arr = [(weight+sgn*e*moment)/2 for weight,moment in m[obs] for sgn in (-1,1)]
            ideal_events = events_from_blocks(fock,1,obs).reshape(4,2)
            ef = float(e.mid)
            measured = (((1+ef)*ideal_events+(1-ef)*ideal_events[:,::-1])/2).ravel()
            finite_max = max(finite_max,max(abs(z-float(x.mid)) for z,x in zip(measured,arr)))
            bell[family+"_"+obs]=arr
    assert finite_max < 1e-7
    for phase in ("calibration","holdout"):
        receipt = read(phase+"_receipt.json")
        assert sha(phase+".npz")==receipt["raw_sha256"] and receipt["freeze_sha256"]==sha("freeze.json")
        assert sha(phase+"_source_cdf.json")==receipt["cdf_sha256"]
        if phase=="holdout":
            assert receipt["prediction_sha256"]==sha("predictions.json")
        plan = cfg["calibration"] if phase=="calibration" else (cfg["holdout_phase"] |
            {f+"_"+o:cfg["shots_per_bell_setting"] for f in cfg["holdout_families"] for o in cfg["bell_tests"]})
        codes = read(phase+"_source_cdf.json")
        with np.load(INFERENCE/(phase+".npz")) as data:
            order,rows = data["block_setting"],data["ordered_codes"]
        for i,(key,N) in enumerate(plan.items()):
            events = bell.get(key)
            if events is None:
                mu = break_values(lam,n,c,eta,off,gain,key)
                events = [(1-mu)/2,(1+mu)/2]
            cum = q(0)
            for val,cut in zip(events[:-1],codes[key],strict=True):
                cum += val
                diff = cum*grid-cut
                maxerr = max(maxerr,abs(edge(diff)),abs(edge(diff,True)))
                cuts_checked+=1
            counts=np.bincount(rows[order==i].ravel(),minlength=len(events))
            assert sum(counts)==N
            if phase=="calibration":
                mu = q(2*int(counts[1]))/N-1
                rad = 2*iv.sqrt(iv.ln(q(2*len(plan))/q(cfg["alpha_cal"]))/(2*N))+q(cfg["bias_mean"])+q(2)/grid
                lo,hi=map(F,fit["seven_mean_bands"][key])
                assert lo<=edge(mu-rad) and hi>=edge(mu+rad,True)
            else:
                rad=iv.sqrt(iv.ln(q(2*cells)/q(cfg["alpha_hold"]))/(2*N))
                for j,count in enumerate(counts):
                    lo,hi=map(F,archived["settings"][key]["frequency_bands"][j])
                    m=q(int(count))/N
                    assert lo<=max(F(0),edge(m-rad)) and hi>=min(F(1),edge(m+rad,True))
                    pred_lo,pred_hi=map(F,preds["outer_event_probability"][key][j])
                    if hi < pred_lo or lo > pred_hi:
                        fails.append(key+"/"+str(j))
                    if key in ("original_ZZ","readout_challenge_ZZ") and j==0:
                        examples[key]={"index":0,"count":int(count),"N":N,
                            "measured":[str(lo),str(hi)],"predicted":[str(pred_lo),str(pred_hi)],
                            "ideal_probability":float(events[0].mid)}
    assert cuts_checked==93 and maxerr<F(1,2)
    assert sorted(fails)==sorted(x for arr in archived["failed_cells"].values() for x in arr)
    assert len(fails)==4 and all(x.startswith("readout_challenge") for x in fails)
    result={"status":"PASS","freeze_sha256":sha("freeze.json"),"predictions_sha256":sha("predictions.json"),
           "holdout_sha256":sha("holdout.npz"),"cuts_checked":cuts_checked,"max_abs_CDF_grid_error":float(maxerr),
           "Fock_K20_vs_96_Bell_cells_max_abs":float(finite_max),"Fock_breaks":phase_gaps,
           "calibration_bands_checked":7,"holdout_bands_checked":cells,"disjoint":fails,"examples":examples}
    if receipt_path is not None or not (HERE/"review_observed.json").exists():
        with (receipt_path or HERE/"review_observed.json").open("x", encoding="utf-8") as out:
            out.write(json.dumps(result,indent=2,allow_nan=False)+"\n")
    print(json.dumps(result,indent=2))


if __name__=="__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path, help="write this run to a new JSON file")
    args = parser.parse_args()
    repo = os.environ.get("UEOT_UPSTREAM_REPO")
    if not repo:
        parser.error("set UEOT_UPSTREAM_REPO to the Git repository containing " + shared.COMMIT)
    main(repo, args.receipt)
