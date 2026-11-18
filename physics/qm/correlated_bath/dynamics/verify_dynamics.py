"""Verify the dynamics deliverable. All reads outside this directory are read-only."""
import argparse
import hashlib
import json
import os
import platform
import resource
import subprocess
import sys
import time
from fractions import Fraction as Q
from pathlib import Path
from types import ModuleType

import numpy as np
import scipy

from bounded_fock import certified_choi, rational_events
from correlated_cq import (RECORDS, TIMES, OBSERVABLES, exact_blocks, events_from_blocks,
                           event_probabilities, input_state)
from fock import galerkin_blocks, thermal_tail, uniform_bound

HERE = Path(__file__).resolve().parent
COMMIT = "44b6cd200cd01eccf15d4dc817311388d317a1af"


def distance(a, b):
    return {k: float(np.linalg.svd(a[k]-b[k], compute_uv=False).sum()/2) for k in RECORDS}


def check_blocks(blocks):
    assert tuple(blocks) == RECORDS
    for b in blocks.values():
        assert np.max(abs(b-b.conj().T)) < 2e-12
        assert np.linalg.eigvalsh(b)[0] > -2e-12
    assert abs(sum(np.trace(b) for b in blocks.values())-1) < 2e-12


def historical(repo):
    mod = ModuleType("frozen_v31_14")
    raw = subprocess.check_output(["git", "-C", repo, "show",
                                  COMMIT+":physics/qm/persistent_bath/dynamics.py"])
    exec(compile(raw, "frozen_v31_14/dynamics.py", "exec"), mod.__dict__)
    return mod, hashlib.sha256(raw).hexdigest()


def historical_gaussian(mod, timing, lam, n, c, rotate_covariance):
    rho = input_state(None)
    ts, rs = mod._configuration(TIMES[timing], None)
    v = np.kron([[n+.5, c], [c, n+.5]], np.eye(2))
    blocks = {}
    for name in RECORDS:
        k = len(name)
        ops = [mod.F if branch == "f" else rs[j]@mod.P for j, branch in enumerate(name)]
        hs = mod._history_operators(lam, ts[:k], ops)
        total = sum(ts[:k]) if rotate_covariance else 0
        block = np.zeros((4, 4), complex)
        for op, beta, p in hs:
            for op2, beta2, p2 in hs:
                coef = mod.gaussian_influence(beta, p, beta2, p2, total, covariance=v)
                block += coef*np.kron(op, np.eye(2))@rho@np.kron(op2.conj().T, np.eye(2))
        blocks[name] = block
    return blocks


def outward(q, digits=12):
    scale = 10**digits
    i = -(-q.numerator*scale//q.denominator)
    return f"{i//scale}.{i%scale:0{digits}d}"


def main(repo, receipt):
    start = time.monotonic()
    mod, digest = historical(repo)
    result = {"commit": COMMIT, "historical_dynamics_sha256": digest,
              "parameters": ["lambda", "n", "c"], "uniform_bounds_upper": {},
              "comparisons": [], "rational_choi": {}, "wrong_clock": {}}
    for k in (0, 4, 8, 12, 13, 14, 16, 20, 24):
        result["uniform_bounds_upper"][k] = outward(uniform_bound(k))
    assert uniform_bound(13) < Q(".038467") and uniform_bound(16) < Q(".011678")
    for timing in TIMES:
        vac = exact_blocks(.3, 0, 0, timing)
        assert sum(distance(vac, mod.exact_output(.3, times=TIMES[timing])).values()) < 1e-14
        for lam, n, c in ((.3, .5, .25), (.4, .6, -.6), (.2, .6, .6), (.4, .6, 0)):
            ref = exact_blocks(lam, n, c, timing)
            check_blocks(ref)
            for eta in (.9, 1):
                for obs in OBSERVABLES:
                    p = event_probabilities(lam, n, c, eta, obs, timing)
                    assert abs(sum(p)-1)<1e-13 and min(p)>=-1e-13
            assert abs(np.trace(ref["f"])-3/16) < 1e-12
            ds = []
            for k in (4, 8, 13, 16, 20):
                tick = time.monotonic()
                approx = galerkin_blocks(lam, n, c, k, timing)
                check_blocks(approx)
                per = distance(approx, ref)
                ds.append(sum(per.values()))
                assert ds[-1] <= float(uniform_bound(k))+1e-13
                entry = {"point": [lam, n, c], "timing": timing, "K": k,
                         "D_by_record": per, "D_CQ": ds[-1], "initial_tail": float(thermal_tail(n,c,k)),
                         "wall_seconds": time.monotonic()-tick}
                result["comparisons"].append(entry)
            assert ds[-1] < ds[0] and ds[-1] < 8e-6
        lam, n, c = .4, .6, -.45
        exact = exact_blocks(lam, n, c, timing)
        independent = galerkin_blocks(lam, n, c, 20, timing)
        good = historical_gaussian(mod, timing, lam, n, c, True)
        bad = historical_gaussian(mod, timing, lam, n, c, False)
        good_d = sum(distance(good, exact).values())
        bad_d = sum(distance(bad, independent).values())
        d = sum(distance(exact, independent).values())
        assert good_d < 1e-14 and d < 1e-5 and bad_d > 1e-3
        result["wrong_clock"][timing] = {"point": [lam,n,c], "pinned_gaussian_vs_API": good_d,
                                        "Fock_K20_vs_API": d, "Fock_K20_vs_wrong_frame": bad_d}
        for k in (13, 16):
            tick = time.monotonic()
            raw, budget = certified_choi(".3", ".5", ".25", k, timing)
            assert all(np.array_equal(sum(pair[j].reshape(2,2,2,2).trace(axis1=0,axis2=2)
                               for pair in raw.values()), np.eye(2)*Q(1,2) if j==0 else np.zeros((2,2))) for j in (0,1))
            blocks = {l: re.astype(float)+1j*im.astype(float) for l,(re,im) in raw.items()}
            check_blocks(blocks)
            for obs in OBSERVABLES:
                p = rational_events(raw, ".96", obs)
                assert min(p)>=0 and sum(p)==1
                assert np.max(abs(np.array(p,float)-events_from_blocks(blocks,.96,obs))) < 1e-15
            sci = galerkin_blocks(.3,.5,.25,k,timing)
            observed = sum(distance(sci,blocks).values())
            assert observed < budget["all_input_arithmetic"]/2
            e = budget["bell_arithmetic"]
            worst = budget["truncation"]+2*(e+1-1/(1+2*e))
            assert worst < (Q(".049431") if k==13 else Q(".027603"))
            result["rational_choi"][f"{timing}_K{k}"] = {
                "point": [".3",".5",".25"], "point_budget_upper": {k:outward(v) for k,v in budget.items()},
                "uniform_with_arithmetic_upper":outward(worst), "observed_D_vs_scipy_on_Bell": observed,
                "wall_seconds_including_comparison":time.monotonic()-tick,
                "choi_real_imag_pairs": {l:[[[str(re[i,j]),str(im[i,j])] for j in range(4)]
                                       for i in range(4)] for l,(re,im) in raw.items()}}

    # Finite nonqubit reference and mixed SR input, and unequal accepted effects.
    rng = np.random.default_rng(731)
    x = rng.normal(size=(6,4))+1j*rng.normal(size=(6,4))
    rho = x@x.conj().T
    rho /= np.trace(rho)
    ref = exact_blocks(.31,.43,-.22,rho_sr=rho)
    finite = galerkin_blocks(.31,.43,-.22,13,rho_sr=rho)
    check_blocks(ref)
    check_blocks(finite)
    d = sum(distance(ref,finite).values())
    assert d < 2e-5
    states = [np.diag([1,0]), np.diag([0,1])]
    weights = [np.trace(exact_blocks(.3,.5,.25,rho_sr=s)["ppp"]).real for s in states]
    assert min(weights)>=27/64 and max(weights)<=343/512 and abs(weights[0]-weights[1])>.001
    result.update({"mixed_qubit_qutrit_D_K13": d, "p_ppp_on_Z_eigenstates":weights,
                   "python":sys.version, "numpy":np.__version__, "scipy":scipy.__version__,
                   "platform":platform.platform(), "elapsed_seconds": time.monotonic()-start,
                   "peak_RSS_bytes_macos":resource.getrusage(resource.RUSAGE_SELF).ru_maxrss if sys.platform=="darwin" else None,
                   "status":"PASS"})
    if receipt is not None or not (HERE/"observed.json").exists():
        with (receipt or HERE/"observed.json").open("x", encoding="utf-8") as out:
            out.write(json.dumps(result,indent=2,allow_nan=False)+"\n")
    print("PASS",len(result["comparisons"]),"Bell/Fock comparisons;", result["wrong_clock"],
          "mixed r=3",d,"wall",result["elapsed_seconds"],"RSS",result["peak_RSS_bytes_macos"])


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path, help="write this run to a new JSON file")
    args = parser.parse_args()
    repo = os.environ.get("UEOT_UPSTREAM_REPO")
    if not repo:
        parser.error("set UEOT_UPSTREAM_REPO to the Git repository containing " + COMMIT)
    main(repo, args.receipt)
