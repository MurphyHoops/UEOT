"""Original KG field, parity exchange, measured feedback, and a closed memory cycle."""
import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path
import sys

import numpy as np
from mpmath import iv
from scipy.sparse.linalg import expm_multiply

HERE = Path(__file__).resolve().parent
BASE = HERE.parents[1] / "correlated_bath"
sys.path.insert(0, str(BASE/"field"))
sys.path.insert(0, str(BASE/"dynamics"))
import probe
from fock import _hamiltonians, _thermal_factor

iv.dps = 55
PIN = "67aa5c4d9a7e77da3f2a74dfb717a711f885cca9"
CASES = {"chapter71_local": ("2/3","3/4","0",False),
         "chapter71_antipodal": ("1/5","1/5","0",True),
         "strict_timelike": ("1/5","1/5","5/2",False),
         "strict_spacelike": ("1/5","1/5","1/10",True)}


def q(x):
    x = Fraction(x)
    return iv.mpf(x.numerator)/x.denominator


def endpoint(parts):
    sign, m, e, _ = parts
    return (-1)**sign*Fraction(m)*Fraction(2)**e


def bounds(x):
    scale = 10**14
    lo, hi = (endpoint(v)*scale for v in x._mpi_)
    return [str(Fraction(lo//1,scale)), str(Fraction(-(-hi//1),scale))]


def mid(x):
    return float(x.mid)


def abs2(z):
    return z.real**2 + z.imag**2


def wedge(a, b):
    return a.real*b.imag-a.imag*b.real


def histories(case, s, last, infinite):
    a,b,gap = map(q, case[:3])
    A, B = [], []
    lam, n, c = q("3/10"), q("1/2"), q("1/4")
    I = iv.mpc(0,1)
    energy = q(0)
    for j in range(last+1):
        w, g = probe.mode(j)
        aj = s*lam*g/w*(1-iv.exp(I*w*a))
        bj = (-1)**(j*case[3])*lam*g/w*iv.exp(I*w*(a+gap))*(1-iv.exp(I*w*b))
        A.append(aj)
        B.append(bj)
        energy += w*(abs2(aj)+abs2(bj))
    phi_rest = 4*sum(wedge(aj,bj) for aj,bj in zip(A[1:],B[1:]))
    vacuum_rest = 2*sum(map(abs2,B[1:]))
    if infinite:
        pref = (80/iv.pi)**8
        htail = 2*pref/(10*probe.beta**3*last**10)
        phi_rest += iv.mpf([-16,16])*lam**2*htail
        vacuum_rest += iv.mpf([0,8])*lam**2*htail
        energy += iv.mpf([0,16])*lam**2*pref/(9*probe.beta**2*last**9)
    phi = phi_rest+4*wedge(A[0],B[0])
    noise = (vacuum_rest+2*abs2(B[0]) + 2*(n+c)*abs2(B[0]+B[1])
             +2*(n-c)*abs2(B[0]-B[1]))
    z = iv.exp(-noise+I*phi)
    den = 1+2*n

    def parity(v):
        return iv.exp(-2*abs2(v)/den)/den

    h = (parity(A[0]+B[0])+parity(A[0]-B[0]))/2
    r = parity(A[0])*iv.exp(-vacuum_rest-4*(n-2*c*c/den)*abs2(B[1])
                             +I*(phi_rest-8*c*wedge(A[0],B[1])/den))
    return phi, noise, energy, z, h, r


def records(mu, h, mixed):
    # i = positive probe outcome (loaded excitation), j = original zero-mode parity.
    return [[(1+(2*i-1)*mu+(-1)**j*h+(2*i-1)*(-1)**j*mixed)/4
             for j in (0,1)] for i in (0,1)]


def account(data):
    phi, Q, Wsrc, z, h, r = data
    out = dict(Phi=bounds(phi), Q=bounds(Q), W_source=bounds(Wsrc))
    for axis, mu, mixed in (("X",z.real,r.real),("Y",-z.imag,-r.imag)):
        p, odd = (1+mu)/2,(1-h)/2
        joint = records(mu,h,mixed)
        assert min(cell.a for row in joint for cell in row)>0
        diff = joint[1][1]-p*odd
        cond = [row[1]/sum(row) for row in joint]
        erase = q("3/2")*p
        # The fresh reset carrier leaves with energy equal to the memory loading work.
        assert 0 in (p-odd)-sum(sum(row)*(i-cond[i]) for i,row in enumerate(joint))
        assert 0 in ((p-odd)-p+odd)
        assert 0 in ((Wsrc+p-p+erase)-(Wsrc+erase))
        out[axis] = {"p_plus":bounds(p),"odd_before":bounds(odd),
                     "joint_i_j":[[bounds(cell) for cell in row] for row in joint],
                     "odd_given_i":[bounds(x) for x in cond],
                     "joint11_minus_product":bounds(diff),
                     "original_field_gain_first_swap":bounds(p-odd),
                     "load_work":bounds(p),"feedback_work":bounds(-p),
                     "field_gain_return_swap":bounds(odd),"memory_reset_work":bounds(erase),
                     "outgoing_reset_energy":bounds(erase),
                     "whole_cycle_drive_work":bounds(Wsrc+erase),
                     "long_then_weak_Cesaro":bounds((p+odd)/2),"weak_then_long":bounds(p)}
    return out


def fock_check(case, s, k, analytic, gates=False):
    # Direct low-mode Schrodinger evolution of a thermal purification, no Weyl rules.
    a,b,gap = (float(Fraction(v)) for v in case[:3])
    ham = _hamiltonians(k,.3)
    f = _thermal_factor(k,.5,.25)
    i0 = np.array([i for total in range(k+1) for i in range(total+1)])
    i1 = np.array([total-i for total in range(k+1) for i in range(total+1)])
    initial = expm_multiply((-1j*a)*ham[int(s<0)],f)
    initial *= np.exp(-1j*gap*(i0+1.5*i1))[:,None]
    sign = ((-1)**(i1*int(case[3])))[:,None]
    plus,minus = (sign*expm_multiply((-1j*b)*h,sign*initial) for h in ham)
    parity = ((-1)**i0)[:,None]
    z = np.vdot(minus,plus)
    r = np.vdot(minus,parity*plus)
    h = (np.vdot(plus,parity*plus)+np.vdot(minus,parity*minus)).real/2
    target = analytic[3:]
    errors = [abs(z-complex(mid(target[0].real),mid(target[0].imag))),
              abs(h-mid(target[1])), abs(r-complex(mid(target[2].real),mid(target[2].imag)))]
    result = {"K":k,"abs_errors_z_h_r":list(map(float,errors))}
    if not gates:
        return result
    # Rotate +Y to excited and embed into complete even/odd pairs before swapping.
    # Coordinates are B, floor(N0/2), parity(N0), N1, thermal purification.
    shape = (2,k//2+1,2,k+1,f.shape[1])
    before = np.zeros(shape,complex)
    for i, amps in enumerate(((plus+1j*minus)/2,(plus-1j*minus)/2)):
        before[i,i0//2,i0%2,i1,:] = amps
    after = before.swapaxes(0,2)
    en = ((2*np.arange(shape[1])[:,None,None]+np.arange(2)[None,:,None])
          +1.5*np.arange(k+1)[None,None,:])
    def field_energy(v):
        return float(np.sum(abs(v)**2*en[None,...,None]))
    old_energy = field_energy(before)
    probs = np.sum(abs(after)**2,axis=(1,3,4)).T  # i (field), j (probe)
    m = probs[1].sum()
    odd = probs[:,1].sum()
    maxerr = abs(field_energy(after)-old_energy-(m-odd))
    out_energy = 0.
    field_dim = shape[1]*shape[2]*shape[3]
    def reduced_field(v):
        return sum(x@x.conj().T for x in (amp.reshape(field_dim,-1) for amp in v))
    returned_field = np.zeros((field_dim,field_dim),complex)
    dp = np.zeros((2,2))
    # Keep each projective outcome unnormalized. Undo the exchange after feedback.
    for i in (0,1):
        branch = np.zeros_like(after)
        branch[:,:,i] = after[:,:,i]
        driven = branch[:,:,::-1] if i else branch
        restored = driven.swapaxes(0,2)
        out_energy += field_energy(restored)
        returned_field += reduced_field(restored)
        dp[i] = (np.vdot(branch,branch).real,field_energy(driven)-field_energy(branch))
        maxerr = max(maxerr,abs(dp[i,1]+i*dp[i,0]),np.linalg.norm(restored[1]))
    predicted = np.array([[mid(x) for x in row] for row in records(-target[0].imag,target[1],-target[2].imag)])
    assert maxerr < 1e-12 and abs(out_energy-old_energy)<1e-12
    state_error = np.linalg.norm(returned_field-reduced_field(before))
    assert state_error < 2e-12
    # At theta=pi/14, a full 14-pulse period averages the B and odd-mode bits.
    theta = np.pi/14
    av = np.mean([np.linalg.norm(np.cos(t*theta)*before[1]+1j*np.sin(t*theta)*after[1])**2
                  for t in range(14)])
    assert abs(av-(m+odd)/2)<1e-12
    result.update({"returned_field_Frobenius_residual":float(state_error),
                   "period_mean_B_excitation":float(av),
                   "gate_joint_max_error_vs_two_mode_exact":float(np.max(abs(probs-predicted))),
                   "gate_energy_max_residual":float(max(maxerr,abs(out_energy-old_energy))),
                   "instrument_probability_and_feedback_work":dp.tolist()})
    return result


def check_reset_gate():
    # Finite dilation: M (gap 0 -> e -> 0) exchanges with a fresh ground port.
    # Check both input bits while entangled with an arbitrary reference via linearity.
    swap = np.eye(4)[[0,2,1,3]]
    E = np.diag([0,1.5])
    H = np.kron(E,np.eye(2))+np.kron(np.eye(2),E)
    assert np.array_equal(swap@H,H@swap)
    for i in (0,1):
        assert np.array_equal(swap[:,2*i],np.eye(4)[:,i])
    return "both basis images and energy commutator exact"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def calculate():
    frozen = json.loads((BASE/"field/observed.json").read_text())
    out = {"baseline":PIN,"source_sha256":{str(p.relative_to(BASE)):sha(p) for p in
           (BASE/"field/probe.py",BASE/"field/observed.json",BASE/"dynamics/fock.py",BASE/"dynamics/correlated_cq.py")},
           "units":"hbar=omega0=kB=1","lambda_n_c":["3/10","1/2","1/4"],
           "reset_gap":"3/2","last_cosine_shell":320,"intervals":"outward rational endpoints, grid 1e-14",
           "memory_dilation_check":check_reset_gate(),"cases":{}}
    for name,case in CASES.items():
        entry = {"a_b_gap_antipodal":list(case),"signs":{}}
        for s in (1,-1):
            full = histories(case,s,320,True)
            data = account(full)
            low = histories(case,s,1,False)
            checks = [fock_check(case,s,k,low,gates=(k==10)) for k in (10,20)]
            assert max(checks[1]["abs_errors_z_h_r"]) < 2e-6
            assert max(checks[1]["abs_errors_z_h_r"]) < max(checks[0]["abs_errors_z_h_r"])
            assert checks[0]["gate_joint_max_error_vs_two_mode_exact"] < 5e-4
            if name=="chapter71_local" and s==1:
                assert abs(mid((1-full[3].imag)/2)-.427005743276)<1e-12
                assert 0 not in (full[5].imag-full[3].imag*full[4])
            if case[3]:
                assert 0 in full[0]
            if name.startswith("chapter71") and s==1:
                prev = frozen["spacelike" if case[3] else "timelike_access"]
                for key,val in (("field_phase",full[0]),("damping_exponent",full[1]),
                                ("bare_energy_gain",full[2]),("signed_imag_coherence",full[3].imag)):
                    lo,hi=map(endpoint,prev[key]["dyadic"])
                    l,h=map(endpoint,val._mpi_)
                    assert lo<=l<=h<=hi
            data["independent_two_mode_Fock"]=checks
            entry["signs"][str(s)]=data
        out["cases"][name]=entry
    return out


def matches(got, saved):
    if isinstance(got,dict):
        return got.keys()==saved.keys() and all(matches(v,saved[k]) for k,v in got.items())
    if isinstance(got,list):
        return len(got)==len(saved) and all(matches(v,w) for v,w in zip(got,saved))
    if isinstance(got,float):
        return abs(got-saved)<5e-11
    return got==saved


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check",action="store_true",help="recompute and compare the saved receipt")
    parser.add_argument("--field-result",type=Path,default=HERE.parent/"field/result.json",help="also compare the sibling field study's four cases")
    args=parser.parse_args()
    result=calculate()
    if args.field_result:
        other=json.loads(args.field_result.read_text())["results"]
        for name,entry in result["cases"].items():
            row=entry["signs"]["1"]
            for key,interval in (("field_phase",row["Phi"]),("Q",row["Q"]),("p_plusY",row["Y"]["p_plus"])):
                a,b=map(Fraction,interval)
                c,d=map(Fraction,other[name][key])
                assert max(a,c)<=min(b,d),(name,key)
        from field_review import review
        result["field_cross_review"] = review(args.field_result,q,bounds,result["cases"]["chapter71_local"]["signs"]["1"]["Y"])
        print("PASS sibling: 12 compatible enclosing intervals",file=sys.stderr)
    if args.check:
        assert matches(result,json.loads((HERE/"result.json").read_text()))
        print("PASS: 4 field settings, both signs, X/Y, 16 direct Fock comparisons, feedback and reset")
    else:
        print(json.dumps(result,indent=2,allow_nan=False))
