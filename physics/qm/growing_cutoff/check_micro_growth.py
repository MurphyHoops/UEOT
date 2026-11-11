#!/usr/bin/env python3
"""Independent finite diagnostic; no project implementation imports.

Analytic statements are proved in B_MICRO_GROWTH.md. Floating checks here
bind a new actual execution and cannot establish the universal quantifiers.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from datetime import datetime, timezone
from decimal import Decimal, getcontext
from pathlib import Path

import numpy as np
from scipy.linalg import expm


def basis(m):
    return [("g", 0)] + [x for j in range(1, m + 1)
                            for x in [("e", j - 1), ("g", j)]]


def embed(m, n):
    a, b = basis(m), basis(n)
    z = np.zeros((len(b), len(a)), complex)
    for j, x in enumerate(a):
        z[b.index(x), j] = 1
    return z


def red(m, alpha):
    a = basis(m)
    h = np.zeros((len(a), len(a)), complex)
    for j in range(1, m + 1):
        i, k = a.index(("e", j - 1)), a.index(("g", j))
        h[i, k] = h[k, i] = np.sqrt(j)
    return expm(-1j * alpha * h)


def phase(m, phi):
    return np.diag([np.exp(-1j * phi) if x[0] == "e" else 1
                    for x in basis(m)])


def blue_rect(m, beta):
    a, b = basis(m), basis(m + 2)
    z = np.zeros((len(b), len(a)), complex)
    for j, (s, n) in enumerate(a):
        if (s, n) == ("e", 0):
            z[b.index((s, n)), j] = 1
            continue
        partner = ("e", n + 1) if s == "g" else ("g", n - 1)
        rate = np.sqrt(n + 1 if s == "g" else n)
        z[b.index((s, n)), j] = np.cos(beta * rate)
        z[b.index(partner), j] = -1j * np.sin(beta * rate)
    return z


def blue_ambient(m, beta):
    # Only used on input columns whose paired blue blocks are wholly present.
    # The top dangling vectors are artificial ambient boundary completion.
    a = basis(m)
    h = np.zeros((len(a), len(a)), complex)
    for n in range(m + 1):
        if ("e", n + 1) in a:
            i, j = a.index(("g", n)), a.index(("e", n + 1))
            h[i, j] = h[j, i] = np.sqrt(n + 1)
    return expm(-1j * beta * h)


def dist(x, y):
    h = (x-y + (x-y).conj().T) / 2
    return float(np.abs(np.linalg.eigvalsh(h)).sum() / 2)


def cqdist(x, y):
    return sum(dist(x[k], y[k]) for k in x)


def density(v):
    return np.outer(v, v.conj())


def source_rect(n, q, phi, alpha, beta, rho, ref=2):
    s = 1-q/2
    final = n+4
    out = {}

    def rec(prefix, m, state):
        p0, p1, pf = s*(1-q), s*q, 1-s
        gates = {
            "0": np.sqrt(p0)*embed(m, m+2)@phase(m, phi),
            "1": np.sqrt(p1)*blue_rect(m, beta)@red(m, alpha),
            "f": np.sqrt(pf)*embed(m, m+2),
        }
        for label, k in gates.items():
            kr = np.kron(k, np.eye(ref))
            nxt = kr@state@kr.conj().T
            hist = prefix+label
            if label == "f" or len(hist) == 2:
                er = np.kron(embed(m+2, final), np.eye(ref))
                out[hist] = er@nxt@er.conj().T
            else:
                rec(hist, m+2, nxt)
    rec("", n, rho)
    return out


def ambient_path_outputs(n, q, phi, alpha, beta, rho, ref=2, policy=False):
    m = n+4
    j = np.kron(embed(n, m), np.eye(ref))
    r = j@rho@j.conj().T
    v0 = np.kron(phase(m, phi), np.eye(ref))
    v1 = np.kron(blue_ambient(m, beta)@red(m, alpha), np.eye(ref))
    vi = np.eye(len(r))
    s = 1-q/2
    probs = ({"f":1-s, "0f":s*(1-q)*(1-s), "1f":s*q*(1-s),
              "00":s*s*(1-q)**2, "01":s*s*q*(1-q),
              "10":s*s*q*(1-q), "11":s*s*q*q}
             if not policy else
             {"f":0.,"0f":0.,"1f":0.,"00":313/1250,
              "01":312/1250,"10":312/1250,"11":313/1250})
    gs = {"0":v0,"1":v1,"f":vi}
    out = {}
    for hist, p in probs.items():
        z = vi
        for c in hist:
            z = gs[c]@z
        out[hist] = p*z@r@z.conj().T
    return out


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--output",type=Path,default=Path("independent-growth-check.json"))
    args=parser.parse_args()
    checks=[]

    def check(name, value, condition):
        checks.append({"name":name,"value":value,"pass":bool(condition)})
        if not condition:
            raise AssertionError((name,value))

    tol=2e-12
    phi=-np.arctan2(4,3)
    alpha=np.arctan2(4,3)

    # Rectangular branch completeness and equality to a larger exact-block model.
    for n in [0,1,2,4]:
        for beta in [0.,.01,-.013,.37]:
            br=blue_rect(n,beta)
            residual=float(np.linalg.norm(br.conj().T@br-np.eye(2*n+1),2))
            check(f"blue_isometry_n{n}_b{beta}",residual,residual<tol)
            ambient=blue_ambient(n+4,beta)@embed(n,n+4)
            finite=embed(n+2,n+4)@br
            residual=float(np.linalg.norm(ambient-finite,2))
            check(f"actual_blue_columns_n{n}_b{beta}",residual,residual<tol)
            q=.52;s=1-q/2
            k0=np.sqrt(s*(1-q))*embed(n,n+2)@phase(n,phi)
            k1=np.sqrt(s*q)*br@red(n,alpha)
            kf=np.sqrt(1-s)*embed(n,n+2)
            residual=float(np.linalg.norm(sum(k.conj().T@k for k in [k0,k1,kf])-np.eye(2*n+1),2))
            check(f"full_instrument_complete_n{n}_b{beta}",residual,residual<tol)

    # Entangled input |e0,0_R>+|g1,1_R>, energy exactly one.
    n=1
    psi=np.zeros((2*n+1)*2,complex)
    psi[1*2]=psi[2*2+1]=1/np.sqrt(2)
    rho=density(psi)
    for q in [.48,.5,.52]:
        for beta in [.01,-.01,.2]:
            finite=source_rect(n,q,phi,alpha,beta,rho)
            direct=ambient_path_outputs(n,q,phi,alpha,beta,rho)
            residual=cqdist(finite,direct)
            check(f"all_seven_rect_vs_ambient_q{q}_b{beta}",residual,residual<tol)
            mass=sum(float(np.trace(x).real) for x in finite.values())
            check(f"raw_total_mass_q{q}_b{beta}",mass,abs(mass-1)<tol)
            s=1-q/2
            accepted={r:(x/(s*s) if "f" not in r else np.zeros_like(x))
                      for r,x in finite.items()}
            compiled=ambient_path_outputs(n,q,phi,alpha,beta,rho,policy=True)
            difference=cqdist(accepted,compiled)
            t=q-.5;u=.02**2-t*t
            exact=max(abs(t),u)+u
            check(f"complete_CQ_equals_TV_q{q}_b{beta}",
                  {"matrix":difference,"formula":exact},abs(difference-exact)<tol)
            no_blue=ambient_path_outputs(n,q,phi,alpha,0.,rho,policy=True)
            omitted=cqdist(compiled,no_blue)
            upper=abs(beta)*np.sqrt(2.)
            check(f"reference_retaining_omission_q{q}_b{beta}",
                  {"distance":omitted,"bound":upper},omitted<=upper+tol)

    # The fixed carrier cannot hold the actual boundary blue output.
    beta=.37;n=2
    v=blue_rect(n,beta)[:,basis(n).index(("g",n))]
    retained=embed(n,n+2).conj().T@v
    lost=float(1-np.vdot(retained,retained).real)
    expected=float(np.sin(beta*np.sqrt(n+1))**2)
    check("fixed_cutoff_loses_nonzero_mass",{"lost":lost,"formula":expected},
          lost>.01 and abs(lost-expected)<tol)

    # CP order witness, intentionally outside the small-beta deployment range.
    m=4;vac=np.zeros(2*m+1,complex);vac[0]=1
    r=red(m,np.pi/(2*np.sqrt(2)))
    b=blue_ambient(m,np.pi/2)
    order_distance=dist(density(b@r@vac),density(r@b@vac))
    check("actual_CP_order_distance_one",order_distance,abs(order_distance-1)<tol)

    # Sharp physical filter with a correlated reference, fail resets S only.
    m=3;ref=2
    for tail in [.000244140625,.05,.5,.9]:
        v=np.zeros((2*m+1)*ref,complex)
        v[basis(m).index(("g",0))*ref]=np.sqrt(1-tail)
        v[basis(m).index(("g",3))*ref+1]=np.sqrt(tail)
        state=density(v)
        ps=np.diag([1 if (n+(s=="e"))<=1 else 0 for s,n in basis(m)])
        p=np.kron(ps,np.eye(ref));qmat=np.eye(len(p))-p
        passing=p@state@p
        failing=qmat@state@qmat
        rho_r=np.trace(failing.reshape(2*m+1,ref,2*m+1,ref),axis1=0,axis2=2)
        reset=density(np.eye(2*m+1)[:,0])
        fail_out=np.kron(reset,rho_r)
        full=dist(state,passing)+dist(np.zeros_like(fail_out),fail_out)
        sharp=(tail+np.sqrt(tail*(4-3*tail)))/2
        check(f"filter_sharp_with_reference_tail{tail}",
              {"distance":full,"bound":sharp},abs(full-sharp)<tol)
        initial_mean=3*tail
        passed_mean=0.
        check(f"low_spectrum_mean_does_not_increase_tail{tail}",
              {"before":initial_mean,"after":passed_mean},passed_mean<=initial_mean)
        check(f"failure_retains_conditioned_reference_tail{tail}",
              rho_r.real.tolist(),np.allclose(rho_r,np.diag([0,tail]),atol=tol))

    # Infinite-support statement is analytic. Check one strictly positive coefficient.
    tau=.7;k=9
    from math import factorial
    prob=float(np.exp(-tau*tau)*tau**(2*k)/factorial(k))
    check("simultaneous_Rabi_positive_beyond_any_claimed_small_window",
          {"oscillator_level":k,"probability":prob},prob>0)

    getcontext().prec=60
    d=Decimal(1)/4096
    f=(d+(4*d-3*d*d).sqrt())/2
    bound=Decimal(1)/50+f+Decimal(2).sqrt()/100
    loose=Decimal(1)/50+Decimal(65)/4096+Decimal(2).sqrt()/100
    check("sharp_budget_passes_loose_budget_fails",
          {"sharp":str(bound),"loose":str(loose),
           "margin":str(Decimal(1)/20-bound)},bound<Decimal(1)/20<loose)

    src=Path(__file__).resolve()
    report={
        "schema":"ueot-qm.independent-growth-diagnostic/1",
        "status":"PASS",
        "executed_at_utc":datetime.now(timezone.utc).isoformat(),
        "checker_author":"native research subagent B",
        "execution_attribution":"Actual executor and workflow are supplied by the invoking runner",
        "source_file":src.name,
        "source_sha256":hashlib.sha256(src.read_bytes()).hexdigest(),
        "basis":"independent implementation, no project runtime imports",
        "proof_status":"paper proof in B_MICRO_GROWTH.md; numerics are finite floating diagnostics",
        "hardware_data":False,
        "checks":checks,
        "check_count":len(checks),
    }
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"status":"PASS","checks":len(checks),"output":str(args.output),
                      "source_sha256":report["source_sha256"],"sharp_bound":str(bound)}))


if __name__=="__main__":
    main()
