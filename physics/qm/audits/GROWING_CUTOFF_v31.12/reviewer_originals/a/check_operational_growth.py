#!/usr/bin/env python3
"""Independent finite controls for A's new written bridge; no project imports."""
from __future__ import annotations
import hashlib
import json
import math
import platform
from datetime import datetime, timezone
from fractions import Fraction
from pathlib import Path

import numpy as np
import scipy
from scipy.linalg import expm

TOL = 3e-12
checks = []


def check(name, condition, **data):
    checks.append({"name": name, "pass": bool(condition), **data})
    if not condition:
        raise AssertionError(name)


def close(name, a, b):
    error = float(np.linalg.norm(np.asarray(a)-np.asarray(b)))
    check(name, error < TOL, residual=error)


def basis(m):
    return [(0, 0)] + [pair for g in range(1, m+1)
                       for pair in ((1, g-1), (0, g))]


def inclusion(m, cap):
    source, target = basis(m), basis(cap)
    out = np.zeros((len(target), len(source)), complex)
    for j, x in enumerate(source):
        out[target.index(x), j] = 1
    return out


def generator(m, blue):
    states = basis(m)
    out = np.zeros((len(states), len(states)), complex)
    for j, (e, n) in enumerate(states):
        if blue:
            other, coefficient = ((1, n+1), math.sqrt(n+1)) if e == 0 else ((0, n-1), math.sqrt(n))
        else:
            other, coefficient = ((1, n-1), math.sqrt(n)) if e == 0 else ((0, n+1), math.sqrt(n+1))
        if other in states:
            out[states.index(other), j] = coefficient
    return out


def blue_rect(m, beta):
    states, targets = basis(m), basis(m+2)
    out = np.zeros((len(targets), len(states)), complex)
    for j, (e, n) in enumerate(states):
        frequency = math.sqrt(n+1) if e == 0 else math.sqrt(n)
        out[targets.index((e, n)), j] = math.cos(beta*frequency)
        if frequency:
            other = (1, n+1) if e == 0 else (0, n-1)
            out[targets.index(other), j] = -1j*math.sin(beta*frequency)
    return out


def red(m, alpha):
    return expm(-1j*alpha*generator(m, False))


def phase(m, phi):
    return np.diag([np.exp(-1j*phi*e) for e, _ in basis(m)])


def path(r, N, q, phi, alpha, beta, weighted=False):
    m = N
    out = np.eye(2*N+1, dtype=complex)
    s = 1-q/2
    for label in r:
        if label == "f":
            if weighted:
                out *= math.sqrt(1-s)
            break
        if label == "0":
            gate = phase(m, phi)
            coefficient = math.sqrt(s*(1-q))
        else:
            gate = blue_rect(m, beta) @ red(m, alpha)
            coefficient = math.sqrt(s*q)
            m += 2
        out = gate @ out
        if weighted:
            out *= coefficient
    return inclusion(m, N+4) @ out


def td(a, b):
    difference = a-b
    return float(np.abs(np.linalg.eigvalsh((difference+difference.conj().T)/2)).sum()/2)


def main():
    for m in range(6):
        for beta in (0.0, 0.01, -0.23):
            v = blue_rect(m, beta)
            close(f"blue_rect_isometry_m{m}_b{beta}", v.conj().T@v, np.eye(2*m+1))
            big = expm(-1j*beta*generator(m+2, True)) @ inclusion(m, m+2)
            close(f"derived_rect_matches_exponential_m{m}_b{beta}", v, big)
    beta = 0.17
    m = 3
    full = blue_rect(m, beta)
    truncated = inclusion(m, m+2).conj().T@full
    j = basis(m).index((0, m))
    lost = 1-float(np.vdot(truncated[:,j], truncated[:,j]).real)
    close("fixed_window_lost_probability", lost, math.sin(beta*math.sqrt(m+1))**2)
    check("fixed_window_is_not_TP", lost > 0.1, lost_probability=lost)

    N, q, phi, alpha, beta = 1, 0.517, -math.atan2(4,3), math.acos(3/5), 0.01
    cap = N+4
    labels = ["f", "0f", "1f", "00", "01", "10", "11"]
    weighted = {r: path(r,N,q,phi,alpha,beta,True) for r in labels}
    total = sum(k.conj().T@k for k in weighted.values())
    accepted = sum(weighted[r].conj().T@weighted[r] for r in labels if "f" not in r)
    close("complete_seven_record_source", total, np.eye(2*N+1))
    close("source_acceptance_derived", accepted, (1-q/2)**2*np.eye(2*N+1))
    actual0 = phase(cap, phi)
    actual1 = expm(-1j*beta*generator(cap,True)) @ red(cap,alpha)
    for r in labels:
        whole = inclusion(N,cap)
        for char in r:
            if char != "f":
                whole = (actual0 if char == "0" else actual1) @ whole
        close(f"terminal_embedding_{r}", path(r,N,q,phi,alpha,beta), whole)

    Q = {"00": Fraction(313,1250), "01": Fraction(312,1250),
         "10": Fraction(312,1250), "11": Fraction(313,1250)}
    expected = sum(prob*r.count("1") for r,prob in Q.items())
    check("exact_deployed_blue_count", expected == 1, value=str(expected))
    for slot in (0,1):
        check(f"exact_label1_marginal_{slot}", sum(prob for r,prob in Q.items() if r[slot]=="1") == Fraction(1,2))

    psi = np.zeros((2*N+1)*2, complex)
    psi[2*basis(N).index((1,0))] = 1/math.sqrt(2)
    psi[2*basis(N).index((0,1))+1] = 1/math.sqrt(2)
    rho = np.outer(psi,psi.conj())
    full_difference = 0.0
    robust_difference = 0.0
    for r,prob in Q.items():
        vb = np.kron(path(r,N,q,phi,alpha,beta), np.eye(2))
        v0 = np.kron(path(r,N,q,phi,alpha,0.0), np.eye(2))
        rhob, rho0 = vb@rho@vb.conj().T, v0@rho@v0.conj().T
        full_difference += float(prob)*td(rhob,rho0)
        p = q**r.count("1")*(1-q)**r.count("0")
        robust_difference += td(p*rhob, float(prob)*rhob)
    check("reference_assisted_pulse_omission_bound", full_difference <= abs(beta)*math.sqrt(2)+TOL,
          actual_complete_CQ_distance=full_difference, bound=abs(beta)*math.sqrt(2))
    tv = sum(abs(q**r.count("1")*(1-q)**r.count("0")-float(p)) for r,p in Q.items())/2
    close("robust_distance_is_full_record_TV", robust_difference, tv)

    # A source/reference entangled input makes incorrect failure-reference reset visible.
    entangled = np.array([1,0,0,1],complex)/math.sqrt(2)
    original = np.outer(entangled,entangled.conj())
    P = np.diag([1,0])
    Qtail = np.diag([0,1])
    tail = np.kron(Qtail,np.eye(2)) @ original @ np.kron(Qtail,np.eye(2))
    reference_tail = np.trace(tail.reshape(2,2,2,2),axis1=0,axis2=2)
    correct_fail = np.kron(P,reference_tail)
    wrong_fail = 0.5*np.kron(P,np.eye(2)/2)
    close("failure_reference_conditional", reference_tail, np.diag([0,0.5]))
    close("wrong_unconditional_reference_distance", td(correct_fail,wrong_fail), 0.25)
    for d in (0.0,1/4096,0.2,0.5,0.9,1.0):
        vec = np.array([math.sqrt(1-d),math.sqrt(d)],complex)
        state = np.outer(vec,vec.conj())
        passout = P@state@P
        difference = (np.abs(np.linalg.eigvalsh(state-passout)).sum()+d)/2
        bound = (math.sqrt(d*(4-3*d))+d)/2
        close(f"sharp_filter_pure_saturation_{d}", difference,bound)

    # Numerical diagnostic: cutoff postselection on an energy-diagonal random input.
    probabilities = np.array([0.1,0.15,0.2,0.05,0.2,0.1,0.2])
    energies = np.arange(len(probabilities))
    for cutoff in range(6):
        low = probabilities[:cutoff+1]
        conditioned_mean = float(np.dot(energies[:cutoff+1],low)/low.sum())
        full_mean = float(np.dot(energies,probabilities))
        check(f"low_spectral_filter_mean_{cutoff}",conditioned_mean<=full_mean+TOL,
              conditioned_mean=conditioned_mean, initial_mean=full_mean)
    prep = (math.sqrt((1/4096)*(4-3/4096))+1/4096)/2
    bound = 1/50+prep+math.sqrt(2)/100
    check("combined_bound_below_frozen_precision", bound<1/20,
          full_bound=bound,remaining_allowance=1/20-bound)
    check("old_loose_filter_does_not_certify_same_target", 1/50+65/4096+math.sqrt(2)/100>1/20)
    result = {
        "schema":"ueot-qm.recovery-a-independent-controls/1",
        "status":"PASS",
        "recorded_at_utc":datetime.now(timezone.utc).isoformat(),
        "source_baseline":"aea2fceef3c62cc8dc749b6cbb1b40a7d89df80d",
        "execution":"fresh execution of reconstructed controls; no claim of recovering interrupted outputs",
        "checker_author":"native research subagent A",
        "execution_attribution":"Actual executor, checkout and workflow identity are supplied by the invoking runner; checker authorship is not executor identity",
        "python":platform.python_version(),"numpy":np.__version__,"scipy":scipy.__version__,
        "checker_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "new_hardware_data":False,
        "evidence_scope":"Exact rational probability checks and floating finite-matrix diagnostics; universal claims are paper proofs, not Lean",
        "checks":checks,
        "check_count":len(checks)
    }
    output=Path(__file__).with_name("A_INDEPENDENT_CHECK.json")
    output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"status":result["status"],"check_count":len(checks),"full_bound":bound,"output":str(output)}))


if __name__=="__main__":
    main()
