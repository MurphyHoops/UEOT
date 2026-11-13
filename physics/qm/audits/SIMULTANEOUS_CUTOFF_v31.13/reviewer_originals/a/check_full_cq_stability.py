#!/usr/bin/env python3
"""Independent finite controls for the complete-CQ hybrid theorem.

This script imports no project model or root implementation. It checks a
state-dependent complete instrument tree, not merely scalar flag laws. Its
floating checks complement the analytic proof and do not establish its
universal/infinite-dimensional quantifiers.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import platform
import sys

import numpy as np


I = np.eye(2, dtype=complex)
X = np.array([[0, 1], [1, 0]], dtype=complex)
Z = np.diag([1., -1.]).astype(complex)
OUTCOMES = ("0", "1", "f")
HEIGHT = 3
TOL = 2e-11


def tn(a):
    return float(np.linalg.svd(a, compute_uv=False).sum())


def td(a, b):
    return tn(a - b) / 2


def rotate(pauli, angle):
    return np.cos(angle) * I - 1j * np.sin(angle) * pauli


def terminal(history):
    return len(history) == HEIGHT or (history and history[-1] == "f")


def policy(history):
    # Only depth and the last visible result are observed. Distinct histories
    # ending in the same symbol have identical action weights.
    if not history:
        return Fraction(2, 5)
    return Fraction(1, 4) if history[-1] == "0" else Fraction(3, 4)


def instrument(history, action, theta, comparison):
    depth = len(history)
    angle = theta + .17 * action + .09 * depth
    if comparison:
        angle += .021 * (1 + action) * (1 + depth)
    u = rotate(X, angle) @ rotate(Z, .13)
    failure = .11 + .02 * action
    t0, t1 = .20 + .10 * (depth % 2) + .05 * theta, .72 - .04 * depth
    d0 = np.diag(np.sqrt([t0, t1]))
    d1 = np.diag(np.sqrt([1 - t0, 1 - t1]))
    k0 = np.sqrt(1 - failure) * d0 @ u
    k1 = np.sqrt(1 - failure) * d1 @ u
    kf = np.sqrt(failure) * I
    # An unobserved Kraus refinement is summed inside its visible event.
    return {"0": (k0,), "1": (np.sqrt(.4)*k1, 1j*np.sqrt(.6)*k1), "f": (kf,)}


def apply_kraus(kraus, state, reference):
    result = np.zeros_like(state)
    for k in kraus:
        joint = np.kron(k, np.eye(reference))
        result += joint @ state @ joint.conj().T
    return result


def event_map(history, outcome, state, theta, comparison, reference):
    weight = float(policy(history))
    result = np.zeros_like(state)
    # The action coin here is hidden, with the same legal weights in E and F.
    # Its refinement is not accessible to subsequent policy decisions.
    for action, w in ((0, 1-weight), (1, weight)):
        result += w * apply_kraus(instrument(history, action, theta, comparison)[outcome],
                                  state, reference)
    return result


def continuation(state, history, theta, comparison, reference):
    if terminal(history):
        return {history: state}
    result = {}
    for outcome in OUTCOMES:
        child = event_map(history, outcome, state, theta, comparison, reference)
        result.update(continuation(child, history+(outcome,), theta, comparison, reference))
    return result


def prefixes(state, theta, reference):
    result = {}
    def visit(sigma, history):
        if terminal(history):
            return
        result[history] = sigma
        for outcome in OUTCOMES:
            visit(event_map(history, outcome, sigma, theta, True, reference), history+(outcome,))
    visit(state, ())
    return result


def cq_distance(a, b):
    if a.keys() != b.keys():
        raise ValueError("the complete record alphabets differ")
    return sum(td(a[h], b[h]) for h in a)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    checks = []
    def check(name, condition, detail=None):
        if not bool(condition):
            raise AssertionError((name, detail))
        checks.append({"name": name, "status": "PASS", "detail": detail})

    reference = 2
    psi = np.array([np.sqrt(.37), 0, 0, np.sqrt(.63)], dtype=complex)
    initial = np.outer(psi, psi.conj())
    rows = []
    for theta in (.0, .19, .41):
        exact = continuation(initial, (), theta, False, reference)
        finite = continuation(initial, (), theta, True, reference)
        pref = prefixes(initial, theta, reference)
        check("all stopping leaves retained", len(exact) == len(finite) == 15)
        for law, name in ((exact, "exact"), (finite, "comparison")):
            trace = sum(np.trace(v).real for v in law.values())
            check(name+" complete terminal trace", abs(trace-1) < TOL, float(trace))
        check("legal weights coincide within observation fibre",
              policy(("0", "1")) == policy(("1", "1")))
        identity_sum = {h: np.zeros_like(v) for h, v in exact.items()}
        local_total = 0.
        local_rows = []
        for history, sigma in pref.items():
            for action in (0, 1):
                for comparison in (False, True):
                    inst = instrument(history, action, theta, comparison)
                    effect = sum(k.conj().T @ k for ks in inst.values() for k in ks)
                    check("complete CP instrument", np.linalg.norm(effect-I) < TOL)
            d_h = 0.
            for outcome in OUTCOMES:
                delta = (event_map(history, outcome, sigma, theta, False, reference)
                         - event_map(history, outcome, sigma, theta, True, reference))
                d_h += tn(delta)/2
                suffix = continuation(delta, history+(outcome,), theta, False, reference)
                for h, value in suffix.items():
                    identity_sum[h] += value
            mass = float(np.trace(sigma).real)
            check("positive prefix, local discrepancy bounded by mass", d_h <= mass+TOL)
            local_total += d_h
            local_rows.append({"history": "".join(history), "mass": mass, "d_h": d_h})
        error = cq_distance(exact, finite)
        residual = sum(tn(identity_sum[h] - (exact[h]-finite[h])) for h in exact)
        check("exact finite-tree hybrid identity", residual < TOL, residual)
        check("complete CQ error below unnormalized-prefix sum", error <= local_total+TOL,
              {"complete_error": error, "prefix_bound": local_total})
        record_tv = sum(abs(np.trace(exact[h]-finite[h])) for h in exact)/2
        check("record-only data underestimates joint-state error", error > record_tv+1e-5,
              {"full": error, "record_TV": float(record_tv)})
        # State-dependent labels are present: exact and F prefixes need not
        # have the same masses. The telescoping identity remains valid.
        exact_first = event_map((), "0", initial, theta, False, reference)
        finite_first = event_map((), "0", initial, theta, True, reference)
        check("state-dependent readout produces unequal branch mass",
              abs(np.trace(exact_first-finite_first)) > 1e-6)
        acceptance = {h for h in exact if len(h)==HEIGHT and "f" not in h and h[-1]=="1"}
        p = sum(np.trace(exact[h]).real for h in acceptance)
        q = sum(np.trace(finite[h]).real for h in acceptance)
        post = sum(td(exact[h]/p, finite[h]/q) for h in acceptance)
        check("same-event postselection uses complete-output bound",
              abs(p-q) <= error+TOL and post <= min(1., error/max(p,q))+TOL,
              {"p": float(p), "q": float(q), "post": post})
        rows.append({"theta": theta, "complete_error": error, "prefix_bound": local_total,
                     "identity_residual": residual, "prefixes": local_rows})

    rho0 = np.diag([1., 0.]).astype(complex)
    rho1 = X @ rho0 @ X
    swapped_e = {("0",): rho0/2, ("1",): rho1/2}
    swapped_f = {("0",): rho1/2, ("1",): rho0/2}
    check("negative control: forgotten channel matches", td(sum(swapped_e.values()),sum(swapped_f.values())) < TOL)
    check("negative control: complete labels remain maximally distinct", abs(cq_distance(swapped_e,swapped_f)-1)<TOL)

    rare = float(Fraction(1, 1000))
    rare_e = {("stop",): (1-rare)*rho0, ("rare",): rare*rho1}
    rare_f = {("stop",): (1-rare)*rho0, ("rare",): rare*rho0}
    check("rare prefix carries its mass", abs(cq_distance(rare_e,rare_f)-rare)<TOL)
    check("rare conditional discrepancy is not the complete discrepancy", td(rho1,rho0)==1.)
    zero = np.zeros((2, 2), dtype=complex)
    check("zero-mass prefix is evaluated without normalization", td(X@zero@X,zero)==0.)

    # C-MICRO-03: the canonical G<=1 Galerkin compression of sigma_x X.
    # Basis is (g0,g1,e0); the full compressed X^2 form is diag(1,3,1).
    hk = np.array([[0.,0.,0.],[0.,0.,1.],[0.,1.,0.]])
    x2 = np.diag([1.,3.,1.])
    val, vec = np.linalg.eigh(hk)
    for area in (.03, .10, .71):
        uk = (vec*np.exp(-1j*area*val))@vec.conj().T
        ket = np.array([0.,0.,1.], dtype=complex)
        final = uk@ket
        moment = float(np.vdot(final,x2@final).real)
        expected = 1+2*np.sin(area)**2
        check("C-MICRO-03 exact finite formula", abs(moment-expected)<TOL,
              {"area":area,"finite_X2":moment,"exact_infinite_X2":1.})
        check("C-MICRO-03 finite prefixes do not retain the exact invariant", moment>1+1e-4)

    receipt={"schema":"ueot-qm.full-cq-prefix-check/1","status":"PASS",
             "created_at_utc":datetime.now(timezone.utc).isoformat(),
             "checker_author":"native research agent A",
             "script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
             "runtime":{"python":sys.version,"executable":sys.executable,
                        "platform":platform.platform(),"numpy":np.__version__},
             "checks":checks,"check_count":len(checks),"parameter_rows":rows,
             "scope":"finite floating controls for the analytical prefix identity and Galerkin invariant counterexample",
             "new_hardware_data":False,"universal_proof_by_finite_testing":False}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(receipt,indent=2)+"\n")
    print(json.dumps({"status":"PASS","checks":len(checks),"parameter_rows":len(rows),"new_hardware_data":False}))


if __name__=="__main__":
    main()
