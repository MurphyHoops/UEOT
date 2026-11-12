#!/usr/bin/env python3
"""Run the new source/rectangular/conditioning/physical-filter integration.

Exact all-domain proofs are in the audit and chapter 68; these finite floating
checks are independent comparisons, not an inference from sampled parameters.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys

import numpy as np
import sympy as sp

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "conditioning"))
from finite_conditioning import (Instrument, repeated_success_tree, backward_effects,
                                 full_leaf_law, normalized_accepted_law,
                                 conditioned_reference, cq_distance)
from model import (basis, red, phase, blue_restriction, stage_gates,
                   ambient_gates, embedding, rectangular_law)


def trace_distance(a, b):
    return float(np.linalg.svd(a - b, compute_uv=False).sum() / 2)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--model", type=Path, default=HERE / "frozen_model.json")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    model = json.loads(args.model.read_text())
    tol = float(Fraction(model["numerical_absolute_tolerance"]))
    if not 0 < tol <= 1e-10:
        raise ValueError("frozen floating tolerance must be positive and at most 1e-10")
    expected_contract = {
        "theta": ["q", "phi", "alpha", "beta"],
        "s_relation": "1-q/2", "source_height": 2, "stop_on": "f",
        "source_records": ["f", "0f", "1f", "00", "01", "10", "11"],
        "accept": ["00", "01", "10", "11"],
        "label1_gate_order": "V1=B_beta U1; red first, then blue",
        "label0_gate": "V0=U0", "failure_gate": "identity",
        "failure_reset_state": "g0 on S, preserving the unnormalized failure-conditioned reference marginal",
    }
    if any(model.get(k) != v for k, v in expected_contract.items()):
        raise ValueError("model semantics differ from this interpreter's declared contract")
    weights = [Fraction(model[k]) for k in ["adaptive_first_label1_weight",
               "adaptive_second_label1_given_0", "adaptive_second_label1_given_1"]]
    policy = tuple(float(w) for w in weights)
    alpha = np.arctan2(float(Fraction(model["exchange_sin"])),
                       float(Fraction(model["exchange_cos"])))
    phi = -np.arctan2(float(Fraction(model["phase_imag"])),
                     float(Fraction(model["phase_real"])))
    n, ref = model["numerical_cutoff_N"], model["reference_dimension"]
    if n != 1 or ref != 2 or model["source_height"] != 2:
        raise ValueError("this witness is explicitly the N=1 two-step qubit-reference example")
    checks = []

    def check(name, ok, detail=None):
        if not bool(ok):
            raise AssertionError((name, detail))
        checks.append({"name": name, "status": "PASS", "detail": detail})

    # Rational raw masses, success effect and declared cost counting are not
    # taken from a target-certificate field.
    q = sp.symbols("q", real=True)
    s = 1 - q / 2
    raw = {"f": 1 - s, "0f": s * (1-q) * (1-s), "1f": s*q*(1-s),
           "00": s*s*(1-q)**2, "01": s*s*q*(1-q),
           "10": s*s*q*(1-q), "11": s*s*q*q}
    check("exact seven-leaf normalization", sp.simplify(sum(raw.values()) - 1) == 0)
    check("exact accepted probability", sp.simplify(sum(raw[k] for k in ["00","01","10","11"]) - s*s) == 0)
    source_calls = sum(v * k.count("1") for k, v in raw.items())
    check("read-flag-first source blue count", sp.simplify(source_calls - s*q*(1+s)) == 0)
    w,w0,w1 = map(sp.Rational,weights)
    qlaw = {"00": (1-w)*(1-w0), "01": (1-w)*w0,
            "10": w*(1-w1), "11": w*w1}
    check("frozen policy is the reviewed design policy",
          qlaw=={"00":sp.Rational(313,1250),"11":sp.Rational(313,1250),
                 "01":sp.Rational(312,1250),"10":sp.Rational(312,1250)})
    check("compiled selected blue mean is one", sum(v*k.count("1") for k,v in qlaw.items()) == 1)
    check("coherent schedule source slots", sp.simplify(sum(v*len(k) for k,v in raw.items())-(1+s)) == 0)

    # A fixed entangled input, G=1, plus every column's isometry check below.
    vector = np.zeros((2*n+1)*ref, complex)
    vector[2] = vector[5] = 1 / np.sqrt(2)
    rho = np.outer(vector, vector.conj())
    records = {tuple(x) for x in model["source_records"]}
    rows = []
    for beta_text in model["numerical_beta_values"]:
        beta = float(Fraction(beta_text))
        for current in [n, n+2]:
            gates = stage_gates(current, phi, alpha, beta)
            for label, gate in zip(["0", "1", "f"], gates):
                residual = np.linalg.norm(gate.conj().T @ gate - np.eye(2*current+1))
                check(f"rectangular isometry M={current}, beta={beta_text}, label={label}", residual < tol, float(residual))
            # A separately implemented block-unitary completion agrees on reachable
            # columns; no vector at the excluded upper boundary is assumed exact.
            ambient = ambient_gates(n+4, phi, alpha, beta)
            for label, local, whole in zip(["0", "1", "f"], gates, ambient):
                residual = np.linalg.norm(whole @ embedding(current,n+4)
                    - embedding(current+2,n+4) @ local)
                check(f"reachable-column intertwining M={current}, beta={beta_text}, label={label}", residual < tol, float(residual))
        for q_text in model["numerical_q_values"]:
            qv = float(Fraction(q_text)); sv = 1-qv/2
            large = n+4
            gates = [np.kron(u,np.eye(ref)) for u in ambient_gates(large,phi,alpha,beta)]
            identity = np.eye((2*large+1)*ref)
            inst = Instrument({"0":(np.sqrt(sv*(1-qv))*gates[0],),
                               "1":(np.sqrt(sv*qv)*gates[1],),
                               "f":(np.sqrt(1-sv)*identity,)})
            inst.validate_complete()
            tree = repeated_success_tree(inst,{"0","1"},2)
            j = np.kron(embedding(n,large),np.eye(ref))
            initial = j @ rho @ j.conj().T
            original, accepted = full_leaf_law(tree,initial)
            rectangular = rectangular_law(rho,n,ref,qv,phi,alpha,beta)
            check("all original seven records retained", set(original)==set(rectangular)==records)
            raw_error = cq_distance(original, rectangular)
            check("old complete source interpreter equals growth recursion",raw_error<tol,raw_error)
            p, target = normalized_accepted_law(original,accepted)
            h = backward_effects(tree,len(initial))[()]
            check("derived backward effect is scalar s squared", np.linalg.norm(h-sv*sv*identity)<tol)
            check("derived source success",abs(p-sv*sv)<tol)
            constructed = conditioned_reference(tree,initial)
            explicit,_ = full_leaf_law(constructed.tree,constructed.initial_state)
            check("inherited source-only conditioned construction",cq_distance(target,explicit)<tol)
            compiled = rectangular_law(rho,n,ref,qv,phi,alpha,beta,compiled=True,policy=policy)
            omitted = rectangular_law(rho,n,ref,qv,phi,alpha,0.,compiled=True,policy=policy)
            x=abs(qv-.5); u=(1/50)**2-x*x
            actual = cq_distance(target,compiled)
            check("same gates reduce full CQ distance to path TV",abs(actual-(max(x,u)+u))<tol)
            omission = cq_distance(compiled,omitted)
            check("blue omission finite witness respects analytic energy bound",omission<=abs(beta)*np.sqrt(2)+tol)
            rows.append({"q":q_text,"beta":beta_text,"raw_interpreter_residual":raw_error,
                         "conditional_full_cq_error":actual,"blue_omission_error":omission,
                         "bound_on_omission":abs(beta)*np.sqrt(2),"source_success":p})

    # Fixed-window compression is not complete: a ground state at the boundary
    # leaks to |e,N+1>. Check the map's mass, not a Kraus commutator.
    beta=.3
    full=blue_restriction(n,beta)
    compressed=full[:2*n+1,:]
    boundary=basis(n).index(("g",n))
    loss=1-float(np.sum(abs(compressed[:,boundary])**2))
    check("negative control: fixed carrier loses actual CP probability",loss>1e-3 and abs(loss-np.sin(beta*np.sqrt(n+1))**2)<tol,loss)
    # CP maps really fail to commute, rather than merely having anticommuting
    # matrix representatives (which could differ only by a phase).
    ket=np.zeros(2*(n+2)+1,complex);ket[1]=1
    aa=ambient_gates(n+2,phi,alpha,.3)[0]
    bb=ambient_gates(n+2,phi,alpha,.3)[1]
    left=aa@bb@ket;right=bb@aa@ket
    noncommute=trace_distance(np.outer(left,left.conj()),np.outer(right,right.conj()))
    check("noncommuting actual CP compositions",noncommute>1e-3,noncommute)

    # Nonzero physical-filter failure with entangled reference. Here the input
    # is supported at G<=2; the ideal source requires a common G<=6 output.
    tail=float(Fraction(model["analytic_energy_budget"])/(model["analytic_cutoff_N"]+1))
    v=np.zeros(5*ref,complex);v[0]=np.sqrt(1-tail);v[3*ref+1]=np.sqrt(tail)
    state=np.outer(v,v.conj())
    projection=np.kron(np.diag([1,1,1,0,0]),np.eye(ref))
    kept=projection@state@projection
    rejected=(np.eye(10)-projection)@state@(np.eye(10)-projection)
    failure_r=np.trace(rejected.reshape(5,ref,5,ref),axis1=0,axis2=2)
    full_r=np.trace(state.reshape(5,ref,5,ref),axis1=0,axis2=2)
    reset=np.zeros((13,13),complex);reset[0,0]=1
    failure=np.kron(reset,failure_r)
    qv=float(Fraction(model["q_interval"][1]));beta=float(Fraction(model["beta_abs_bound"]))
    exact=rectangular_law(state,2,ref,qv,phi,alpha,beta)
    source_success=(1-qv/2)**2
    exact={h:(b/source_success if "f" not in h else np.zeros_like(b)) for h,b in exact.items()}
    for use_beta,label in [(beta,"full blue"),(0.,"omitted blue")]:
        reduced=rectangular_law(kept[:6,:6],1,ref,qv,phi,alpha,use_beta,compiled=True,policy=policy)
        j=np.kron(embedding(5,6),np.eye(ref))
        actual={("pass",)+h:j@b@j.conj().T for h,b in reduced.items()}
        actual[("prep_fail",)]=failure
        ideal={("pass",)+h:b for h,b in exact.items()}
        ideal[("prep_fail",)]=np.zeros_like(failure)
        error=cq_distance(ideal,actual)
        bound=.02+(np.sqrt(4*tail-3*tail*tail)+tail)/2
        if use_beta==0:bound+=abs(beta)*np.sqrt(2)
        check("complete physical filter integrated: "+label,error<=bound+tol,error)
        check("complete physical trace retained: "+label,abs(sum(np.trace(b).real for b in actual.values())-1)<tol)
    wrong_failure=np.kron(reset,tail*full_r)
    reference_error=trace_distance(failure,wrong_failure)
    check("negative control: unconditional reference substitution changes output",reference_error>0,reference_error)
    # Label records alone cannot identify beta. This example gives identical
    # weights but orthogonal final states on word01 for beta=pi/2 vs zero.
    vac=np.zeros((3*ref,3*ref),complex);vac[0,0]=1
    pulse=rectangular_law(vac,1,ref,.5,phi,alpha,np.pi/2,compiled=True,policy=policy)
    no_pulse=rectangular_law(vac,1,ref,.5,phi,alpha,0.,compiled=True,policy=policy)
    check("negative control: same flag counts for different beta",all(abs(np.trace(pulse[h])-np.trace(no_pulse[h]))<tol for h in pulse))
    beta_gap=cq_distance(pulse,no_pulse)
    check("negative control: flags do not certify the requested terminal accuracy",beta_gap>=312/1250-tol,beta_gap)

    report={"schema":"ueot-qm.growing-cutoff-integration/1","status":"PASS",
            "created_at_utc":datetime.now(timezone.utc).isoformat(),
            "model_sha256":hashlib.sha256(args.model.read_bytes()).hexdigest(),
            "script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "checks":checks,"check_count":len(checks),"parameter_rows":rows,
            "system_input_dimension":3,"reference_dimension":2,"ordinary_output_dimension":11,
            "filter_control_output_dimension":13,"floating_absolute_tolerance":tol,
            "filter_control":{"numeric_filter_cutoff":1,"input_support_max_G":2,
                              "chosen_exact_tail_mass":"1/4096",
                              "analytic_cutoff_4095_was_numerically_executed":False},
            "scope":"exact rational mass/cost identities and finite floating source comparisons; all-domain proofs remain analytic",
            "new_hardware_data":False}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"status":"PASS","checks":len(checks),"parameter_rows":len(rows),"new_hardware_data":False}))


if __name__=="__main__":main()
