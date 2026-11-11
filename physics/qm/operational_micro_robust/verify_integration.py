#!/usr/bin/env python3
"""Independent source-to-CQ integration checks for the frozen v31.11 model.

Exact polynomial/rational checks are kept separate from floating execution of
the inherited source-tree interpreter. No simulated result is hardware data.
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
import sympy as sp

HERE = Path(__file__).resolve().parent
QM = HERE.parent
sys.path.insert(0, str(QM / "conditioning"))
from finite_conditioning import (Instrument, Leaf, Node, repeated_success_tree,
    backward_effects, full_leaf_law, normalized_accepted_law,
    conditioned_reference, cq_distance, expected_action_cost,
    independent_retry_cost)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def exact_checks() -> dict:
    checks = []
    def check(name, condition, detail=None):
        if not bool(condition):
            raise AssertionError(name)
        checks.append({"name": name, "status": "PASS_EXACT", "detail": detail})

    q = sp.symbols("q", real=True)
    delta = sp.Rational(1, 50)
    s = 1 - q / 2
    p0, p1, pf = s * (1-q), s*q, 1-s
    raw = {"f": pf, "0f": p0*pf, "1f": p1*pf,
           "00": p0**2, "01": p0*p1, "10": p1*p0, "11": p1**2}
    check("all seven raw terminal masses sum to one", sp.simplify(sum(raw.values())-1) == 0)
    check("source accepted mass is derived as s squared",
          sp.simplify(sum(raw[k] for k in ("00","01","10","11"))-s**2) == 0)
    for k, value in {"00":(1-q)**2,"01":q*(1-q),"10":q*(1-q),"11":q**2}.items():
        check("raw accepted block normalization "+k, sp.simplify(raw[k]/s**2-value)==0)
    check("success floor", s.subs(q,sp.Rational(13,25))**2==sp.Rational(1369,2500))

    law = {"00":sp.Rational(1,4)+delta**2,"11":sp.Rational(1,4)+delta**2,
           "01":sp.Rational(1,4)-delta**2,"10":sp.Rational(1,4)-delta**2}
    first = sp.Rational(1,2)
    after0, after1 = sp.Rational(312,625), sp.Rational(313,625)
    check("legal adaptive law 00", (1-first)*(1-after0)==law["00"])
    check("legal adaptive law 01", (1-first)*after0==law["01"])
    check("legal adaptive law 10", first*(1-after1)==law["10"])
    check("legal adaptive law 11", first*after1==law["11"])
    x = sp.symbols("x", nonnegative=True)
    u = delta**2-x**2
    # Complete-CQ block analysis gives max(x,u)+u, for 0<=x<=delta.
    # Case x>=u: delta-(x+u)=(delta-x)*(1-delta-x)>=0.
    check("uniform adaptive upper bound, first case factorization",
          sp.expand(delta-(x+u)-(delta-x)*(1-delta-x))==0)
    check("first case remaining factor nonnegative", 1-2*delta>0)
    check("uniform adaptive upper bound, second case", 2*delta**2<=delta)
    P=lambda v:{"00":(1-v)**2,"01":v*(1-v),"10":v*(1-v),"11":v**2}
    endpoints=[P(sp.Rational(1,2)-delta),P(sp.Rational(1,2)+delta)]
    endpoint_tv=sum(abs(endpoints[0][k]-endpoints[1][k]) for k in law)/2
    check("minimax lower bound from endpoint record laws", endpoint_tv/2==delta)
    check("memoryless worst-case comparison", delta*(1+delta)==sp.Rational(51,2500))
    check("adaptive nominal tradeoff", sum(abs(P(sp.Rational(1,2))[k]-law[k]) for k in law)/2==sp.Rational(1,1250))
    tail=sp.Rational(1,4096)
    total=sp.sqrt(tail)+tail+delta
    check("complete physical preparation plus robust policy meets frozen precision", total<sp.Rational(1,20), str(total))

    I=sp.I
    X=sp.Matrix([[0,1],[1,0]]); Y=sp.Matrix([[0,-I],[I,0]]); Z=sp.diag(1,-1)
    U0=sp.diag(1,(3+4*I)/5)
    U1=(3*sp.eye(2)-4*I*X)/5
    paulis=[X,Y,Z]
    rot=lambda U:sp.Matrix([[sp.simplify(sp.trace(a*U*b*U.conjugate().T)/2)
                            for b in paulis] for a in paulis])
    R0,R1=rot(U0),rot(U1)
    check("actual gates are unitary", sp.simplify(U0.conjugate().T*U0-sp.eye(2))==sp.zeros(2)
          and sp.simplify(U1.conjugate().T*U1-sp.eye(2))==sp.zeros(2))
    check("derived Bloch matrices are rotations", R0.T*R0==sp.eye(3) and R1.T*R1==sp.eye(3))
    ket=sp.Matrix([1,0]); left=U0*U1*ket; right=U1*U0*ket
    overlap=(left.conjugate().T*right)[0]
    d2=sp.simplify(1-overlap*sp.conjugate(overlap))
    check("actual CP composition noncommutes on a state", d2==sp.Rational(576,3125), str(d2))
    M0=(R0+R1)/2; power=M0*M0
    gap=sp.Rational(81,100)*sp.eye(3)-power.T*power
    minors=[sp.det(gap[:k,:k]) for k in range(1,4)]
    check("Sylvester certificate for two-step contraction below 9/10", all(v>0 for v in minors), [str(v) for v in minors])
    check("uniform perturbation contraction is 49/50", sp.Rational(9,10)+4*delta==sp.Rational(49,50))
    # G=0 and the invariant maximally mixed G=1 state are distinct fixed states.
    vacuum=sp.diag(1,0,0); sector=sp.diag(0,sp.Rational(1,2),sp.Rational(1,2))
    V0=sp.diag(1,1,(3+4*I)/5)
    V1=sp.diag(1,1,1); V1[1:3,1:3]=U1
    permutation=sp.Matrix([[1,0,0],[0,0,1],[0,1,0]])
    c_order_phase=sp.diag(1,(3+4*I)/5,1)
    check("independent checker basis bridge", permutation*c_order_phase*permutation.T==V0
          and permutation*V1*permutation.T==V1,
          "C uses [g0,e0,g1]; root and the Bloch proof use [g0,g1,e0].")
    for label,state in [("vacuum",vacuum),("G=1 mixed",sector)]:
        check("whole-system distinct fixed state: "+label,
              sp.simplify((1-q)*V0*state*V0.conjugate().T+q*V1*state*V1.conjugate().T-state)==sp.zeros(3))
    return {"checks":checks,"count":len(checks),"adaptive_bound":str(delta),
            "full_physical_bound":str(total),"full_physical_bound_decimal":str(float(total)),
            "precision":"1/20","contraction_bound":"49/50",
            "source_success_floor":"1369/2500","real_hardware_data":False}


def numerical_integration() -> dict:
    # The G<=1 order is |g,0>,|g,1>,|e,0>. R is a genuine untouched qubit.
    z=(3+4j)/5
    U0=np.diag([1,1,z]).astype(complex)
    U1=np.array([[1,0,0],[0,3/5,-4j/5],[0,-4j/5,3/5]],complex)
    gate=[np.kron(U0,np.eye(2)),np.kron(U1,np.eye(2))]
    identity=np.eye(6)
    vector=np.zeros(6,complex); vector[2]=1/np.sqrt(2); vector[5]=1/np.sqrt(2)
    rho=np.outer(vector,vector.conj())
    records={('f',),('0','f'),('1','f'),('0','0'),('0','1'),('1','0'),('1','1')}
    expected_weights={('0','0'):313/1250,('1','1'):313/1250,
                      ('0','1'):312/1250,('1','0'):312/1250}
    def instrument(weight):
        return Instrument({'0':(np.sqrt(1-weight)*gate[0],),
                           '1':(np.sqrt(weight)*gate[1],),
                           'f':(np.zeros_like(identity),)})
    adaptive=Node(instrument(0.5),{
        'f':Leaf(False),
        '0':Node(instrument(312/625),{'f':Leaf(False),'0':Leaf(True),'1':Leaf(True)}),
        '1':Node(instrument(313/625),{'f':Leaf(False),'0':Leaf(True),'1':Leaf(True)})})
    compiled,_=full_leaf_law(adaptive,rho)
    assert set(compiled)==records
    for h,w in expected_weights.items():
        U=gate[int(h[1])]@gate[int(h[0])]
        assert np.linalg.norm(compiled[h]-w*U@rho@U.conj().T)<1e-13
    rows=[]
    for q in [12/25,49/100,1/2,51/100,13/25]:
        s=1-q/2
        source=Instrument({'0':(np.sqrt(s*(1-q))*gate[0],),
                           '1':(np.sqrt(s*q)*gate[1],),
                           'f':(np.sqrt(1-s)*identity,)})
        source.validate_complete()
        tree=repeated_success_tree(source,{'0','1'},2)
        raw,accepted=full_leaf_law(tree,rho)
        assert set(raw)==records
        p,conditioned=normalized_accepted_law(raw,accepted)
        ref=conditioned_reference(tree,rho)
        constructed,_=full_leaf_law(ref.tree,ref.initial_state)
        H=backward_effects(tree,6)[()]
        assert abs(p-s*s)<1e-13 and np.linalg.norm(H-s*s*identity)<1e-12
        assert cq_distance(conditioned,constructed)<1e-12
        full_error=cq_distance(conditioned,compiled)
        x=abs(q-.5); u=(1/50)**2-x*x
        expected=max(x,u)+u
        assert abs(full_error-expected)<1e-12 and full_error<=.02+1e-12
        cost=independent_retry_cost(tree,rho,preparation=2,failed_reset=3,other_per_attempt=5)
        expected_cost=((1+s)+2+(1-s*s)*3+5)/(s*s)
        assert abs(expected_action_cost(tree,rho)-(1+s))<1e-12
        assert abs(cost['all_cost_per_output']-expected_cost)<1e-11
        # Adversarial complete-record guard: deleting all failure records changes
        # a raw source distribution by its failure probability, despite the same
        # conditional successful distribution.
        raw_source_vs_conditional=cq_distance(raw,conditioned)
        assert abs(raw_source_vs_conditional-(1-s*s))<1e-12
        rows.append({'q':q,'source_success':p,'seven_records_retained':True,
                     'backward_effect_residual':float(np.linalg.norm(H-s*s*identity)),
                     'inherited_interpreter_conditional_residual':cq_distance(conditioned,constructed),
                     'adaptive_full_cq_error':full_error,'analytic_value':expected,
                     'raw_source_vs_conditional_distance':raw_source_vs_conditional,
                     'illustrative_dimensionless_full_cost':cost['all_cost_per_output']})
    return {'rows':rows,'reference_dimension':2,'system_dimension':3,
            'input':'entangled |g,1;0_R>+|e,0;1_R>, normalized',
            'scope':'floating execution of inherited source-only finite interpreter; universal claims are analytic',
            'cost_units':'illustrative dimensionless bookkeeping, not measured hardware cost',
            'real_hardware_data':False}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output-dir',type=Path,required=True)
    args=parser.parse_args(); args.output_dir.mkdir(parents=True,exist_ok=True)
    consumed=[Path(__file__),QM/'conditioning/finite_conditioning.py',
              QM/'audits/OPERATIONAL_MICRO_ROBUST_v31.11/SHARED_MODEL.md']
    before={str(p.relative_to(QM)):digest(p) for p in consumed}
    exact=exact_checks(); numeric=numerical_integration()
    after={str(p.relative_to(QM)):digest(p) for p in consumed}
    if before!=after:raise RuntimeError('consumed source changed during execution')
    receipt={'schema':'ueot-qm.v31.11.independent-integration/1','status':'PASS',
             'executed_at_utc':datetime.now(timezone.utc).isoformat(),
             'command':[sys.executable,*sys.argv],
             'versions':{'python':sys.version,'platform':platform.platform(),
                         'numpy':np.__version__,'sympy':sp.__version__},
             'source_sha256':before,'source_unchanged_during_execution':True,
             'exact':exact,'floating':numeric,'new_hardware_data':False}
    (args.output_dir/'independent-integration.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'status':'PASS','exact_checks':exact['count'],'floating_cases':len(numeric['rows']),
                      'complete_physical_bound':exact['full_physical_bound_decimal'],
                      'real_hardware_data':False},indent=2))


if __name__=='__main__':main()
