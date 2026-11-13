#!/usr/bin/env python3
"""Source-only conditioning and independent complete-output comparisons.

Finite floating controls do not establish the universal analytic statements.
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
from finite_conditioning import (Instrument, repeated_success_tree, full_leaf_law,
    normalized_accepted_law, backward_effects, conditioned_reference, cq_distance)
from model import (basis, embedding, gates, hamiltonian, law, Q, RECORDS,
                   raw_weights, remainder_float)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    checks, rows = [], []
    def check(name, ok, detail=None):
        if not bool(ok): raise AssertionError((name, detail))
        checks.append({"name":name, "status":"PASS", "detail":detail})
    tol = 2e-11
    q = sp.Symbol("q", real=True); s=1-q/2
    raw=raw_weights(q)
    check("original complete seven-leaf mass", sp.simplify(sum(raw.values())-1)==0)
    check("source-derived accepted mass", sp.simplify(sum(raw[r] for r in Q)-s*s)==0)
    check("source calls use actual stopping", sp.simplify(sum(w*r.count('1') for r,w in raw.items())-s*q*(1+s))==0)
    check("compiled average drive calls", sum(w*r.count('1') for r,w in Q.items())==1)
    check("policy masses sum to one", sum(Q.values())==1)
    n,l,ref=1,3,2; k=n+2*l; large=17
    psi=np.zeros(3*ref,complex);psi[2]=psi[5]=1/np.sqrt(2)
    rho0=np.outer(psi,psi.conj())
    rho=embedding(n,k,ref)@rho0@embedding(n,k,ref).conj().T
    for x in [.02,.06,.1]:
        vv=[np.kron(v,np.eye(ref)) for v in gates(k,x)]
        unit=np.eye(len(rho))
        for i,v in enumerate(vv):check(f"finite Galerkin unitary x={x},label={i}",np.linalg.norm(v.conj().T@v-unit)<tol)
        for qv in [.48,.5,.52]:
            sv=1-qv/2
            source=Instrument({'0':(np.sqrt(sv*(1-qv))*vv[0],),'1':(np.sqrt(sv*qv)*vv[1],),'f':(np.sqrt(1-sv)*unit,)})
            source.validate_complete()
            tree=repeated_success_tree(source,{'0','1'},2)
            output,accepted=full_leaf_law(tree,rho)
            direct=law(rho,k,ref,qv,x)
            check("all seven source labels retained",set(output)==set(map(tuple,RECORDS)))
            check("old interpreter agrees with direct source",cq_distance(output,direct)<tol)
            effect=backward_effects(tree,len(rho))[()]
            check("backward effect derived as scalar",np.linalg.norm(effect-sv*sv*unit)<tol)
            p,target=normalized_accepted_law(output,accepted)
            construction=conditioned_reference(tree,rho)
            conditioned,_=full_leaf_law(construction.tree,construction.initial_state)
            check("source-only conditional constructor",cq_distance(target,conditioned)<tol)
            deployed=law(rho,k,ref,qv,x,compiled=True)
            path_tv=sum(abs(float(Q[r])-((1-qv)**(2-r.count('1'))*qv**r.count('1'))) for r in Q)/2
            actual=cq_distance(target,deployed)
            check("same-source full CQ error equals path TV",abs(actual-path_tv)<tol,actual)
            check("frozen robust design tolerance",actual<=.02+tol)
            # A larger Galerkin matrix is a diagnostic reference only. Both
            # have their own analytic remainder; it is never called exact.
            bigrho=embedding(n,large,ref)@rho0@embedding(n,large,ref).conj().T
            big=law(bigrho,large,ref,qv,x,compiled=True)
            j=embedding(k,large,ref)
            embedded={r:j@b@j.conj().T for r,b in deployed.items()}
            discrepancy=cq_distance(big,embedded)
            analytic=sum(float(w)*(remainder_float(n,l,r.count('1')*Fraction(str(x)))+
                       remainder_float(n,(large-n)//2,r.count('1')*Fraction(str(x)))) for r,w in Q.items())
            check("two genuine Galerkin cutoffs respect two remainder budgets",discrepancy<=analytic+tol,discrepancy)
            rows.append({'q':qv,'x':x,'finite_compiler_error':actual,'larger_cutoff_discrepancy':discrepancy,'two_remainder_bound':analytic,'source_success':p})
    # CP maps, not representatives alone, are tested for noncommutation.
    v0,v1=gates(k,.2);z=np.zeros(2*k+1,complex);z[0]=1
    a=v0@v1@z;b=v1@v0@z
    cp_gap=np.sqrt(max(0.,1-abs(np.vdot(a,b))**2))
    check("noncommuting actual CP compositions",cp_gap>1e-3,cp_gap)
    # The wrong compressed unitary is TNI and loses full records, whereas
    # exp(-i P H P) is unitary. This prevents an implementation shortcut.
    vbig=gates(large,.3)[1];j=embedding(1,large)
    compressed=j.conj().T@vbig@j
    deficit=1-np.linalg.norm(compressed[:,1])**2
    check("projected exact evolution is not a complete finite gate",deficit>1e-3,float(deficit))
    # Nonzero filter failure, including its actual reference conditional state.
    tail=Fraction(1,4096)
    pvec=np.zeros(5*ref,complex);pvec[0]=np.sqrt(1-float(tail));pvec[7]=np.sqrt(float(tail))
    source_rho=np.outer(pvec,pvec.conj());proj=np.kron(np.diag([1,1,1,0,0]),np.eye(ref))
    keep=proj@source_rho@proj;reject=(np.eye(10)-proj)@source_rho@(np.eye(10)-proj)
    failure_r=np.trace(reject.reshape(5,ref,5,ref),axis1=0,axis2=2)
    whole_r=np.trace(source_rho.reshape(5,ref,5,ref),axis1=0,axis2=2)
    jk=embedding(2,k,ref);passed=jk@keep@jk.conj().T
    prepared=law(passed,k,ref,.52,.06,compiled=True)
    reset=np.zeros((2*k+1,2*k+1));reset[0,0]=1
    prepared[('prep_fail',)]=np.kron(reset,failure_r)
    check("physical preparation and all terminal records have trace one",abs(sum(np.trace(b).real for b in prepared.values())-1)<tol)
    wrong=np.kron(reset,float(tail)*whole_r)
    failure_gap=np.linalg.svd(prepared[('prep_fail',)]-wrong,compute_uv=False).sum()/2
    check("unconditional reference replacement is detectably wrong",failure_gap>0,float(failure_gap))
    # Calibration cannot validate all channels from a single tester family.
    r0=law(rho,k,ref,.5,0.,compiled=True);r1=law(rho,k,ref,.5,.4,compiled=True)
    check("all flag distributions identical for different drives",all(abs(np.trace(r0[r])-np.trace(r1[r]))<tol for r in r0))
    check("same flags coexist with different complete output",cq_distance(r0,r1)>.1,cq_distance(r0,r1))
    report={'schema':'ueot-qm.simultaneous-source-integration/1','status':'PASS',
      'created_at_utc':datetime.now(timezone.utc).isoformat(),'checks':checks,'check_count':len(checks),
      'parameter_rows':rows,'input_N':n,'Galerkin_K':k,'diagnostic_larger_K':large,'reference_dimension':ref,
      'large_design_cutoff_used_in_this_gate':False,'floating_tolerance':tol,
      'scope':'exact scalar source identities and finite floating controls, not universal analytic or empirical proof',
      'new_hardware_data':False,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':'PASS','checks':len(checks),'rows':len(rows)}))


if __name__=='__main__':main()
