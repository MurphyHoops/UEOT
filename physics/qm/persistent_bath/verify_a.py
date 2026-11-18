"""Reproduce A's finite arithmetic, operations, and diagnostic witnesses.

The exact assertions certify the displayed finite algebra only.  The analytic
all-input bounds are proved in A_THEOREMS.md; floating checks are not interval
certificates or device data.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import platform
import time
import numpy as np
import scipy
from scipy.linalg import expm
import sympy as sp

from finite_operations import (FiniteTest, adjoint, frame, identity_test,
    labelled_choi_distance, probabilities, reconstruct_blocks, trace_norm,
    weighted_diamond_bound)

ROOT = Path(__file__).resolve().parent


def exact_frames():
    ans = []
    for d in (2, 3, 4):
        vectors = [sp.eye(d)[:, j] for j in range(d)]
        rho = [v * v.conjugate().T for v in vectors]
        dual = [x.copy() for x in rho]
        for j in range(d):
            for k in range(j+1, d):
                x = vectors[j]*vectors[k].T + vectors[k]*vectors[j].T
                y = -sp.I*vectors[j]*vectors[k].T + sp.I*vectors[k]*vectors[j].T
                rho.extend([(rho[j]+rho[k]+x)/2, (rho[j]+rho[k]+y)/2])
                dual.extend([x, y])
                dual[j] -= (x+y)/2
                dual[k] -= (x+y)/2
        gram = sp.Matrix([[sp.simplify((a*b).trace()) for b in dual] for a in rho])
        assert gram == sp.eye(d*d)
        assert all(p*p == p and p.trace() == 1 and p == p.conjugate().T for p in rho)
        x = sp.Symbol('x')
        s = sp.sqrt(2*d-1)
        for j in range(d):
            assert sp.expand(dual[j].charpoly(x).as_expr()
                             - x**(d-2)*(x*x-x-sp.Rational(d-1, 2))) == 0
        A = d*(1+s)/2 + d*(d-1)
        B = d*s + 2*d*(d-1)
        ans.append({'dimension':d, 'frame_count':d*d,
                    'exact_duality':True, 'rank_one_effects':True,
                    'sum_dual_operator_norm_exact':str(A),
                    'sum_dual_trace_norm_exact':str(B),
                    'coarse_half_diamond_constant_exact':str(sp.simplify(A*B/2)),
                    'coarse_half_diamond_constant_float':float(A*B/2)})
    return ans


def random_test(d, rng):
    raw = rng.normal(size=(2*d,d)) + 1j*rng.normal(size=(2*d,d))
    q, _ = np.linalg.qr(raw)
    return FiniteTest(d, d, {'f':(q[:d],), 'p':(q[d:],)})


def operation_checks():
    rng = np.random.default_rng(20261114)
    ans = []
    for d in (2,3,4):
        _, rho, dual = frame(d)
        test = random_test(d,rng)
        other = random_test(d,rng)
        test.validate(); other.validate()
        labels, p = probabilities(test,rho,rho)
        _, p2 = probabilities(other,rho,rho)
        # A reference as large as the input; generic correlated pure state.
        v = rng.normal(size=d*d) + 1j*rng.normal(size=d*d)
        v /= np.linalg.norm(v)
        joint = np.outer(v,v.conj())
        original = test.blocks(joint,d)
        recovered = reconstruct_blocks(p,dual,dual,joint,d)
        residual = max(trace_norm(original[y]-z) for y,z in zip(labels,recovered))
        assert residual < 5e-13
        second = other.blocks(joint,d)
        actual = sum(trace_norm(original[y]-second[y]) for y in labels)
        upper = weighted_diamond_bound(p-p2,dual,dual)
        assert actual <= upper + 1e-12
        conditional = test.then({'f':identity_test(d), 'p':other})
        parallel = test.parallel(other)
        coarse = test.coarse_grain({'f':'all','p':'all'})
        discarded = test.discard()
        binary = test.with_binary_effect(rho[-1])
        residuals = {name:t.validate() for name,t in [
            ('conditional',conditional),('parallel',parallel),
            ('coarse',coarse),('discard',discarded),('binary',binary)]}
        # Same labelled CP maps with a nontrivial change of Kraus representation.
        equivalent = FiniteTest(d,d,{y:tuple(z for k in ks for z in
                              (k/np.sqrt(2),1j*k/np.sqrt(2)))
                              for y,ks in test.branches.items()})
        eq_checks = {
            'base':labelled_choi_distance(test,equivalent),
            'conditional':labelled_choi_distance(
                conditional,equivalent.then({'f':identity_test(d),'p':other})),
            'parallel':labelled_choi_distance(parallel,equivalent.parallel(other)),
            'coarse':labelled_choi_distance(coarse,equivalent.coarse_grain({'f':'all','p':'all'})),
            'discard':labelled_choi_distance(discarded,equivalent.discard())}
        assert max(eq_checks.values()) < 1e-12
        ans.append({'dimension':d, 'reference_dimension':d,
                    'reconstruction_trace_norm_residual':residual,
                    'executed_joint_output_trace_norm_difference':actual,
                    'all_input_analytic_bound_evaluated':upper,
                    'completeness_residuals':residuals,
                    'labelled_quotient_residuals':eq_checks})
    return ans


def replacement_test(q, accepted):
    e = np.eye(2, dtype=complex)
    return FiniteTest(2,2,{
        'accept':tuple(np.sqrt(q)*np.outer(e[accepted],e[j]) for j in range(2)),
        'fail':tuple(np.sqrt(1-q)*np.outer(e[0],e[j]) for j in range(2))})


def negative_controls():
    I=np.eye(2,dtype=complex); X=np.array([[0,1],[1,0]],complex)
    Y=np.array([[0,-1j],[1j,0]],complex); Z=np.diag([1.,-1.]).astype(complex)
    H=(X+Z)/np.sqrt(2)
    plus=np.array([1,1],complex)/np.sqrt(2); pplus=np.outer(plus,plus.conj())
    ident=identity_test(2); ztest=FiniteTest(2,2,{'id':(Z,)})
    computational=[np.diag([1.,0.]),np.diag([0.,1.])]
    _, p=probabilities(ident,computational,computational)
    _, q=probabilities(ztest,computational,computational)
    assert np.max(np.abs(p-q)) == 0
    blind_distance=trace_norm(pplus-Z@pplus@Z)/2
    assert abs(blind_distance-1)<1e-14

    _,rhos,_=frame(2)
    xtest=FiniteTest(2,2,{'id':(X,)})
    _,a=probabilities(ztest,rhos,rhos)
    rotated=np.array([H@r@H for r in rhos])
    _,b=probabilities(xtest,rotated,rotated)
    assert np.max(np.abs(a-b))<1e-14
    bell=np.array([1,0,0,1],complex)/np.sqrt(2); bell=np.outer(bell,bell.conj())
    gauge_distance=trace_norm(ztest.blocks(bell,2)['id']-xtest.blocks(bell,2)['id'])/2
    assert abs(gauge_distance-1)<1e-14

    qsmall=1e-6
    r0=replacement_test(qsmall,0); r1=replacement_test(qsmall,1)
    b0=r0.blocks(pplus); b1=r1.blocks(pplus)
    full=sum(trace_norm(b0[y]-b1[y]) for y in b0)/2
    conditional=trace_norm(b0['accept']/qsmall-b1['accept']/qsmall)/2
    assert abs(full-qsmall)<1e-15 and abs(conditional-1)<1e-14

    ill=[]
    for eps in (1.,.1,.01,.001):
        small=np.array([1,1j*eps])/np.sqrt(1+eps*eps)
        rs=np.array([rhos[0],rhos[1],rhos[2],np.outer(small,small.conj())])
        basis=[I/np.sqrt(2),X/np.sqrt(2),Y/np.sqrt(2),Z/np.sqrt(2)]
        mat=np.array([[np.trace(r@b).real for b in basis] for r in rs])
        singular=np.linalg.svd(mat,compute_uv=False)
        ill.append({'epsilon':eps,'smallest_singular_value':float(singular[-1]),
                    'condition_number':float(singular[0]/singular[-1])})
    assert ill[-1]['condition_number']>1000

    leak=1e-4
    k=np.array([[np.sqrt(1-leak),0],[0,1],[np.sqrt(leak),0]],complex)
    j=np.array([[1,0],[0,1],[0,0]],complex)
    actual=k@computational[0]@adjoint(k); target=j@computational[0]@adjoint(j)
    leak_distance=trace_norm(actual-target)/2
    assert abs(leak_distance-np.sqrt(leak))<1e-12

    # The retained classical environment bit chooses I or Z once for both slots.
    dephased=(pplus+Z@pplus@Z)/2
    persistent_two=pplus
    reset_two=(dephased+Z@dephased@Z)/2
    reset_distance=trace_norm(persistent_two-reset_two)/2
    assert abs(reset_distance-.5)<1e-14

    # Real-local-tomography witness, checked in an exact real spanning frame.
    si=sp.eye(2); sy=sp.Matrix([[0,-sp.I],[sp.I,0]])
    yy=sp.kronecker_product(sy,sy)
    rp=(sp.eye(4)+yy)/4; rm=(sp.eye(4)-yy)/4
    real_effects=[sp.diag(1,0),sp.diag(0,1),sp.ones(2)/2]
    assert all((sp.kronecker_product(e,f)*(rp-rm)).trace()==0
               for e in real_effects for f in real_effects)
    joint_effect=(sp.eye(4)+yy)/2
    assert (joint_effect*rp).trace()==1 and (joint_effect*rm).trace()==0

    # An unreachable central sector leaves every visible branch unchanged.
    embedded={}
    for label,ks in ztest.branches.items():
        vv=[]
        for kk in ks:
            mat=np.zeros((3,3),complex); mat[:2,:2]=kk; vv.append(mat)
        h=np.zeros((3,3),complex); h[2,2]=1; vv.append(h)
        embedded[label]=tuple(vv)
    extended=FiniteTest(3,3,embedded); extended.validate()
    visible=np.zeros((3,3),complex); visible[:2,:2]=pplus
    ext=extended.then({'id':extended}).blocks(visible)[('id','id')]
    ordinary=ztest.then({'id':ztest}).blocks(pplus)[('id','id')]
    hidden_res=float(np.linalg.norm(ext[:2,:2]-ordinary))
    assert hidden_res<1e-14 and abs(ext[2,2])<1e-14
    return {
        'incomplete_test_max_probability_gap':0,
        'incomplete_test_untested_trace_distance':blind_distance,
        'spam_gauge_max_probability_gap':float(np.max(np.abs(a-b))),
        'spam_gauge_same_coordinate_trace_distance':gauge_distance,
        'rare_acceptance_probability':qsmall,
        'rare_acceptance_full_trace_distance':full,
        'rare_acceptance_conditional_trace_distance':conditional,
        'ill_conditioned_frames':ill,
        'leakage_probability':leak,'coherent_leakage_trace_distance':leak_distance,
        'same_single_slot_different_two_slot_trace_distance':reset_distance,
        'real_joint_states_local_tests_equal_exact':True,
        'real_joint_effect_probabilities_exact':[1,0],
        'hidden_superselection_visible_composition_residual':hidden_res,
        'all_negative_controls_detected':True}


def causal_break_memory():
    omega=np.array([1.,1.5]); c=np.array([1.,.6]); t=2/3; tau=3/4
    ans=[]
    for lam in (.2,.3,.4):
        kap=lam*c/omega
        vis=float(np.exp(-4*np.sum(kap**2*(1-np.cos(omega*tau)))))
        theta=float(4*np.sum(kap**2*(np.sin(omega*t)+np.sin(omega*tau)
                                         -np.sin(omega*(t+tau)))))
        response=vis*np.sin(theta)
        matrix=np.array([[(1-response)/2,(1+response)/2],
                         [(1+response)/2,(1-response)/2]])
        assert np.linalg.matrix_rank(matrix)==2
        finite=[]
        for sign in (1,-1):
            coherence=1.+0j
            for w,cc in zip(omega,c):
                K=14
                aa=np.diag(np.sqrt(np.arange(1,K+1)),1)
                nn=np.diag(np.arange(K+1))
                source=expm(-1j*t*(w*nn+sign*lam*cc*(aa+aa.T)))[:,0]
                up=expm(-1j*tau*(w*nn+lam*cc*(aa+aa.T)))
                um=expm(-1j*tau*(w*nn-lam*cc*(aa+aa.T)))
                coherence*=np.vdot(um@source,up@source)
            finite.append(coherence)
        expected=np.array([vis*np.exp(1j*theta),vis*np.exp(-1j*theta)])
        residual=float(np.max(np.abs(np.array(finite)-expected)))
        assert residual<5e-13
        ans.append({'lambda':lam,'visibility':vis,'phase':theta,
                    'response_matrix':matrix.tolist(),
                    'smallest_singular_value':float(np.linalg.svd(matrix,compute_uv=False)[-1]),
                    'rank':2,'finite_K14_coherence_residual':residual,
                    'memory_dimension_lower_bound':2})
    return {'protocol':'separately declared causal-break diagnostic; not the frozen f/p tree',
            'reference':'not used; independent fixed preparations; no variable reference crosses cut; future controls do not read the history label',
            'analytic_domain':'lambda in [1/5,2/5]',
            'analytic_rank_proof':'0<theta<12*(2/5)^2*(1+(2/5)^2)<pi; visibility>0',
            'rows':ans}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--contract',type=Path,required=True)
    parser.add_argument('--output',type=Path,default=ROOT/'A_VERIFICATION.json')
    args=parser.parse_args()
    start=time.perf_counter()
    result={'schema':'ueot-physics-a-operations-verification/1',
            'time_utc':datetime.now(timezone.utc).isoformat(),
            'contract_sha256':hashlib.sha256(args.contract.read_bytes()).hexdigest(),
            'scope':'Exact finite algebra plus floating verification; no new Lean run or device data',
            'versions':{'python':platform.python_version(),'numpy':np.__version__,
                        'scipy':scipy.__version__,'sympy':sp.__version__},
            'exact_frames':exact_frames(),
            'operations':operation_checks(),
            'negative_controls':negative_controls(),
            'memory_witness':causal_break_memory()}
    result['runtime_seconds']=time.perf_counter()-start
    result['source_sha256']={p.name:hashlib.sha256(p.read_bytes()).hexdigest()
                            for p in (ROOT/'finite_operations.py',ROOT/'verify_a.py')}
    result['status']='PASS_DECLARED_FINITE_SCOPE'
    path=args.output
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'runtime_seconds':result['runtime_seconds'],
                      'output':str(path),'frame_constants':result['exact_frames'],
                      'memory_witness':result['memory_witness']},indent=2))


if __name__=='__main__':
    main()
