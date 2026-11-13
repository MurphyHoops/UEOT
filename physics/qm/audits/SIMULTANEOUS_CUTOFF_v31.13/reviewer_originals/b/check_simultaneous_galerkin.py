#!/usr/bin/env python3
"""Independent dynamics diagnostics and rational finite-Duhamel enclosure.

No project runtime, certificate producer, or C checker is imported. Exact
infinite-force matrix elements are evaluated using the displacement formula;
a larger finite matrix is only a labelled diagnostic for the general Rabi case.
The universal operator bounds are paper proofs, not inferred from these tests.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
from fractions import Fraction as F
import hashlib
import json
import os
import platform
import sys
from math import factorial, isqrt, comb
from pathlib import Path

import mpmath as mp
import numpy as np
from scipy.linalg import expm


def basis(k):
    return [("g", 0)] + [z for m in range(1, k+1)
                          for z in [("g", m), ("e", m-1)]]


def mp_generator(k, omega=0, delta=0, g=1, h=1):
    states=basis(k); index={v:i for i,v in enumerate(states)}
    a=mp.zeros(len(states));b=mp.zeros(len(states));diag=mp.zeros(len(states))
    for j,(spin,n) in enumerate(states):
        diag[j,j]=mp.mpf(omega)*n+mp.mpf(delta)*(spin=="e")
        if spin=="g":
            r=("e",n-1);blue=("e",n+1)
            if r in index:a[index[r],j]=mp.sqrt(n)
            if blue in index:b[index[blue],j]=mp.sqrt(n+1)
        else:
            r=("g",n+1);blue=("g",n-1)
            if r in index:a[index[r],j]=mp.sqrt(n+1)
            if blue in index:b[index[blue],j]=mp.sqrt(n)
    return diag+mp.mpf(g)*a+mp.mpf(h)*b


def phase(k,phi):
    return mp.diag([mp.exp(-1j*phi) if spin=="e" else 1 for spin,n in basis(k)])


def embedding(n,k):
    ans=mp.zeros(2*k+1,2*n+1)
    for i in range(2*n+1):ans[i,i]=1
    return ans


def kron(a,b):
    out=mp.zeros(a.rows*b.rows,a.cols*b.cols)
    for i in range(a.rows):
        for j in range(a.cols):
            for k in range(b.rows):
                for l in range(b.cols):out[i*b.rows+k,j*b.cols+l]=a[i,j]*b[k,l]
    return out


def laguerre(n,d,x):
    return sum(mp.mpf((-1)**j*comb(n+d,n-j))*x**j/factorial(j)
               for j in range(n+1))


def displacement_element(m,n,x,sign):
    """<m|D(sign*i*x)|n>; pure-imaginary displacements are symmetric."""
    low,high=min(m,n),max(m,n)
    z=sign*1j*x
    return (mp.exp(-x*x/2)*mp.sqrt(mp.mpf(factorial(low))/factorial(high))
            *z**(high-low)*laguerre(low,high-low,x*x))


def exact_force_columns(n,k,x):
    """P_K exp[-ix sigma_x(a+a†)] P_N from exact displacement entries."""
    ans=mp.zeros(2*k+1,2*n+1)
    for i,(so,m) in enumerate(basis(k)):
        for j,(si,nn) in enumerate(basis(n)):
            minus=displacement_element(m,nn,x,-1)
            plus=displacement_element(m,nn,x,1)
            ans[i,j]=(minus+plus)/2 if so==si else (minus-plus)/2
    return ans


def vector_norm(v):
    return mp.sqrt(mp.re((v.H*v)[0]))


def trace_distance_from_exact_overlap(approx,projected_exact):
    # Exact full state and finite predictor are normalized by the source theorem
    # and the finite unitary. Their overlap needs only these finite exact columns.
    overlap=(approx.H*projected_exact)[0]
    rad=1-abs(overlap)**2
    if rad<0 and abs(rad)<mp.mpf("1e-55"):rad=mp.mpf(0)
    if rad<0:raise AssertionError("normalization inconsistent with exact overlap")
    return mp.sqrt(rad),overlap


def scalar_error(n,l,x):
    j=l+1
    return min(mp.mpf(1),2*x**j/mp.factorial(j)*
               mp.sqrt(mp.fprod(n+2*k-1 for k in range(1,j+1))))


def sqrt_fraction_interval(x,places=40):
    scale=10**places
    r=isqrt(x.numerator*scale*scale//x.denominator)
    lo=F(r,scale);hi=lo if lo*lo==x else F(r+1,scale)
    assert lo*lo<=x<=hi*hi
    return lo,hi


def bound_interval(n,l,x):
    j=l+1;prod=1
    for k in range(1,j+1):prod*=n+2*k-1
    squared=4*x**(2*j)*prod/F(factorial(j)**2)
    lo,hi=sqrt_fraction_interval(squared)
    return min(F(1),lo),min(F(1),hi)


def encode(v):
    if isinstance(v,F):return str(v)
    if isinstance(v,(mp.mpf,mp.mpc)):return mp.nstr(v,45)
    if isinstance(v,dict):return {k:encode(x) for k,x in v.items()}
    if isinstance(v,(list,tuple)):return [encode(x) for x in v]
    if isinstance(v,(np.floating,np.integer)):return v.item()
    return v


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--model',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    args=p.parse_args();model=json.loads(args.model.read_text())
    mp.mp.dps=70
    checks=[]

    def check(name,ok,detail=None):
        if not bool(ok):raise AssertionError((name,encode(detail)))
        checks.append({'name':name,'status':'PASS','detail':encode(detail)})

    check('frozen primary cutoffs and exposure',
          (model['input_filter_N'],model['galerkin_extra_L'],model['galerkin_K'],
           F(model['design_x_abs_max']))==(4095,40,4175,F(1,10)))
    n,l,k=1,3,7
    check('small witness cutoff matches separately declared example',
          model['numerical_small_instance']=={'input_N':n,'galerkin_L':l,'reference_dimension':2})
    phi=mp.pi/3;ref=mp.eye(2);j=embedding(n,k)
    psi=mp.zeros((2*n+1)*2,1)
    psi[2]=psi[5]=1/mp.sqrt(2)
    gsmall=mp.diag([nn+(s=='e') for s,nn in basis(n)])
    check('untouched entangled reference input has mean G one',
          abs((psi.H*kron(gsmall,ref)*psi)[0]-1)<mp.mpf('1e-60'))
    full_generator=mp_generator(k)
    pk=phase(k,phi);pn=phase(n,phi)
    Q={'00':mp.mpf(313)/1250,'01':mp.mpf(312)/1250,
       '10':mp.mpf(312)/1250,'11':mp.mpf(313)/1250}
    force_rows=[]
    for xt in ['-0.1','0.07','0.1']:
        x=mp.mpf(xt);u=mp.expm(-1j*x*full_generator)
        check('finite true-compression unitary at '+xt,
              mp.norm(u.H*u-mp.eye(u.rows))<mp.mpf('1e-60'))
        exact=exact_force_columns(n,k,x)
        exact2=exact_force_columns(n,k,2*x)
        finite_words={'00':pk*pk*j,'01':u*pk*j,'10':pk*u*j,'11':u*u*j}
        exact_words={'00':j*pn*pn,'01':exact*pn,'10':pk*exact,'11':exact2}
        weighted=mp.mpf(0);weighted_bound=mp.mpf(0)
        for word in ['00','01','10','11']:
            v=kron(finite_words[word],ref)*psi
            exact_projection=kron(exact_words[word],ref)*psi
            error,overlap=trace_distance_from_exact_overlap(v,exact_projection)
            tail=1-vector_norm(exact_projection)**2
            exposure=word.count('1')*abs(x)
            upper=scalar_error(n,l,exposure)
            check('true infinite displacement vs actual Galerkin '+xt+' '+word,
                  error<=upper+mp.mpf('1e-30'),
                  {'distance':error,'paper_bound':upper,'exact_output_tail':tail})
            check('tail is only a lower constraint on this pure-state error '+xt+' '+word,
                  error*error+mp.mpf('1e-55')>=tail)
            ek=kron(mp.diag([nn+(s=='e') for s,nn in basis(k)]),ref)
            energy=mp.re((v.H*ek*v)[0])
            energy_bound=(mp.sqrt(2)+exposure)**2-1
            check('derived finite energy budget '+xt+' '+word,
                  energy<=energy_bound+mp.mpf('1e-55'),
                  {'mean_G':energy,'upper':energy_bound})
            weighted+=Q[word]*error;weighted_bound+=Q[word]*upper
        check('complete Q weighted dynamics '+xt,weighted<=weighted_bound+mp.mpf('1e-30'))
        force_rows.append({'x':xt,'N':n,'L':l,'K':k,
                           'complete_Q_distance_from_exact_overlaps':weighted,
                           'analytic_Q_upper':weighted_bound,
                           'exact_oracle':'conditional displacement matrix elements; no large-matrix infinite surrogate'})

    # Concrete failure of the projection-versus-generator substitution.
    x=mp.mpf('0.4');kk=1
    e=mp.zeros(3,1);e[1]=1
    finite=mp.expm(-1j*x*mp_generator(kk))*e
    projected=exact_force_columns(kk,kk,x)*e
    normalized_projection=projected/vector_norm(projected)
    wrong_equivalence=mp.sqrt(max(mp.mpf(0),1-abs((finite.H*normalized_projection)[0])**2))
    check('negative: normalized evolved projection differs from Galerkin',
          wrong_equivalence>mp.mpf('0.01'),wrong_equivalence)

    # A perfect finite exponential can have substantial physical dynamics error.
    x=mp.mpf('0.3');finite0=mp.expm(-1j*x*mp_generator(0))
    actual_error=mp.sqrt(1-mp.exp(-x*x))
    check('negative: zero finite exponential residual does not certify truncation',
          finite0[0,0]==1 and actual_error>mp.mpf('.25'),actual_error)

    # Independent general-Rabi finite diagnostic. The larger carrier is NOT
    # claimed to be the infinite source: the paper gives both continuum bounds.
    general_rows=[];n=1;l=3;k=7;big=19;tb=0.2
    def arr(m):return np.array(m.tolist(),dtype=complex)
    for hh in [0.,0.1,-0.1,0.2]:
        hs=arr(mp_generator(k,1,mp.mpf('0.6'),mp.mpf('0.4'),hh))
        hb=arr(mp_generator(big,1,mp.mpf('0.6'),mp.mpf('0.4'),hh))
        es=np.eye(2*k+1,2*n+1,dtype=complex)
        eb=np.eye(2*big+1,2*n+1,dtype=complex)
        embed=np.eye(2*big+1,2*k+1,dtype=complex)
        ps=np.array(psi.tolist(),dtype=complex).reshape(-1)
        vs=np.kron(expm(-1j*tb*hs)@es,np.eye(2))@ps
        vb=np.kron(expm(-1j*tb*hb)@eb,np.eye(2))@ps
        vse=np.kron(embed,np.eye(2))@vs
        observed=float(np.linalg.norm(vb-vse))
        bs=float(scalar_error(n,l,mp.mpf(str(abs(hh)*tb))))
        bb=float(scalar_error(n,(big-n)//2,mp.mpf(str(abs(hh)*tb))))
        check('general Rabi nested finite diagnostic h='+str(hh),
              observed<=bs+bb+1e-12,
              {'vector_difference':observed,'small_continuum_bound':bs,'large_continuum_bound':bb,
               'larger_matrix_is_infinite_oracle':False})
        residual=hb@embed-embed@hs
        w=np.zeros((2*k+1,2*k+1),complex);idx={s:i for i,s in enumerate(basis(k))}
        w[idx[('g',k)],idx[('g',k)]]=k+1
        w[idx[('g',k-1)],idx[('g',k-1)]]=k
        defect=float(np.linalg.norm(residual.conj().T@residual-hh*hh*w))
        check('source-derived two-edge residual h='+str(hh),defect<1e-12,defect)
        if hh==0:check('positive: zero-blue source is exactly cutoff-preserving',observed<1e-12)
        general_rows.append({'h':hh,'omega':1,'Delta':'3/5','g':'2/5','duration':'1/5',
                             'N':n,'K':k,'comparison_K':big,'vector_difference':observed,
                             'finite_diagnostic_only':True})

    # Genuine integer/rational bound enclosure for the frozen large-domain
    # analytic theorem; this does not run an 8351-dimensional exponential.
    nn=model['input_filter_N'];ll=model['galerkin_extra_L']
    xmax=F(model['design_x_abs_max'])
    d1=bound_interval(nn,ll,xmax);d2=bound_interval(nn,ll,2*xmax)
    a,b=F(312,625),F(313,1250)
    qbound=(a*d1[0]+b*d2[0],a*d1[1]+b*d2[1])
    check('rational full-design Galerkin bound below one ten-thousandth',
          qbound[1]<F(1,10000),{'one_drive':d1,'two_drive':d2,'complete_Q':qbound})
    report={'schema':'ueot-qm.independent-simultaneous-dynamics/1',
            'status':'PASS','executed_at_utc':datetime.now(timezone.utc).isoformat(),
            'checker_author':'native research subagent B',
            'execution_context':{'provider':'github_actions' if os.environ.get('GITHUB_ACTIONS')=='true' else 'local_python_process',
                                 'python':sys.version,'platform':platform.platform(),
                                 'github':{key:os.environ.get(key) for key in ['GITHUB_RUN_ID','GITHUB_RUN_ATTEMPT','GITHUB_SHA','GITHUB_REF','GITHUB_WORKFLOW','GITHUB_ACTOR']} if os.environ.get('GITHUB_ACTIONS')=='true' else None,
                                 'attribution':'Checker author is not an executor label; the enclosing runner identifies its invoker and checkout.'},
            'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'frozen_model_sha256':hashlib.sha256(args.model.read_bytes()).hexdigest(),
            'imports_project_runtime':False,'mp_decimal_precision':mp.mp.dps,
            'check_count':len(checks),'checks':checks,
            'exact_force_diagnostics':force_rows,'general_rabi_finite_diagnostics':general_rows,
            'analytic_large_domain':{'N':nn,'L':ll,'K':nn+2*ll,'input_dimension':2*nn+1,
                                     'predictor_dimension':2*(nn+2*ll)+1,
                                     'large_matrix_executed':False,'rational_Q_bound':qbound},
            'evidence_classes':['paper universal operator proof consumed',
                                'exact rational enclosure of scalar bound',
                                'finite high-precision displacement-overlap diagnostics',
                                'finite floating general-Rabi comparison'],
            'new_lean_execution':False,'new_hardware_data':False,
            'limits':'High precision and finite residuals alone are not interval certification of numerical output; the analytic global bound has its independent rational enclosure.'}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(encode(report),indent=2)+'\n')
    print(json.dumps({'status':'PASS','checks':len(checks),'output':str(args.output),
                      'full_design_Galerkin_upper':float(qbound[1]),'new_hardware_data':False}))


if __name__=='__main__':main()
