#!/usr/bin/env python3
"""Exact rational complex controls for the finite-complex operational bridge.
These examples do not replace universal paper/Lean proofs or laboratory data.
"""
import hashlib
import json
from pathlib import Path
import sympy as s

I2=s.eye(2)
Z=s.diag(1,-1)
P0=s.diag(1,0)
P1=s.diag(0,1)
plus=s.Matrix([[1,1],[1,1]])/2


def apply(kraus, X):
    return sum((K*X*K.conjugate().T for K in kraus), s.zeros(kraus[0].rows) if kraus else s.zeros(X.rows))


def choi(kraus, din, dout):
    C=s.zeros(din*dout)
    for i in range(din):
        for j in range(din):
            E=s.zeros(din); E[i,j]=1
            block=apply(kraus,E)
            C[i*dout:(i+1)*dout,j*dout:(j+1)*dout]=block
    return C


def cq(instrument, X):
    return s.diag(*(apply(k,X) for k in instrument))


def trace_distance_hermitian(A,B):
    values=(A-B).eigenvals()
    return s.simplify(sum(s.Abs(l)*m for l,m in values.items())/2)


def main():
    rows=[]
    def add(name, condition, detail):
        if not condition:
            raise AssertionError(name)
        rows.append({'name':name,'verified':True,'detail':detail})

    old=[I2]; new=[s.Rational(3,5)*I2,s.Rational(4,5)*I2]
    add('same_cp_distinct_kraus',choi(old,2,2)==choi(new,2,2),
        'Kraus counts 1 and 2; exact 9/25+16/25=1; Choi matrices equal.')
    embedding=s.Matrix([[1,0],[0,1],[0,0]])
    e1=[embedding]; e2=[s.Rational(3,5)*embedding,s.Rational(4,5)*embedding]
    add('rectangular_same_cp',choi(e1,2,3)==choi(e2,2,3),
        'Actual qubit-to-qutrit maps, input-first 6x6 Choi, equal exactly.')
    bell=s.Matrix([1,0,0,1]); bell=bell*bell.conjugate().T/2
    amp1=[s.kronecker_product(K,I2) for K in e1]
    amp2=[s.kronecker_product(K,I2) for K in e2]
    add('entangled_reference_positive_control',apply(amp1,bell)==apply(amp2,bell),
        'Same rectangular CP map on an entangled 2x2 input; output dimension 6.')
    M=[[P0],[P1]]; swap=[[P1],[P0]]
    add('same_forgotten_channel',sum((choi(k,2,2) for k in M),s.zeros(4))==
        sum((choi(k,2,2) for k in swap),s.zeros(4)),
        'Outcome-forgetting channels coincide.')
    d=trace_distance_hermitian(cq(M,P0),cq(swap,P0))
    add('visible_label_swap_detected',d==1,'Complete CQ trace distance is exactly 1.')
    add('normalized_posterior_false_success',
        (P0/4)/(P0/4).trace()==(P0/2)/(P0/2).trace() and
        (P0/4).trace()!=(P0/2).trace(),
        'Posterior equal while raw event masses are 1/4 and 1/2.')
    hidden=cq([new],plus)
    visible=cq([[new[0]],[new[1]]],plus)
    add('hidden_index_is_not_visible_label',hidden.shape==(2,2) and visible.shape==(4,4),
        'Hidden refinement has one visible block; promoted refinement has two.')
    add('zero_event',apply([s.zeros(2)],plus)==s.zeros(2),
        'Zero Kraus event has zero probability; no normalized posterior created.')
    output0=apply([I2],plus); output1=apply([Z],plus)
    add('restricted_effect_false_success',
        s.trace(P0*output0)==s.trace(P0*output1) and
        s.trace(P1*output0)==s.trace(P1*output1) and output0!=output1,
        'All diagonal effects agree but full outputs are orthogonal.')
    add('restricted_input_false_success',apply([I2],P0)==apply([Z],P0)
        and choi([I2],2,2)!=choi([Z],2,2),
        'One supported input agrees; full-space Choi maps differ.')
    out={'classification':'exact symbolic rational controls, not empirical evidence',
        'sympy_version':s.__version__,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'checks':rows,'all_verified':all(r['verified'] for r in rows)}
    target=Path(__file__).with_name('operational_controls_receipt.json')
    target.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()
