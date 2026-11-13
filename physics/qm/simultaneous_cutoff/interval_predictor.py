#!/usr/bin/env python3
"""Outward-integer Taylor prediction for one entangled input on the large carrier.

Every interval endpoint is an integer divided by SCALE. Square roots use isqrt;
all multiplication and division round outwards. No scipy value is used in the
certificate. The returned exact normalized integer vectors are valid pure
states; their Q mixture is a valid complete CQ prediction. The global Taylor
remainder applies to exp(-i P_K H P_K), not a projected infinite exponential.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
import math
import os
from pathlib import Path

SCALE=10**80
DEGREE=100
ZERO=(0,0,0,0)
Q={"00":Fraction(313,1250),"01":Fraction(312,1250),
   "10":Fraction(312,1250),"11":Fraction(313,1250)}


def ceildiv(a,b):return -((-a)//b)
def sqrt_interval(n):
    a=math.isqrt(n*SCALE*SCALE)
    return a,a if a*a==n*SCALE*SCALE else a+1
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def product(a,b):
    p=[a[0]*b[0],a[0]*b[1],a[1]*b[0],a[1]*b[1]]
    return min(p)//SCALE,ceildiv(max(p),SCALE)
def times_real(z,a):return product(z[:2],a)+product(z[2:],a)
def times_rational(z,a):
    a=Fraction(a)
    vals=[]
    for lo,hi in (z[:2],z[2:]):
        p,q=lo*a.numerator,hi*a.numerator
        vals.extend((min(p,q)//a.denominator,ceildiv(max(p,q),a.denominator)))
    return tuple(vals)
def minus_i(z):return z[2],z[3],-z[1],-z[0]
def phase(z):
    # (1-i sqrt(3))/2; both sqrt endpoints outward.
    sr=times_real(z,sqrt_interval(3))
    return times_rational(add(z,minus_i(sr)),Fraction(1,2))
def apply_phase(state):
    return {key:phase(z) if key[0]=='e' else z for key,z in state.items()}


def force_term(state,cutoff,x_over_j):
    output={}
    for (spin,n,ref),z in state.items():
        other='e' if spin=='g' else 'g'
        for nn,root in ((n-1,n),(n+1,n+1)):
            if nn<0 or nn+(other=='e')>cutoff or root==0:continue
            key=other,nn,ref
            term=minus_i(times_rational(times_real(z,sqrt_interval(root)),x_over_j))
            output[key]=add(output.get(key,ZERO),term)
    return output


def force_polynomial(state,cutoff,x):
    result=dict(state);term=dict(state)
    for j in range(1,DEGREE+1):
        term=force_term(term,cutoff,x/j)
        for key,z in term.items():result[key]=add(result.get(key,ZERO),z)
    return result


def norm_upper_squared_cutoff(k,x):
    # ||A_K||<=sqrt(K), ||B_K||<=sqrt(K+1).
    return 4*x*x*(k+1)


def state_summary(state,remainder,word):
    centres=[];radius2=0;norm2=0
    for key,z in sorted(state.items()):
        re=(z[0]+z[1])//2;im=(z[2]+z[3])//2
        rr=max(re-z[0],z[1]-re);ri=max(im-z[2],z[3]-im)
        radius2+=rr*rr+ri*ri;norm2+=re*re+im*im
        if re or im:centres.append([*key,str(re),str(im)])
    ir=math.isqrt(radius2)
    if ir*ir<radius2:ir+=1
    radius=Fraction(ir,SCALE)
    vector_error=(1+remainder)**word.count('1')-1+radius
    # Normalizing the interval centre adds at most its distance to a unit
    # vector. Pure-state trace distance <= vector distance <=2*vector_error.
    trace_error=min(Fraction(1),2*vector_error)
    if norm2==0:raise ValueError('zero predictor centre cannot be normalized')
    return {'word':word,'exact_normalization':'each integer amplitude divided by sqrt(sum_abs_integer_squared)',
      'sum_abs_integer_squared':str(norm2),'amplitudes':centres,
      'interval_radius_upper':str(radius),'unit_vector_error_upper':str(vector_error),
      'normalized_state_trace_distance_upper':str(trace_error),'stored_amplitudes':len(centres)},trace_error


def run(k,x):
    if k<1 or abs(x)>Fraction(1,10):raise ValueError('outside frozen interval predictor contract')
    # A deliberately uniform simple norm bound, checked exactly, covers the
    # whole design carrier K=4175 and every accepted calibrated nominal x.
    z=Fraction(13)
    if norm_upper_squared_cutoff(k,x)>z*z:raise ValueError('Taylor norm bound violated')
    n=DEGREE+1
    remainder=z**n/math.factorial(n)/(1-z/(n+1))
    root2=times_rational(sqrt_interval(2)+(0,0),Fraction(1,2))
    initial={('g',1,0):root2,('e',0,1):root2}
    rows=[];total=Fraction(0)
    for word,weight in Q.items():
        state=initial
        for letter in word:
            state=apply_phase(state) if letter=='0' else force_polynomial(state,k,x)
        row,error=state_summary(state,remainder,word)
        row['Q']=str(weight);rows.append(row);total+=weight*error
    if not total<Fraction(1,10**8):raise AssertionError('reserved numerical budget not achieved')
    return rows,total,remainder


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--calibration',type=Path)
    ap.add_argument('--x',default='3/50')
    args=ap.parse_args()
    x=Fraction(args.x)
    calibration_identity=None
    if args.calibration:
        raw=args.calibration.read_bytes();data=json.loads(raw)
        if data.get('status') not in {'PASS','CERTIFIED'}:raise ValueError('calibration not accepted')
        x=Fraction(data['nominal_x'])
        calibration_identity={'path':os.path.relpath(args.calibration.resolve(),args.output.resolve().parent),
                              'path_base':'prediction artifact parent',
                              'sha256':hashlib.sha256(raw).hexdigest()}
    k=4175
    rows,total,remainder=run(k,x)
    report={'schema':'ueot-qm.interval-complete-cq-prediction/1','status':'PASS',
       'created_at_utc':datetime.now(timezone.utc).isoformat(),'nominal_x':str(x),
       'Galerkin_K':k,'system_dimension':2*k+1,'reference_dimension':2,'initial_G_support':1,
       'input_state':'(|g,1>|0_R>+|e,0>|1_R>)/sqrt(2)',
       'physical_filter_4095_passes_this_input_with_probability_one':True,
       'arithmetic':'outward fixed-denominator integer intervals; isqrt-certified radicals',
       'scale':str(SCALE),'Taylor_degree':DEGREE,'uniform_operator_norm_upper':'13',
       'one_gate_Taylor_remainder_upper':str(remainder),
       'complete_CQ_numerical_error_upper':str(total),
       'complete_CQ_numerical_error_upper_decimal_diagnostic':float(total),
       'reserved_budget':'1/100000000','calibration_identity':calibration_identity,
       'records':rows,'zero_mass_records':['f','0f','1f','prep_fail'],
       'scope':'interval output certificate for this one specified entangled input; analytic uniform Galerkin theorem is separate',
       'large_design_carrier_executed_by_sparse_polynomial':True,
       'omitted_coordinates':'outside the propagated dictionary the polynomial is exactly zero; rounded-zero centres within it are covered by the interval radius; the infinite Taylor tail is separate',
       'not_an_independent_quantum_hardware_implementation':True,'new_hardware_data':False,
       'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':'PASS','K':k,'nominal_x':str(x),'numerical_error_bound':float(total),
                     'stored_amplitudes':[r['stored_amplitudes'] for r in rows]}))


if __name__=='__main__':main()
