#!/usr/bin/env python3
"""Independently diagnose a root interval-predictor artifact.

The root's stored integer vectors are compared with the exact infinite-force
displacement formulas at high precision. This checks signs, spin/reference
columns, chronological phase placement, and normalization. It is NOT a proof
of the root's outward-integer numerical enclosure and does not replace it.
"""
from __future__ import annotations
import argparse
from datetime import datetime,timezone
from fractions import Fraction as F
import hashlib,json,os,platform,sys
from pathlib import Path
import mpmath as mp

from check_simultaneous_galerkin import displacement_element


def rational_mp(value):
    q=F(value);return mp.mpf(q.numerator)/q.denominator


def exact_amplitude(word,spin,n,ref,x):
    """The declared (g1,R0 + e0,R1)/sqrt(2) input and phi=pi/3."""
    initial_spin,initial_n=('g',1) if ref==0 else ('e',0)
    phi=mp.pi/3
    if word=='00':
        return (mp.exp(-2j*phi) if spin=='e' else 1)/mp.sqrt(2) if (spin,n)==(initial_spin,initial_n) else mp.mpc(0)
    exposure=2*x if word=='11' else x
    minus=displacement_element(n,initial_n,exposure,-1)
    plus=displacement_element(n,initial_n,exposure,1)
    amp=(minus+plus)/2 if spin==initial_spin else (minus-plus)/2
    if word=='01' and initial_spin=='e':amp*=mp.exp(-1j*phi)
    if word=='10' and spin=='e':amp*=mp.exp(-1j*phi)
    return amp/mp.sqrt(2)


def n1_galerkin_bound(k,exposure):
    if not exposure:return mp.mpf(0)
    # N=1, L=(K-1)/2, c_j = (sqrt(2)*exposure)^j/sqrt(j!).
    j=(k-1)//2+1
    return min(mp.mpf(1),2*mp.exp(j*mp.log(mp.sqrt(2)*abs(exposure))-mp.loggamma(j+1)/2))


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--artifact',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--calibration',type=Path)
    a=p.parse_args();r=json.loads(a.artifact.read_text());mp.mp.dps=240
    checks=[]
    def check(name,ok,detail=None):
        if not bool(ok):raise AssertionError((name,detail))
        checks.append({'name':name,'status':'PASS','detail':detail})
    check('artifact is the declared specified-input finite prediction',
          r['status']=='PASS' and r['initial_G_support']==1 and r['reference_dimension']==2
          and r['input_state']=='(|g,1>|0_R>+|e,0>|1_R>)/sqrt(2)')
    k=r['Galerkin_K'];x=rational_mp(r['nominal_x'])
    check('actual large carrier identity',k==4175 and r['system_dimension']==2*k+1)
    check('all zero mass failure records retained',set(r['zero_mass_records'])=={'f','0f','1f','prep_fail'})
    if a.calibration:
        cal=json.loads(a.calibration.read_text())
        check('predictor uses data-chosen nominal area',F(r['nominal_x'])==F(cal['certificate']['xhat']))
        check('calibration identity matches artifact',hashlib.sha256(a.calibration.read_bytes()).hexdigest()==r['calibration_identity']['sha256'])
    expectedQ={'00':F(313,1250),'01':F(312,1250),'10':F(312,1250),'11':F(313,1250)}
    check('exact four positive record blocks',set(v['word'] for v in r['records'])==set(expectedQ))
    rows=[];weighted=mp.mpf(0);weighted_galerkin=mp.mpf(0);worst_coordinate=mp.mpf(0)
    for record in r['records']:
        word=record['word'];q=F(record['Q']);seen=set();sum_integer_squared=0
        data=[]
        for spin,n,ref,real,imag in record['amplitudes']:
            coord=(spin,n,ref)
            check('legal unique coordinate '+word+' '+str(coord),
                  coord not in seen and spin in ('g','e') and n>=0 and n+(spin=='e')<=k and ref in (0,1))
            seen.add(coord);u,v=int(real),int(imag);sum_integer_squared+=u*u+v*v
            data.append((coord,u,v))
        check('integer vector normalization denominator '+word,
              sum_integer_squared==int(record['sum_abs_integer_squared']) and sum_integer_squared>0)
        check('record weight is the deployed Q '+word,q==expectedQ[word])
        denominator=mp.sqrt(sum_integer_squared);overlap=mp.mpc(0);coordinate_error=mp.mpf(0)
        for (spin,n,ref),u,v in data:
            stored=mp.mpc(u,v)/denominator
            true=exact_amplitude(word,spin,n,ref,x)
            coordinate_error=max(coordinate_error,abs(stored-true))
            overlap+=mp.conj(stored)*true
        rad=1-abs(overlap)**2
        if rad<0 and abs(rad)<mp.mpf('1e-215'):rad=mp.mpf(0)
        check('infinite analytic overlap has legal modulus '+word,rad>=0)
        distance=mp.sqrt(rad);gal=n1_galerkin_bound(k,word.count('1')*abs(x))
        root_numerical=rational_mp(record['normalized_state_trace_distance_upper'])
        check('high precision overlap consistent with independent numerical plus truncation budgets '+word,
              distance<=root_numerical+gal+mp.mpf('1e-100'))
        # This loose diagnostic threshold targets sign/order/column bugs. The
        # root's much sharper interval guarantee is NOT proved by this check.
        check('no amplitude-scale or phase-order discrepancy '+word,coordinate_error<mp.mpf('1e-60'))
        weighted+=rational_mp(q)*distance;weighted_galerkin+=rational_mp(q)*gal
        worst_coordinate=max(worst_coordinate,coordinate_error)
        rows.append({'word':word,'coordinates_checked':len(data),
                     'maximum_coordinate_discrepancy':mp.nstr(coordinate_error,45),
                     'joint_pure_state_distance_from_infinite_overlap':mp.nstr(distance,45),
                     'paper_N1_to_K_Galerkin_upper_diagnostic':mp.nstr(gal,12),
                     'root_numerical_interval_bound_consumed':record['normalized_state_trace_distance_upper']})
    check('complete CQ discrepancy within root numerical plus true Galerkin bounds',
          weighted<=rational_mp(r['complete_CQ_numerical_error_upper'])+weighted_galerkin+mp.mpf('1e-100'))
    report={'schema':'ueot-qm.independent-interval-output-diagnostic/1','status':'PASS',
            'created_at_utc':datetime.now(timezone.utc).isoformat(),
            'checker_author':'native research subagent B',
            'execution_context':{'provider':'github_actions' if os.environ.get('GITHUB_ACTIONS')=='true' else 'local_python_process',
                                 'python':sys.version,'platform':platform.platform(),
                                 'github':{name:os.environ.get(name) for name in ['GITHUB_RUN_ID','GITHUB_RUN_ATTEMPT','GITHUB_SHA','GITHUB_REF','GITHUB_WORKFLOW','GITHUB_ACTOR']} if os.environ.get('GITHUB_ACTIONS')=='true' else None,
                                 'attribution':'Actual invoker/checkout supplied by enclosing runner; checker author is not an executor label.'},
            'artifact':{'path':str(a.artifact),'sha256':hashlib.sha256(a.artifact.read_bytes()).hexdigest()},
            'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'displacement_helper_sha256':hashlib.sha256(Path(__file__).with_name('check_simultaneous_galerkin.py').read_bytes()).hexdigest(),
            'mp_decimal_precision':mp.mp.dps,'check_count':len(checks),'checks':checks,'words':rows,
            'maximum_coordinate_discrepancy':mp.nstr(worst_coordinate,45),
            'complete_CQ_distance_high_precision_diagnostic':mp.nstr(weighted,45),
            'scope':'Independent analytic-displacement diagnostic of signs, phase chronology, reference columns, normalization and output values. Not an independent proof of outward-integer rounding or the root numerical enclosure.',
            'numerical_interval_certificate_replaced':False,'new_hardware_data':False}
    a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':'PASS','checks':len(checks),'complete_CQ_diagnostic':mp.nstr(weighted,18),
                      'maximum_coordinate_discrepancy':mp.nstr(worst_coordinate,18),'output':str(a.output)}))


if __name__=='__main__':main()
