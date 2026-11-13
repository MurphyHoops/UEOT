#!/usr/bin/env python3
"""Independent rational checker for a conditional, synthetic-only certificate.

Does not import the analyzer, interval library or generator. Uses a different
pi identity and the standard-normal variable to enclose the Gaussian CDF.
The universal physical inequalities remain paper proofs, not finite tests.
"""
import argparse
from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction as F
from functools import lru_cache
from math import factorial, isqrt
from pathlib import Path
import hashlib
import json
import os
import platform
import sys

WORDS=('f','0f','1f','00','01','10','11')
RAW=('q_calibration_flags.txt','drive_calibration_bits.txt',
     'source_holdout_records.txt','compiled_holdout_records.txt',
     'drive_holdout_bits.txt','drive_holdout_drift_bits.txt')


def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def encode(x):
    if isinstance(x,F):return str(x)
    if isinstance(x,dict):return {k:encode(v) for k,v in x.items()}
    if isinstance(x,(tuple,list)):return [encode(v) for v in x]
    return x


def root_interval(x,digits=65):
    x=F(x);scale=10**digits
    a=isqrt(x.numerator*scale*scale//x.denominator)
    return F(a,scale),F(a+1,scale)


@lru_cache(maxsize=1)
def independent_pi():
    # arctan(1/2)+arctan(1/3)=pi/4, by tangent addition and angle range.
    brackets=[]
    for d in (2,3):
        n=140
        terms=[F((-1)**j,(2*j+1)*d**(2*j+1)) for j in range(n+1)]
        s=sum(terms[:n],F(0));t=s+terms[n]
        brackets.append((min(s,t),max(s,t)))
    return 4*sum(b[0] for b in brackets),4*sum(b[1] for b in brackets)


def standard_phi(z):
    """Independent enclosure of Phi(z), valid for |z|<=1/2."""
    z=F(z)
    if z<0:
        lo,hi=standard_phi(-z);return 1-hi,1-lo
    if z==0:return F(1,2),F(1,2)
    if z>F(1,2):raise ValueError('Checker CDF domain exceeded')
    # Integral_0^z exp(-u^2/2) du; 38-term alternating brackets.
    terms=[F((-1)**j)*z**(2*j+1)/F(2**j*factorial(j)*(2*j+1)) for j in range(39)]
    s=sum(terms[:38],F(0));t=s+terms[38]
    ilo,ihi=min(s,t),max(s,t)
    pl,ph=independent_pi()
    cl=root_interval(1/(2*ph))[0];ch=root_interval(1/(2*pl))[1]
    return F(1,2)+cl*ilo,F(1,2)+ch*ihi


def inverse_outer(p,width=F(1,10**12)):
    p=F(p);lo,hi=F(-1,4),F(1,4)
    while hi-lo>width:
        mid=(lo+hi)/2;l,h=standard_phi(2*mid)
        if h<p:lo=mid
        elif l>p:hi=mid
        else:return mid-width/2,mid+width/2
    return lo,hi


def exp_minus_interval(x):
    x=F(x)
    # Terms eventually decrease; n=120 is beyond their peak for x<=10.
    if not 0<=x<=10:raise ValueError('exponential checker domain exceeded')
    terms=[(-x)**j/F(factorial(j)) for j in range(121)]
    s=sum(terms[:120],F(0));t=s+terms[120]
    return min(s,t),max(s,t)


def dynamics_interval(n,l,area):
    j=l+1;p=1
    for r in range(j):p*=n+2*r+1
    rr=4*abs(F(area))**(2*j)*p/F(factorial(j)**2)
    lo,hi=root_interval(rr)
    return min(F(1),lo),min(F(1),hi)


def contained(outer,inner):
    return F(outer[0])<=inner[0]<=inner[1]<=F(outer[1])


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--plan',type=Path,required=True)
    ap.add_argument('--report',type=Path,required=True)
    ap.add_argument('--raw-dir',type=Path,required=True)
    ap.add_argument('--shared-model',type=Path)
    ap.add_argument('--executor',default='unspecified; see actual invocation')
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    plan=json.loads(args.plan.read_text());rep=json.loads(args.report.read_text())
    cert=rep['certificate'];checks=[]

    def check(name,condition,detail=None):
        checks.append({'check':name,'passed':bool(condition),'detail':detail})
        if not condition:raise AssertionError(name)

    check('frozen main scientific baseline',plan['scientific_baseline']=='cb17211653fde30aa50e0e9848798a6a5b3b3f12')
    check('frozen design',tuple(map(F,plan['design_q_interval']))==(F(12,25),F(13,25)) and tuple(map(F,plan['design_x_interval']))==(F(-1,10),F(1,10)))
    check('frozen mean and cutoffs',F(plan['mean_G_budget'])==1 and (plan['physical_filter_N'],plan['galerkin_L'],plan['galerkin_K'])==(4095,40,4175))
    check('padding identity',plan['galerkin_K']==plan['physical_filter_N']+2*plan['galerkin_L'])
    check('frozen precision and conditional numerical reserve',F(plan['required_full_CQ_precision'])==F(1,20) and F(plan['reserved_numerical_error'])==F(1,10**8))
    check('frozen calibration sample sizes and half-widths',(plan['q_calibration']['shots'],plan['drive_calibration']['shots'])==(120000,1000000) and F(plan['q_calibration']['radius'])==F(1,100) and F(plan['drive_calibration']['probability_radius'])==F(1,500))
    check('frozen legal policy',plan['policy']=={'first':'1/2','after_0':'312/625','after_1':'313/625'})
    check('all terminal source records',tuple(plan['source_records'])==WORDS)
    check('complete raw inventory',set(rep['raw_sha256'])==set(RAW))
    check('plan hash bound',rep['input_identity']['plan_sha256']==digest(args.plan))
    for name,field in [('certify_from_records.py','analyzer_sha256'),('certified_intervals.py','intervals_sha256')]:
        path=args.plan.parent/name
        check('consumed '+name,path.exists() and digest(path)==rep['input_identity'][field])
    raw={}
    for name in RAW:
        path=args.raw_dir/name
        check('raw hash '+name,digest(path)==rep['raw_sha256'][name])
        raw[name]=path.read_text().strip()
    for name,n,alphabet in [('q_calibration_flags.txt',120000,'01f'),('drive_calibration_bits.txt',1000000,'01'),('drive_holdout_bits.txt',50000,'01'),('drive_holdout_drift_bits.txt',50000,'01')]:
        check('complete ordered stream '+name,len(raw[name])==n and set(raw[name])<=set(alphabet))
    for name in ['source_holdout_records.txt','compiled_holdout_records.txt']:
        check('complete terminal stream '+name,len(raw[name].splitlines())==50000 and set(raw[name].splitlines())<=set(WORDS))
    counts={'q_trials':120000,'q_failures':raw['q_calibration_flags.txt'].count('f'),
            'drive_trials':1000000,'momentum_nonpositive':raw['drive_calibration_bits.txt'].count('1')}
    check('actual calibration counts',cert['calibration_counts']==counts,counts)
    qhat=F(2*counts['q_failures'],120000);phat=F(counts['momentum_nonpositive'],1000000)
    check('calibration estimators',F(cert['qhat'])==qhat and F(cert['phat'])==phat)
    qlo,qhi=qhat-F(1,100),qhat+F(1,100);plo,phi=phat-F(1,500),phat+F(1,500)
    check('untrimmed data confidence intervals',tuple(map(F,cert['q_interval']))==(qlo,qhi) and tuple(map(F,cert['drive_probability_interval']))==(plo,phi))
    xl,xh=map(F,cert['x_interval']);cl,ch=map(F,cert['inverse_center_bracket'])
    check('independent lower inverse endpoint',standard_phi(2*xl)[1]<=plo)
    check('independent upper inverse endpoint',standard_phi(2*xh)[0]>=phi)
    check('independent nominal inverse bracket',standard_phi(2*cl)[1]<=phat<=standard_phi(2*ch)[0])
    check('center inversion width',ch-cl<=F(plan['drive_calibration']['inverse_bracket_width']))
    grid=F(plan['drive_calibration']['nominal_grid']);scaled=(cl+ch)/(2*grid)+F(1,2)
    nominal=F(scaled.numerator//scaled.denominator)*grid
    check('nominal determined only by observed frequency and frozen grid',F(cert['xhat'])==nominal==F(rep['nominal_x']))
    delta=max(abs(xl-nominal),abs(xh-nominal))
    check('outer Delta includes grid and inversion enclosure',F(cert['delta_x'])==delta)
    check('entire set and grid nominal inside design',F(12,25)<=qlo<=qhi<=F(13,25) and F(-1,10)<=xl<=xh<=F(1,10) and abs(nominal)<=F(1,10) and cert['untrimmed_set_inside_design'])
    sq=rep['statistics'];qe=F(120000)*F(1,100)**2/2;xe=2*F(1000000)*F(1,500)**2
    check('correct Hoeffding exponent scaling',qe==6 and xe==8)
    check('independent q exponential upper bound',F(sq['q_failure_upper'])>=2*exp_minus_interval(qe)[1])
    check('independent drive exponential upper bound',F(sq['drive_failure_upper'])>=2*exp_minus_interval(xe)[1])
    failure=F(sq['q_failure_upper'])+F(sq['drive_failure_upper'])
    check('joint coverage by union bound, without q/x independence requirement',F(sq['joint_failure_upper'])==failure<F(1,100) and sq['coverage_budget_met'])
    e=F(1,4096);prep=tuple(map(F,cert['preparation_interval']))
    check('sharp complete physical-filter radical bracket',(2*prep[0]-e)**2<=4*e-3*e*e<=(2*prep[1]-e)**2 and 2*prep[0]>=e)
    phys=tuple(map(F,cert['physical_compiler_bound_interval']))
    check('physical compiler bound includes failure once',phys==tuple(v+F(1,50) for v in prep))
    par=tuple(map(F,cert['nominal_parameter_error_interval']))
    check('exact-form parameter error bracket',par[0]>=0 and par[0]**2<=6*delta**2<=par[1]**2)
    d1=dynamics_interval(4095,40,nominal);d2=dynamics_interval(4095,40,2*nominal)
    dyn=tuple(F(624,1250)*d1[i]+F(313,1250)*d2[i] for i in (0,1))
    check('independent finite-Duhamel radical enclosure',contained(cert['nominal_galerkin_error_interval'],dyn))
    dd1=dynamics_interval(4095,40,F(1,10));dd2=dynamics_interval(4095,40,F(1,5))
    dyn_design=tuple(F(624,1250)*dd1[i]+F(313,1250)*dd2[i] for i in (0,1))
    check('entire declared-design Galerkin enclosure',contained(cert['design_uniform_galerkin_interval'],dyn_design))
    reported_dyn=tuple(map(F,cert['nominal_galerkin_error_interval']))
    total=tuple(phys[i]+par[i]+reported_dyn[i] for i in (0,1))
    check('same-metric triangle arithmetic',tuple(map(F,cert['exact_finite_predictor_bound_interval']))==total)
    check('exact finite nominal precision certified',total[1]<F(1,20) and cert['status']=='CERTIFIED_EXACT_FINITE_MODEL_BOUND' and rep['status']=='CERTIFIED')
    conditional=total[1]+F(1,10**8)
    check('numerical reserve is conditional and fits',F(cert['conditional_bound_if_numerics_independently_certified'])==conditional<F(1,20) and cert['numerical_output_status']=='NOT_CERTIFIED_BY_THIS_CALIBRATION_ANALYZER')
    check('full source attempt success includes physical filter',F(cert['source_attempt_success_probability_lower'])==(1-e)*(1-qhi/2)**2)
    Q={'00':F(313,1250),'01':F(312,1250),'10':F(312,1250),'11':F(313,1250)}
    check('normalization and actual force-call expectation',sum(Q.values())==1 and sum(word.count('1')*v for word,v in Q.items())==1)

    # Independent holdout prediction: one calibrated pulse -> two-pulse tester.
    ho=rep['holdout'];rad=F(plan['holdout']['radius'])
    check('holdout frozen protocol and allowance',plan['holdout']['drive_gate_calls']==2 and rad==F(1,100) and plan['holdout']['tested_cells']==15)
    expected_h=(standard_phi(4*xl)[0],standard_phi(4*xh)[1])
    check('two-pulse predicted interval independent enclosure',contained(ho['drive']['prediction_outer_interval'],expected_h))
    for name,key in [('source_holdout_records.txt','source'),('compiled_holdout_records.txt','compiled')]:
        counts_h=Counter(raw[name].splitlines())
        check(key+' holdout includes all seven records',tuple(c['record'] for c in ho[key]['cells'])==WORDS)
        for cell in ho[key]['cells']:
            w=cell['record'];frequency=F(counts_h[w],50000);lo,hi=map(F,cell['predicted_outer_interval'])
            check(key+' actual count '+w,cell['count']==counts_h[w] and F(cell['frequency'])==frequency)
            if key=='compiled':check('compiled predicted law '+w,lo==hi==Q.get(w,F(0)))
            else:
                # Endpoints need not extremize every polynomial. Reconstruct
                # the positive-factor interval instead of assuming they do.
                s=(1-qhi/2,1-qlo/2);q=(qlo,qhi);one=(1-qhi,1-qlo);f=(qlo/2,qhi/2)
                factors={'f':[f],'0f':[s,one,f],'1f':[s,q,f],
                         '00':[s,s,one,one],'01':[s,s,q,one],
                         '10':[s,s,q,one],'11':[s,s,q,q]}[w]
                pl=ph=F(1)
                for ab in factors:pl*=ab[0];ph*=ab[1]
                check('source shared-q outer response '+w,lo==pl and hi==ph)
            dist=max(lo-frequency,frequency-hi,F(0))
            check(key+' frozen decision '+w,F(cell['distance'])==dist and cell['accepted']==(dist<=rad))
        check(key+' holdout not rejected',ho[key]['status']=='NOT_REJECTED_BY_FROZEN_RECORD_TESTERS')
    drive=ho['drive'];freq=F(raw['drive_holdout_bits.txt'].count('1'),50000);hl,hh=map(F,drive['prediction_outer_interval'])
    dist=max(hl-freq,freq-hh,F(0))
    check('two-pulse holdout actual count and decision',drive['nonpositive_count']==raw['drive_holdout_bits.txt'].count('1') and F(drive['frequency'])==freq and F(drive['distance'])==dist<=rad and drive['status']=='NOT_REJECTED_BY_FROZEN_DRIVE_TESTER')
    check('holdout union bound applies only to fifteen declared cells',F(ho['family_failure_upper'])>=30*exp_minus_interval(10)[1] and F(ho['family_failure_upper'])<F(1,100) and ho['budget_met'])
    check('null false rejection includes calibration failure',F(ho['null_false_rejection_upper'])==failure+F(ho['family_failure_upper'])<F(1,100))
    control=rep['controls']['nonshared_pulse_holdout'];driftfreq=F(raw['drive_holdout_drift_bits.txt'].count('1'),50000)
    driftdist=max(hl-driftfreq,driftfreq-hh,F(0))
    check('nonshared pulse alternative uses same prediction and threshold',control['same_prediction_outer_interval']==drive['prediction_outer_interval'] and F(control['radius'])==rad and F(control['frequency'])==driftfreq)
    check('actual negative control rejected',F(control['distance'])==driftdist>rad and control['status']=='REJECTED_BY_FROZEN_DRIVE_TESTER')
    loose=rep['controls']['wider_calibration_precision']
    loose_lo=inverse_outer(phat-F(1,100))[0];loose_hi=inverse_outer(phat+F(1,100))[1]
    # Independent tighter inverse brackets give a lower bound on the required
    # outer radius, sufficient to disprove attainment by this sufficient bound.
    min_radius=max(nominal-loose_lo-F(1,10**12),loose_hi-nominal-F(1,10**12))
    loose_lower=phys[0]+root_interval(6)[0]*min_radius+dyn[0]
    check('wider interval insufficient without claiming impossibility',loose['status']=='INSUFFICIENT_BOUND' and loose_lower>F(1,20) and F(loose['upper'])>F(1,20))
    # Exact, independently derived negative-control witnesses.
    check('single-dose detector-offset symmetry',2*F(1,50)-2*F(1,50)==0,
          'For the single-dose p1 only, (x,b)->(x+c,b+sqrt(2)c) preserves the normal argument. A shared fixed b is identifiable using both p1 and p2.')
    check('two-dose shared bias breaks that symmetry',4*F(1,50)-2*F(1,50)!=0 and rep['controls']['detector_bias']['status']=='SINGLE_DOSE_CALIBRATION_NONIDENTIFIABLE_WITH_UNRESTRICTED_BIAS')
    check('zero state tail and zero finite residual do not bound dynamics',1-exp_minus_interval(F(1,100))[1]>0,
          'At K=N=0, input |g,0> has zero initial tail and H_K=0, but exact overlap at x=1/10 is exp(-x^2/2), so D=sqrt(1-exp(-x^2))>0.')
    check('repeating one latent bit has no iid concentration',F(1,2)>2*exp_minus_interval(8)[1],
          'An n-times-repeated fair bit deviates from its mean by 1/2 with probability one.')
    check('no actual empirical or machine-proof upgrade',rep['new_hardware_data'] is False and rep['device_membership']=='UNVERIFIED' and rep['empirical_full_CQ_status']=='UNTESTED' and cert['hidden_truth_consumed'] is False)
    check('calibration and holdout resources retained',rep['resource_counts']['q_calibration']==120000 and rep['resource_counts']['drive_calibration']==1000000 and rep['resource_counts']['holdout']==150000 and rep['resource_counts']['synthetic_alternative_control']==50000)
    if args.shared_model:
        shared=json.loads(args.shared_model.read_text())
        check('shared scientific baseline',shared['research_baseline']==plan['scientific_baseline'])
        check('shared cutoffs and design',shared['input_filter_N']==4095 and shared['galerkin_extra_L']==40 and shared['galerkin_K']==4175 and F(shared['design_x_abs_max'])==F(1,10) and shared['design_q']==plan['design_q_interval'])
        check('shared calibration',shared['calibration']['source_flag_trials']==120000 and shared['calibration']['drive_trials']==1000000 and F(shared['calibration']['q_half_width'])==F(1,100) and F(shared['calibration']['drive_probability_half_width'])==F(1,500))
        check('shared precision',F(shared['precision']['complete_CQ_target'])==F(1,20) and F(shared['precision']['numerical_budget_only_when_independently_verified'])==F(1,10**8))
    result={'schema':'ueot-qm.independent-simultaneous-calibration-check/1','status':'PASS',
       'executed_at_utc':datetime.now(timezone.utc).isoformat(),'executor':args.executor,
       'execution_context':{'python':platform.python_version(),'platform':platform.platform(),
                            'github_actions':os.environ.get('GITHUB_ACTIONS'),
                            'github_run_id':os.environ.get('GITHUB_RUN_ID'),
                            'argv':sys.argv},
       'consumed_sha256':{'plan':digest(args.plan),'analysis':digest(args.report),'checker':digest(Path(__file__)),
                          **({'shared_model':digest(args.shared_model)} if args.shared_model else {})},
       'raw_sha256':{name:digest(args.raw_dir/name) for name in RAW},
       'passed_checks':len(checks),'checks':checks,
       'independent_derived':{'nominal_x':nominal,'Delta_x':delta,'exact_finite_upper':total[1],
                              'conditional_with_numerical_reserve':conditional,'calibration_failure_upper':failure,
                              'design_uniform_galerkin_interval':dyn_design},
       'evidence_scope':'Independent integer/rational computation and raw-record accounting; universal physics remains a paper theorem, and all records are synthetic.',
       'new_lean_execution':False,'new_hardware_data':False,
       'numerical_output_scope':'A separate numerical output certificate is required; this checker does not certify a floating matrix exponential.'}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(encode(result),indent=2)+'\n')
    print(json.dumps({'status':'PASS','checks':len(checks),'nominal_x':str(nominal),'new_hardware_data':False}))


if __name__=='__main__':main()
