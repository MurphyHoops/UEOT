#!/usr/bin/env python3
"""Analyze only observed synthetic/raw calibration and disjoint holdout files.

The analysis neither opens synthetic_provenance.json nor receives true q/x.
The result certifies a mathematical finite predictor under declared model
membership, not the laboratory or the floating implementation.
"""
from collections import Counter
from pathlib import Path
from fractions import Fraction as F
import argparse, hashlib, json
from certified_intervals import (inverse_probability_interval,
    normal_half_axis_probability, sqrt_interval, galerkin_interval,
    exp_negative_upper)

RECORDS=('f','0f','1f','00','01','10','11')


def encode(x):
    if isinstance(x,F):return str(x)
    if isinstance(x,dict):return {k:encode(v) for k,v in x.items()}
    if isinstance(x,(tuple,list)):return [encode(v) for v in x]
    return x


def read_symbols(path,expected,alphabet):
    text=path.read_text().strip()
    if len(text)!=expected or set(text)-set(alphabet):
        raise ValueError('Missing, extra, failure/leakage, or illegal calibration outcomes: '+str(path))
    return text


def from_counts(plan,nq,nf,nx,nnegative):
    """No truth input; no silent clipping to the design interval."""
    rq=F(plan['q_calibration']['radius']);rp=F(plan['drive_calibration']['probability_radius'])
    qhat=F(2*nf,nq);phat=F(nnegative,nx)
    qlo,qhi=max(F(0),qhat-rq),min(F(1),qhat+rq)
    plo,phi=max(F(0),phat-rp),min(F(1),phat+rp)
    result={'qhat':qhat,'phat':phat,'q_interval':[qlo,qhi],
            'drive_probability_interval':[plo,phi],
            'calibration_counts':{'q_trials':nq,'q_failures':nf,'drive_trials':nx,'momentum_nonpositive':nnegative},
            'policy':plan['policy'],'hidden_truth_consumed':False}
    if qlo>qhi:
        result['status']='INCONSISTENT_CALIBRATION_MODEL';return result
    try:
        width=F(plan['drive_calibration']['inverse_bracket_width'])
        xlo=inverse_probability_interval(plo,width)[0]
        xhi=inverse_probability_interval(phi,width)[1]
        center=inverse_probability_interval(phat,width)
    except (ValueError,ArithmeticError) as exc:
        result.update(status='INSUFFICIENT_CERTIFICATE',reason=str(exc));return result
    grid=F(plan['drive_calibration']['nominal_grid'])
    center_mid=sum(center)/2
    # Deterministic quantization of a certified center bracket, not hidden truth.
    scaled=center_mid/grid
    nearest=(scaled+F(1,2)).numerator//(scaled+F(1,2)).denominator
    xhat=nearest*grid
    delta=max(abs(xlo-xhat),abs(xhi-xhat))
    result.update(x_interval=[xlo,xhi],inverse_center_bracket=center,
                  xhat=xhat,delta_x=delta)
    designq=tuple(map(F,plan['design_q_interval']));designx=tuple(map(F,plan['design_x_interval']))
    admitted=(designq[0]<=qlo<=qhi<=designq[1] and designx[0]<=xlo<=xhi<=designx[1]
              and designx[0]<=xhat<=designx[1])
    result['untrimmed_set_inside_design']=admitted
    if not admitted:
        result.update(status='INSUFFICIENT_CERTIFICATE',reason='Entire data-derived set must be within the design; it is not trimmed to pass.')
        return result
    e=F(plan['mean_G_budget'])/F(plan['physical_filter_N']+1)
    root=sqrt_interval(4*e-3*e*e)
    preparation=((e+root[0])/2,(e+root[1])/2)
    n=plan['physical_filter_N'];l=plan['galerkin_L']
    d1=galerkin_interval(n,l,abs(xhat));d2=galerkin_interval(n,l,2*abs(xhat))
    a=F(312,625);b=F(313,1250)
    dynamics=(a*d1[0]+b*d2[0],a*d1[1]+b*d2[1])
    invariant=sqrt_interval(4*F(plan['mean_G_budget'])+2)
    parameter=(invariant[0]*delta,invariant[1]*delta)
    physical=(F(1,50)+preparation[0],F(1,50)+preparation[1])
    total=(physical[0]+parameter[0]+dynamics[0],physical[1]+parameter[1]+dynamics[1])
    reserved=F(plan['reserved_numerical_error']);target=F(plan['required_full_CQ_precision'])
    upper_with_reservation=total[1]+reserved
    design_x=max(abs(v) for v in designx)
    dd1=galerkin_interval(n,l,design_x);dd2=galerkin_interval(n,l,2*design_x)
    result.update(
        status='CERTIFIED_EXACT_FINITE_MODEL_BOUND' if total[1]<target else 'INSUFFICIENT_BOUND',
        preparation_interval=preparation,physical_compiler_bound_interval=physical,
        nominal_parameter_error_interval=parameter,nominal_galerkin_error_interval=dynamics,
        exact_finite_predictor_bound_interval=total,
        conditional_bound_if_numerics_independently_certified=upper_with_reservation,
        numerical_reservation_fits=upper_with_reservation<target,
        numerical_output_status='NOT_CERTIFIED_BY_THIS_CALIBRATION_ANALYZER',
        design_uniform_galerkin_interval=(a*dd1[0]+b*dd2[0],a*dd1[1]+b*dd2[1]),
        source_attempt_success_probability_lower=(1-e)*(1-qhi/2)**2,
        required_precision=target,
        full_CQ_not_inferred_from_test_counts=True)
    return result


def product(*pairs):
    a,b=F(1),F(1)
    for lo,hi in pairs:a*=lo;b*=hi
    return a,b


def source_ranges(qlo,qhi):
    q=qlo,qhi;one=1-qhi,1-qlo;s=1-qhi/2,1-qlo/2;f=qlo/2,qhi/2
    return {'f':f,'0f':product(s,one,f),'1f':product(s,q,f),
            '00':product(s,s,one,one),'01':product(s,s,q,one),
            '10':product(s,s,q,one),'11':product(s,s,q,q)}


def holdout_records(path,n,predicted,radius):
    rows=path.read_text().splitlines()
    if len(rows)!=n or set(rows)-set(RECORDS):
        raise ValueError('Incomplete source holdout, unknown failure, or leakage: '+str(path))
    counts=Counter(rows);cells=[]
    for word in RECORDS:
        f=F(counts[word],n);lo,hi=predicted[word];distance=max(lo-f,f-hi,F(0))
        cells.append({'record':word,'count':counts[word],'frequency':f,
                      'predicted_outer_interval':[lo,hi],'distance':distance,'accepted':distance<=radius})
    return {'status':'NOT_REJECTED_BY_FROZEN_RECORD_TESTERS' if all(c['accepted'] for c in cells) else 'REJECTED_BY_FROZEN_RECORD_TESTERS',
            'shots':n,'all_failures_retained':True,'cells':cells}


def analyze(plan,raw):
    nq=plan['q_calibration']['shots'];nx=plan['drive_calibration']['shots']
    flags=read_symbols(raw/'q_calibration_flags.txt',nq,'01f')
    bits=read_symbols(raw/'drive_calibration_bits.txt',nx,'01')
    cert=from_counts(plan,nq,flags.count('f'),nx,bits.count('1'))
    qbound=2*exp_negative_upper(F(nq)*F(plan['q_calibration']['radius'])**2/2)
    xbound=2*exp_negative_upper(2*F(nx)*F(plan['drive_calibration']['probability_radius'])**2)
    statistical={'q_failure_upper':qbound,'drive_failure_upper':xbound,
                 'joint_failure_upper':qbound+xbound,
                 'budget':F(plan['calibration_family_failure_budget']),
                 'coverage_budget_met':qbound+xbound<F(plan['calibration_family_failure_budget']),
                 'conditional_on':'fixed shared q,x, iid fresh trials, ideal calibration preparation/readout; not device model verification',
                 'coverage_semantics':'At the frozen fixed sample sizes, P(true theta outside C) and P(a certificate is emitted but invalid because of calibration) are at most this failure bound. No 99% post-selection conditional coverage is claimed.',
                 'optional_stopping':'Not covered; do not repeat until admitted under this fixed-sample guarantee.'}
    holdouts={}
    if cert['status']=='CERTIFIED_EXACT_FINITE_MODEL_BOUND':
        n=plan['holdout']['shots_per_stream'];rad=F(plan['holdout']['radius'])
        qlo,qhi=cert['q_interval']
        words={'00':F(313,1250),'01':F(312,1250),'10':F(312,1250),'11':F(313,1250)}
        holdouts['source']=holdout_records(raw/'source_holdout_records.txt',n,source_ranges(qlo,qhi),rad)
        holdouts['compiled']=holdout_records(raw/'compiled_holdout_records.txt',n,{r:(words.get(r,F(0)),)*2 for r in RECORDS},rad)
        drive=read_symbols(raw/'drive_holdout_bits.txt',n,'01');frequency=F(drive.count('1'),n)
        calls=plan['holdout']['drive_gate_calls']
        lo=normal_half_axis_probability(calls*cert['x_interval'][0])[0]
        hi=normal_half_axis_probability(calls*cert['x_interval'][1])[1]
        distance=max(lo-frequency,frequency-hi,F(0))
        holdouts['drive']={'shots':n,'nonpositive_count':drive.count('1'),'frequency':frequency,
                           'prediction_outer_interval':[lo,hi],'distance':distance,
                           'protocol':'two consecutive same force gates; Phi(4*x), with no holdout refit',
                           'status':'NOT_REJECTED_BY_FROZEN_DRIVE_TESTER' if distance<=rad else 'REJECTED_BY_FROZEN_DRIVE_TESTER'}
        holdouts['family_failure_upper']=2*plan['holdout']['tested_cells']*exp_negative_upper(2*n*rad*rad)
        holdouts['family_budget']=F(plan['holdout_family_failure_budget'])
        holdouts['budget_met']=holdouts['family_failure_upper']<holdouts['family_budget']
        holdouts['null_false_rejection_upper']=statistical['joint_failure_upper']+holdouts['family_failure_upper']
        holdouts['meaning']='Synthetic finite tester checks only. The holdout family bound controls deviations from the true probabilities; false rejection of a shared model also includes the calibration-set failure bound. Neither empirical nor full-CQ certification is inferred.'
    # Algebraic/model-bound controls; none is promoted to hardware evidence.
    wider=json.loads(json.dumps(plan));wider['drive_calibration']['probability_radius']='1/100'
    loose=from_counts(wider,nq,flags.count('f'),nx,bits.count('1'))
    controls={
        'wider_calibration_precision':{'status':loose['status'],'upper':loose.get('exact_finite_predictor_bound_interval',[None,None])[1],
            'meaning':'Failure of this sufficient upper bound is not physical impossibility'},
        'flag_only':{'status':'INSUFFICIENT_IDENTIFIABILITY','witness':'q equal, x unequal => every source record probability identical'},
        'detector_bias':{'status':'SINGLE_DOSE_CALIBRATION_NONIDENTIFIABLE_WITH_UNRESTRICTED_BIAS',
            'probability':'Phi(2*x-sqrt(2)*b)','symmetry':'(x,b) -> (x+c,b+sqrt(2)*c)',
            'bias_convention':'observed momentum equals physical momentum plus b; record observed momentum <= 0',
            'meaning':'Single-dose calibration alone does not identify x when b is unrestricted. This analyzer assumes b=0.',
            'two_dose_fixed_bias':'Phi(2*x-sqrt(2)*b) and Phi(4*x-sqrt(2)*b) jointly identify x and a shared fixed b; the second dose is held out here, not fitted.',
            'setting_dependent_bias':'If separate unrestricted b_k are allowed, (x,b_k)->(x+c,b_k+sqrt(2)*k*c) preserves every k-dose binary probability.'},
        'numerical_residual':{'status':'NOT_AN_ANALYTIC_BOUND','example':'K=0 gives a 1x1 identity with zero exponentiation residual while the true force maps vacuum to a nonvacuum state'},
        'mean_tail':{'status':'MEAN_OR_STATE_TAIL_NOT_GALERKIN_ERROR','example':'With a sigma_x eigenprobe and vacuum oscillator, nonzero force creates a coherent state with a Poisson infinite tail; a hard truncated evolution can return to vacuum while the exact evolved state has nonzero displacement'},
        'dependent_shots':{'status':'IID_ASSUMPTION_REQUIRED','example':'one latent Bernoulli bit repeated n times has correct one-shot marginals but no Hoeffding concentration'},
    }
    if 'drive' in holdouts:
        ctrl=plan['synthetic_nonshared_pulse_control']
        drift=read_symbols(raw/'drive_holdout_drift_bits.txt',ctrl['shots'],'01')
        frequency=F(drift.count('1'),ctrl['shots']);lo,hi=holdouts['drive']['prediction_outer_interval']
        distance=max(lo-frequency,frequency-hi,F(0))
        controls['nonshared_pulse_holdout']={'shots':ctrl['shots'],'nonpositive_count':drift.count('1'),
            'frequency':frequency,'same_prediction_outer_interval':[lo,hi],'distance':distance,
            'radius':F(plan['holdout']['radius']),
            'status':'REJECTED_BY_FROZEN_DRIVE_TESTER' if distance>F(plan['holdout']['radius']) else 'NOT_REJECTED_BY_FROZEN_DRIVE_TESTER',
            'meaning':'Explicitly synthetic alternative-model control; no refit and no complete-CQ or empirical inference'}
    raw_names=['q_calibration_flags.txt','drive_calibration_bits.txt','source_holdout_records.txt','compiled_holdout_records.txt','drive_holdout_bits.txt','drive_holdout_drift_bits.txt']
    return {'schema':'ueot-qm.simultaneous-calibrated-nominal/1','classification':'SYNTHETIC_ONLY_CONDITIONAL_MODEL_CERTIFICATE',
            'status':'CERTIFIED' if cert['status']=='CERTIFIED_EXACT_FINITE_MODEL_BOUND' and statistical['coverage_budget_met'] else 'INSUFFICIENT_CERTIFICATE',
            'nominal_x':cert.get('xhat'),
            'status_scope':'Conditional mathematical calibration/finite-model error certificate only; neither hardware membership nor floating-output accuracy is certified.',
            'new_hardware_data':False,'certificate':cert,'statistics':statistical,'holdout':holdouts,'controls':controls,
            'raw_sha256':{n:hashlib.sha256((raw/n).read_bytes()).hexdigest() for n in raw_names},
            'raw_input_policy':'Only these six complete raw streams are consumed; provenance/hidden truth are not read.',
            'resource_counts':{'q_calibration':nq,'drive_calibration':nx,'holdout':3*plan['holdout']['shots_per_stream'],
                               'synthetic_alternative_control':plan['synthetic_nonshared_pulse_control']['shots'],
                               'time_energy_money_costs':'UNMEASURED','calibration_amortization':'one-time cost divided by outputs, not by source retry success'},
            'device_membership':'UNVERIFIED','empirical_full_CQ_status':'UNTESTED','numerical_budget_requires_independent_output_receipt':True}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--plan',type=Path,required=True);p.add_argument('--raw-dir',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();plan=json.loads(a.plan.read_text());result=analyze(plan,a.raw_dir)
    result['input_identity']={'plan_sha256':hashlib.sha256(a.plan.read_bytes()).hexdigest(),
        'analyzer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'intervals_sha256':hashlib.sha256(Path(__file__).with_name('certified_intervals.py').read_bytes()).hexdigest()}
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(encode(result),indent=2)+'\n')
    print(json.dumps(encode({'status':result['certificate']['status'],'xhat':result['certificate'].get('xhat'),
                            'counts':result['certificate']['calibration_counts'],
                            'upper':result['certificate'].get('exact_finite_predictor_bound_interval',[None,None])[1],
                            'new_hardware_data':False})))


if __name__=='__main__':main()
