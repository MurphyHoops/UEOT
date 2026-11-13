"""Attach directed displays and exact repaired predictions without changing frozen data.

The nominal JSON and classifier results retain their historical hashes. The
review correction below fixes presentation rounding, not the data or decisions.
"""
from __future__ import annotations
import argparse, datetime, importlib.util
from fractions import Fraction as F
from pathlib import Path
from common_c import BASE, decimal_string, digest, dump_json, load_json

def directed(x,upper=False,digits=12):
    x=F(x); scale=10**digits; value=x*scale
    integer=value.numerator//value.denominator
    if upper and value != integer: integer+=1
    return decimal_string(F(integer,scale),digits)

def main():
    p=argparse.ArgumentParser();p.add_argument('--certificate-dir',type=Path)
    a=p.parse_args()
    certdir=a.certificate_dir or (BASE if (BASE/'interval_certificate_index.json').exists() else BASE.parent/'work_b')
    spec=importlib.util.spec_from_file_location('rational_physical_prediction',certdir/'physical_prediction.py')
    pp=importlib.util.module_from_spec(spec);spec.loader.exec_module(pp)
    nominal=load_json(BASE/'NOMINAL_MODEL.json');held=load_json(BASE/'HOLDOUT_RESULTS.json')
    lam=F(nominal['lambda_hat']);eta=F(nominal['eta_hat'])
    l,u=map(F,nominal['lambda_projection_outer']);el,eu=map(F,nominal['eta_projection_outer'])
    radius=max(lam-l,u-lam);eradius=max(eta-el,eu-eta)
    parameter=F(51,10)*radius;truncation=F('0.00001344');repair=F('0.00000001')
    quantum=parameter+truncation+repair
    measured=quantum+eradius/2
    assert quantum < F('0.05') and measured < F('0.05')
    corrected={}
    status_unchanged=True
    for name,family in held['families'].items():
        rows=[];reject=False
        for s in family['settings']:
            env=[[max(F(0),F(lo)-F('1e-12')),min(F(1),F(hi)+F('1e-12'))] for lo,hi in s['calibration_prediction_envelope']]
            obs=[[max(F(0),F(lo)-F('1e-12')),min(F(1),F(hi)+F('1e-12'))] for lo,hi in s['empirical_event_intervals']]
            bad=[j for j,(x,y) in enumerate(zip(env,obs)) if x[1]<y[0] or y[1]<x[0]]
            reject |= bool(bad)
            rows.append({'observable':s['observable'],'model_envelope_outward':[[directed(lo),directed(hi,True)] for lo,hi in env],
                         'data_interval_outward':[[directed(lo),directed(hi,True)] for lo,hi in obs],'disjoint_events':bad})
        status='REJECTED_MODEL_CONTRACT' if reject else 'NOT_REJECTED_FROZEN_HOLDOUT'
        status_unchanged &= status == family['status']
        corrected[name]={'status':status,'settings':rows}
    assert status_unchanged
    exact_predictions={};exact_comparisons={};bindings={}
    for timing in ['original','permuted']:
        backend_results={}
        for backend in ['weyl','galerkin']:
            path=certdir/f'interval_calibrated_{timing}_{backend}.json'
            certificate=load_json(path)
            assert F(certificate['lambda_exact']) == lam
            bindings[path.name]=digest(path)
            backend_results[backend]={obs:pp.event_probabilities(path,str(eta),obs) for obs in ['XX','XY','YZ','ZZ']}
        exact_predictions[timing]={b:{obs:[str(x) for x in vals] for obs,vals in data.items()} for b,data in backend_results.items()}
        exact_comparisons[timing]={obs:str(sum(abs(x-y) for x,y in zip(backend_results['weyl'][obs],backend_results['galerkin'][obs]))/2) for obs in ['XX','XY','YZ','ZZ']}
    result={'schema':'final-persistent-bath-calibration-certificate/1','created_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),
      'nominal_sha256_unchanged':digest(BASE/'NOMINAL_MODEL.json'),'heldout_results_sha256_unchanged':digest(BASE/'HOLDOUT_RESULTS.json'),
      'calibration_shots_sha256':digest(BASE/'calibration_shots.npz'),'holdout_shots_sha256':digest(BASE/'holdout_shots.npz'),
      'review_correction':'B found nearest-rounded displays could understate an exact upper bound by <1e-12. Frozen decisions used exact Fractions; this file supplies authoritative directed displays and conservative event intervals without resampling/refitting.',
      'parameter_error_exact':str(parameter),'parameter_error_upper':directed(parameter,True),
      'truncation_error_exact':str(truncation),'physical_numerical_repair_error_exact':str(repair),
      'quantum_complete_CQ_bound_exact':str(quantum),'quantum_complete_CQ_upper':directed(quantum,True),
      'terminal_visibility_error_exact':str(eradius/2),'terminal_visibility_error_upper':directed(eradius/2,True),
      'fixed_complete_terminal_tester_bound_exact':str(measured),'fixed_complete_terminal_tester_upper':directed(measured,True),
      'target':'1/20','source_certificate_status':'CERTIFIED_CONDITIONAL_SYNTHETIC_SOURCE',
      'hardware_status':'NOT_CERTIFIED','method_gain':'EQUIVALENT_NO_ADDED_GAIN',
      'calibration_coverage_failure_upper':'1/100','holdout_simultaneous_failure_upper':'1/100',
      'corrected_heldout_displays':corrected,'all_original_decisions_unchanged':status_unchanged,
      'exact_repaired_prediction_certificate_bindings':bindings,'exact_repaired_event_probabilities':exact_predictions,
      'exact_repaired_backend_TV_differences':exact_comparisons,
      'generator_probability_check_sha256':digest(BASE/'GENERATOR_PROBABILITY_CHECK.json'),
      'scope':'arbitrary S/R input to the fixed complete three-slot source for the CQ bound; four fixed terminal Pauli testers for the detector bound; exact stored rational Choi predictor, not an unbudgeted later floating contraction'}
    dump_json(BASE/'FINAL_CERTIFICATE.json',result)
    print({k:result[k] for k in ['parameter_error_upper','quantum_complete_CQ_upper','fixed_complete_terminal_tester_upper','all_original_decisions_unchanged']})

if __name__=='__main__':main()
