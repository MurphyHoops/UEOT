#!/usr/bin/env python3
"""Bind the calibrated finite-map certificate to the stated interval output."""
import argparse
from datetime import datetime, timezone
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--directory',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    a=ap.parse_args();checks=[]
    def ck(name,ok):
        if not ok:raise AssertionError(name)
        checks.append({'name':name,'status':'PASS'})
    names=['integration.json','operational.json','micro.json','calibration.json',
           'independent-calibration.json','interval-prediction.json','independent-interval.json']
    data={n:json.loads((a.directory/n).read_text()) for n in names}
    for n,d in data.items():ck(n+' accepted in its explicit scope',d['status'] in {'PASS','CERTIFIED'})
    cal=data['calibration.json'];pred=data['interval-prediction.json'];cert=cal['certificate']
    ck('nominal area actually selected from calibration',F(pred['nominal_x'])==F(cal['nominal_x'])==F(cert['xhat']))
    ck('calibration file is exactly the consumed file',pred['calibration_identity']['sha256']==hashlib.sha256((a.directory/'calibration.json').read_bytes()).hexdigest())
    ck('raw truth was not available to analyzer',cert['hidden_truth_consumed'] is False)
    ck('raw full model response is not inferred from finite tester samples',cert['full_CQ_not_inferred_from_test_counts'] is True)
    ck('untrimmed calibration set admitted',cert['untrimmed_set_inside_design'] is True)
    exact=F(cert['exact_finite_predictor_bound_interval'][1])
    num=F(pred['complete_CQ_numerical_error_upper'])
    reserved=F(pred['reserved_budget']);required=F(cert['required_precision'])
    ck('independent numerical error fits the frozen reservation',0<=num<reserved==F(1,10**8))
    ck('exact finite-map full-domain bound meets frozen precision',exact<required==F(1,20))
    ck('this computed input meets precision including actual numerical error',exact+num<required)
    ck('reservation itself fits with a positive margin',exact+reserved<required)
    ck('wider calibration is not falsely certified',cal['controls']['wider_calibration_precision']['status']=='INSUFFICIENT_BOUND')
    ck('held-out nonshared drive is rejected without refit',cal['controls']['nonshared_pulse_holdout']['status']=='REJECTED_BY_FROZEN_DRIVE_TESTER')
    ck('shared two-pulse response is held out',cal['holdout']['drive']['status']=='NOT_REJECTED_BY_FROZEN_DRIVE_TESTER')
    ck('fixed-sample coverage failure is below budget',F(cal['statistics']['joint_failure_upper'])<F(1,100))
    ck('no empirical status promotion',cal['new_hardware_data'] is False and cal['empirical_full_CQ_status']=='UNTESTED')
    report={'schema':'ueot-qm.simultaneous-end-to-end/1','status':'PASS',
      'created_at_utc':datetime.now(timezone.utc).isoformat(),'checks':checks,'check_count':len(checks),
      'exact_finite_map_uniform_bound':str(exact),'specified_input_numerical_error':str(num),
      'specified_input_total_bound':str(exact+num),'specified_input_bound_with_reserved_error':str(exact+reserved),
      'remaining_reserved_margin':str(required-exact-reserved),
      'decimal_diagnostics':{'exact_finite_map':float(exact),'numerical':float(num),
        'with_reserved_error':float(exact+reserved),'remaining_margin':float(required-exact-reserved)},
      'inputs':{n:hashlib.sha256((a.directory/n).read_bytes()).hexdigest() for n in names},
      'universal_numerical_certification':False,'interval_input':pred['input_state'],
      'independent_physical_inputs':'complex Fock/Born/CP model, effective shared force and phase, ideal filter and readout, fixed iid calibration',
      'empirical_status':'UNTESTED_NO_REAL_DEVICE_DATA','new_lean_execution':False}
    a.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':'PASS','checks':len(checks),**report['decimal_diagnostics']}))


if __name__=='__main__':main()
