#!/usr/bin/env python3
import json
from pathlib import Path

# Registered before evaluation: same budget point, same coordinate normalization,
# operator-norm error radius eta, practical-zero tolerance tau0.
eta = 0.10
tau0 = 0.15

def verdict(sigma3_hat):
    if eta < sigma3_hat:
        return 'REJECTED'
    if sigma3_hat + eta <= tau0:
        return 'COMPATIBLE'
    return 'AMBIGUOUS'

# Diagonal sensitivity benchmarks make exact singular values transparent without
# a numerical linear-algebra dependency.
cases = [
    {
      'name':'two_drive_positive_control_discovery',
      'true_diagonal':[3.0,2.0,0.0],
      'estimated_diagonal':[3.04,1.96,0.04],
      'sigma3_hat':0.04,
      'expected':'COMPATIBLE'
    },
    {
      'name':'three_drive_negative_control_discovery',
      'true_diagonal':[3.0,2.0,1.0],
      'estimated_diagonal':[2.95,2.02,0.93],
      'sigma3_hat':0.93,
      'expected':'REJECTED'
    },
    {
      'name':'boundary_ambiguous',
      'true_diagonal':[3.0,2.0,0.10],
      'estimated_diagonal':[3.01,1.97,0.08],
      'sigma3_hat':0.08,
      'expected':'AMBIGUOUS'
    },
    {
      'name':'two_drive_heldout',
      'true_diagonal':[2.5,1.7,0.0],
      'estimated_diagonal':[2.44,1.73,0.03],
      'sigma3_hat':0.03,
      'expected':'COMPATIBLE'
    },
    {
      'name':'three_drive_heldout',
      'true_diagonal':[2.5,1.7,0.8],
      'estimated_diagonal':[2.46,1.72,0.74],
      'sigma3_hat':0.74,
      'expected':'REJECTED'
    },
]
for c in cases:
    c['verdict']=verdict(c['sigma3_hat'])
    c['pass']=c['verdict']==c['expected']

out={
  'kind':'SYNTHETIC_DUAL_DRIVE_METHOD_BENCHMARK_NOT_MECHANISM_IDENTIFICATION',
  'registration':{
      'same_budget_point_required':True,
      'coordinate_normalization':'fixed registered diagonal benchmark coordinates',
      'finite_difference_bandwidth':'not_applicable_exact_linear_benchmark',
      'eta_operator_norm':eta,
      'tau0_practical_zero':tau0,
      'decision_rule':'reject if eta < sigma3_hat; compatible if sigma3_hat+eta <= tau0; else ambiguous'
  },
  'cases':cases,
  'assertions':{
      'all_expected':all(c['pass'] for c in cases),
      'two_drive_holdout_not_rejected':cases[3]['verdict']=='COMPATIBLE',
      'three_drive_holdout_rejected':cases[4]['verdict']=='REJECTED',
      'boundary_abstains':cases[2]['verdict']=='AMBIGUOUS',
  },
  'nonclaim':'COMPATIBLE does not identify Pi/Phi or prove a universal two-drive mechanism.'
}
assert all(out['assertions'].values())
Path(__file__).with_name('c5_dual_drive_benchmark.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
