"""Focused physical verification and declared negative controls for the source."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import platform
import resource
import time

import numpy as np
import scipy

import dynamics as d


def norm_trace(a):
    return float(np.abs(np.linalg.eigvalsh((a + a.conj().T) / 2)).sum())


def run():
    started = time.perf_counter()
    convergence, physical, controls = [], [], []
    for lam in (0.2, 0.3, 0.4):
        exact_started = time.perf_counter()
        exact = d.exact_output(lam)
        exact_seconds = time.perf_counter() - exact_started
        choi_sum = sum(exact.values())
        marginal = np.trace(choi_sum.reshape(2, 2, 2, 2), axis1=0, axis2=2)
        min_eigenvalue = min(np.linalg.eigvalsh(x).min() for x in exact.values())
        tp_residual = np.linalg.norm(marginal - np.eye(2) / 2)
        assert min_eigenvalue > -1e-12 and tp_residual < 1e-12
        effect = d.acceptance_effect(lam)
        effect_eigenvalues = np.linalg.eigvalsh(effect)
        assert effect_eigenvalues[0] >= 27/64 - 1e-12
        assert effect_eigenvalues[1] <= 343/512 + 1e-12
        # Prefix non-signalling uses the same second post-pass rotation.
        prefix = d.exact_output(lam, times=d.DEFAULT_TIMES[:2],
                                rotations=[d.rotation('y', np.pi/2), d.rotation('x', np.pi/3)])
        future = exact['ppf'] + exact['ppp']
        prefix_marginal = np.trace(prefix['pp'].reshape(2, 2, 2, 2), axis1=0, axis2=2)
        future_marginal = np.trace(future.reshape(2, 2, 2, 2), axis1=0, axis2=2)
        prefix_residual = np.linalg.norm(prefix_marginal - future_marginal)
        assert prefix_residual < 1e-12
        physical.append({
            'lambda': lam, 'total_trace': float(np.trace(choi_sum).real),
            'minimum_choi_eigenvalue': float(min_eigenvalue),
            'normalized_choi_trace_preservation_residual': float(tp_residual),
            'prefix_causality_residual': float(prefix_residual),
            'terminal_probabilities': {k: float(np.trace(v).real) for k,v in exact.items()},
            'acceptance_effect_eigenvalues': effect_eigenvalues.tolist(),
            'acceptance_non_scalar_eigenvalue_gap': float(np.ptp(effect_eigenvalues)),
            'first_pass_conditional_bath_fourth_cumulant': d.conditional_bath_fourth_cumulant(lam),
        })
        for k in (0, 2, 4, 6, 8, 12, 20):
            tick = time.perf_counter()
            finite = d.galerkin_output(lam, cutoff=k)
            seconds = time.perf_counter() - tick
            distance = d.cq_distance(exact, finite)
            bound = d.truncation_bound(k)
            assert distance <= bound + 1e-12
            convergence.append({
                'lambda': lam, 'cutoff': k, 'bath_dimension': (k+1)**2,
                'executed_SR_dimension': 4, 'full_CQ_Bell_distance': distance,
                'all_input_analytic_truncation_bound_display': bound,
                'standard_joint_Galerkin_seconds': seconds,
                'exact_Weyl_seconds': exact_seconds,
                'floating_diagnostic_only': True,
            })
        one_slot = d.exact_output(lam, times=[d.DEFAULT_TIMES[0]], rotations=[d.I2])
        one_slot_reset = d.reset_bath_output(lam, times=[d.DEFAULT_TIMES[0]], rotations=[d.I2])
        one_distance = d.cq_distance(one_slot, one_slot_reset)
        multitime_distance = d.cq_distance(exact, d.reset_bath_output(lam))
        no_phase_distance = d.cq_distance(exact, d.exact_output(lam, omit_history_phase=True))
        assert one_distance < 1e-12 and multitime_distance > 0.04 and no_phase_distance > 0.02
        controls.append({'lambda':lam, 'same_single_slot_reset_distance':one_distance,
                         'persistent_vs_reset_full_CQ_distance':multitime_distance,
                         'omitted_history_phase_distance':no_phase_distance})
    # An arbitrary non-Bell input with a three-dimensional reference checks ordering.
    rng = np.random.default_rng(71114)
    v = rng.normal(size=6) + 1j * rng.normal(size=6)
    v /= np.linalg.norm(v)
    rho = np.outer(v, v.conj())
    stored = d.exact_output(.3)
    contracted = d.apply_stored_choi(stored, rho)
    direct = d.exact_output(.3, rho_sr=rho)
    finite = d.galerkin_output(.3, rho_sr=rho, cutoff=12)
    choi_contract_distance = d.cq_distance(contracted, direct)
    arbitrary_reference_distance = d.cq_distance(direct, finite)
    assert choi_contract_distance < 1e-12 and arbitrary_reference_distance < 1e-12
    # Exact toy control: rare accepted terminal states can be maximally different.
    p = 1e-6
    rho0, rho1 = np.diag([1.,0.]), np.diag([0.,1.])
    toy_a = {'accept':p*rho0, 'fail':(1-p)*rho0}
    toy_b = {'accept':p*rho1, 'fail':(1-p)*rho0}
    rare_full = d.cq_distance(toy_a, toy_b)
    rare_conditional = norm_trace(rho0-rho1)/2
    assert abs(rare_full-p) < 1e-18 and rare_conditional == 1
    # Explicit leakage extension is outside the frozen qubit model.
    leakage_state = np.diag([.95, 0, .05])
    omitted_leakage_mass = 1-float(np.trace(leakage_state[:2,:2]))
    # The certificate refuses an effective-model parameter domain violation.
    rejected = False
    try:
        d.parameter_error_bound(.5, .3)
    except ValueError:
        rejected = True
    assert rejected
    report = {
        'schema':'ueot.persistent_bath.dynamics_execution.v1',
        'status':'FOCUSED_SCIENTIFIC_CHECKS_PASSED_FLOATING_RESULTS_SEPARATE_FROM_ANALYTIC_BOUNDS',
        'frozen_source':'three-slot two-mode vacuum source in model_contract.json',
        'physical_checks':physical,
        'convergence':convergence,
        'negative_controls':{
            'same_single_slot_different_multitime':controls,
            'initial_tail_zero_does_not_bound_propagation':{
                'initial_vacuum_tail_above_K0':0,
                'K0_lambda_0_4_actual_full_CQ_error':next(x['full_CQ_Bell_distance'] for x in convergence if x['lambda']==.4 and x['cutoff']==0)},
            'rare_acceptance_declared_toy':{'acceptance_probability':p,'full_distance':rare_full,'conditional_distance':rare_conditional},
            'leakage_declared_qutrit_extension':{'omitted_mass':omitted_leakage_mass,'outside_frozen_qubit_domain':True},
            'parameter_domain_violation_rejected':rejected,
        },
        'reference_and_choi_ordering':{'untouched_reference_dimension':3,
            'stored_choi_vs_direct_distance':choi_contract_distance,
            'exact_vs_K12_distance':arbitrary_reference_distance},
        'resource':{'wall_seconds':time.perf_counter()-started,
            'max_rss_platform_units':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            'platform':platform.platform(), 'python':platform.python_version(),
            'numpy':np.__version__,'scipy':scipy.__version__,
            'largest_joint_SR_environment_dimension':4*21**2,
            'largest_conditional_environment_unitary_dimension':21**2,
            'environment_reset_in_true_source':False},
        'method_comparison':'Exact Weyl and standard persistent joint evolution implement the same standard model; no UEOT predictive superiority claimed.',
        'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),Path(d.__file__)]},
        'not_claimed':['real device validation','new Lean proof','arbitrary Gaussian executed certificate',
                       'general memory compression advantage','thermalization','Core-derived complex structure']}
    return report


if __name__=='__main__':
    result=run()
    destination=Path(__file__).with_name('dynamics_results.json')
    destination.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'resource':result['resource'],
                     'negative_controls':result['negative_controls']},indent=2))
