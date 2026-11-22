"""Outward initial-constraint and exact clock-only FRW comparison bounds."""
import sympy as sp
from common import iv,box,load,require,above,below,outward,finish
p='physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/'
d=load(p+'ground_datum.json')
G=box(d['G_N_model_units']);Lam=box(d['Lambda_model_units'])
g=iv.mpf(1)/10**40;V=2*iv.pi**2
energy=V/(2*g*g);rho=1/(2*g*g)
require(above(energy,iv.mpf('9.5e80')),'state-independent kinetic boost difference')
rhs=8*iv.pi*G/(g*g)-16*iv.pi*G*10**8
require(above(rhs,iv.mpf('2.1e84')),'conditional initial-constraint obstruction')
variance=V/(16*g*g)
require(above(variance,iv.mpf('1.18e80')),'complete retained energy variance lower')
C=4*iv.pi*G/(3*g*g);H=iv.sqrt(C);Hinv=1/H
A=(3*C/Lam)**(iv.mpf(1)/6)
require(below(A**4,C.a/2) and above(A**2,(6/Lam).b),'clock-only expanding comparison hypotheses')
advance=iv.sqrt(2)/iv.sqrt(C)*(iv.log(A)+iv.mpf(1)/3)
require(below(advance,iv.mpf('1e-39')) and below(advance,iv.mpf('.8')),'future clock cannot reach compact gate in comparison')
eps=iv.mpf(1)/100
require(above(C,2*(1+eps)**6),'near-unit-radius window hypothesis')
window=iv.sqrt(2)*eps*(1+eps)**3/iv.sqrt(C)
kk=sp.symbols('kk')
require(3**2*kk**2-3*kk**2==6*kk**2,'isotropic extrinsic curvature contraction')
finish('backreaction_gate.py',{
 'g':'1e-40','clock_boost_energy_increment':outward(energy),
 'clock_boost_density_and_pressure_increment':outward(rho),
 'complete_total_energy_variance_lower':outward(variance),
 'variance_lower_preserved_by_parity_code_and_all_outcome_reader':True,
 'same_variance_lower_claimed_for_every_conditional_outcome':False,
 'conditional_constraint_rhs_B_1e8_delta_v_0':outward(rhs),
 'initial_isotropic_H_magnitude_required':outward(H),
 'inverse_H_model_time':outward(Hinv),
 'clock_only_FRW_C':outward(C),'clock_only_FRW_transition_radius':outward(A),
 'clock_only_FRW_future_clock_coordinate_advance_upper':outward(advance),
 'clock_only_FRW_one_percent_radius_window_upper':outward(window),
 'same_subtraction_boost_difference':True,
 'new_field_reference_stress_assumed_zero':False,
 'old_AP_state_silently_kept_at_nonzero_extrinsic_curvature':False,
 'massless_conformal_old_chart_beta':'-i H/(2k); non-HS with k^2 degeneracy',
 'conditional_B_bound_inferred_from_trace_norm':False,
 'pure_Lambda_shift_cancels_clock_enthalpy':False,
 'full_five_field_quantum_geometry_evolution_solved':False,
 'FRW_comparison_is_actual_actuator_solution':False,
 'all_apparatus_designs_excluded':False,'SI_time_calibration':False
},inputs=[p+'GROUND_DATUM.md',p+'ground_datum.json',p+'CLOCK_ACTUATOR.md'])
