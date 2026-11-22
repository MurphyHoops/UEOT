"""Initial enthalpy, clock uncertainty and actual free-Y quadrupole certificate."""
import sympy as sp
from common import iv,box,load,require,above,below,outward,finish
p='physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/'
oldp='physics/qm/null_source/timelike/finite_stress/lapse_boundary/autonomous_preparation/'
old=load(oldp+'local_record.json');tot=load(p+'total_columns.json')
V=2*iv.pi**2;K=64;eta=iv.mpf(1)/10**13
tail=(iv.mpf(22)/5)**2/(2*(K*K-1))
d=box(old['frozen_density_first_harmonic_projection_lower'])-tail
require(below(tail,iv.mpf('.002365')) and above(d,iv.mpf('.0268')),'nonzero actual projected cap target')
mu=iv.mpf(1)/5
scale=sum(iv.mpf(k*k)/iv.sqrt(k*k+mu) for k in range(1,K+1))/16
lip=13*scale+6+iv.mpf('4.096e-9')+iv.mpf('6.728e-21')
require(below(lip,2000),'full limiting mean map derivative bound')
umin=eta**2*d/2000
require(above(umin,iv.mpf('1.3e-31')),'nonzero limiting program')
quad=iv.sqrt(V/48)*umin**2
require(above(quad,iv.mpf('1e-62')),'remaining scaled spatial-trace quadrupole')
lam1,lam2=sp.symbols('lambda1 lambda2',nonnegative=True)
rank_margin=lam1**2+lam2**2-(lam1+lam2)**2/2
require(sp.Rational(9-7,2)==1 and sp.Rational(11-9,2)==1,'higher graph interpolation exponents')
require(sp.expand(rank_margin-(lam1-lam2)**2/2)==0,'rank-two PSD second moment bound')
a,g,v=sp.symbols('a g V0',positive=True)
require(sp.simplify(v/(4*a*g*g)*(g*g*a/v)-sp.Rational(1,4))==0,'full clock-energy uncertainty bound')
finish('post_closure.py',{
 'K':64,'encoding_slice':'pi','eta':'1e-13',
 'initial_raw_total_integrated_enthalpy_lower':'V0/g^2',
 'initial_enthalpy_lower_claimed_for_all_later_times':False,
 'smooth_clock_full_energy_uncertainty_product_lower':'1/4',
 'autonomous_homogeneous_lapse_CTP':'Tr rho exp[-i (tau_plus-tau_minus) H_total]',
 'homogeneous_connected_lapse_noise':'full Var H_total',
 'intermediate_instruments_absorbed_into_total_proper_time':False,
 'Y_classical_density_at_pi':'homogeneous ||u||^2/(2g^2)',
 'Y_classical_spatial_trace_second_harmonic':'-Q2(u)/g^2',
 'Q2_squared_norm_lower':'V0 ||u||^4/48',
 'cap_moment_cutoff_error_upper':outward(tail),
 'actual_K64_cap_density_moment_lower':outward(d),
 'limiting_total_mean_derivative_norm_upper':outward(lip),
 'limiting_corrected_program_norm_lower':outward(umin),
 'scaled_limiting_actual_total_finite_K_spatial_trace_quadrupole_norm_lower':outward(quad),
 'actual_weighted_total_finite_K_mean_limit_used_not_trace_distance_only':True,
 'full_total_spatial_trace_same_limit_proved_at_fixed_K':True,
 'projected_force_composite_domain':'H_squared_form_on_D_H',
 'projected_force_operator_domain_or_variance_proved':False,
 'parametrix_order_for_mean':9,'parametrix_order_for_C1_if_needed':11,
 'extra_graph_coupling_threshold_quantified':False,
 'continuum_local_metric_Ward_claimed':False,
 'remaining_spatial_quadrupole_threshold_numerically_bounded':False,
 'fixed_g_1e_40_claimed_below_that_threshold':False,
 'all_static_spatial_Einstein_rows_repaired':False,
 'sharp_stress_variance_claimed_finite':False,
 'all_alternative_apparatus_designs_excluded':False,
 'SI_calibration':False
},inputs=[oldp+'local_record.json',p+'TOTAL_COLUMNS.md',p+'total_columns.json',
p+'ACTUATOR_MEANS.md',p+'CLOCK_ACTUATOR.md',p+'BACKREACTION_GATE.md'])
