"""Strict actual-history sign and concrete finite-amplitude residual."""
import sympy as sp
from common import iv,box,load,require,above,below,outward,finish
r=iv.mpf(1)/5;kappa=1-r;delta=iv.mpf(1)/100;eps=iv.mpf(1)/10**8
w0=iv.sqrt(1+r);w1=iv.sqrt(4+r);d=-r/(2+r+w0*w1);W=1/(16*w0*w1)
first_M1=(w0+w1)*d*d*W
M1lower=iv.mpf(4)/23763;M2upper=iv.mpf(9)/1024
require(above(first_M1,M1lower.b),'first pair strict moment lower')
I_lower=iv.exp(-iv.mpf(1)/2)/3
require(above(I_lower,iv.mpf(1)/5),'normalized lapse bump')
chi_mag=delta*(2*M1lower-2*delta*M2upper)
require(above(chi_mag,iv.mpf('1.6e-6')),'all-lag negative response')
K=16;tail=2*r*r/(192*kappa**3*K**3)
require(above(chi_mag-tail,iv.mpf('1.35e-6')),'actual K16 first tangent sign')
signal_mag=eps*chi_mag-eps*eps
require(above(signal_mag,iv.mpf('1.59e-14')),'nonlinear signal with unrounded interval margin')
ground=load('physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/ground_datum.json')
residual=16*iv.pi*box(ground['G_N_model_units'])*signal_mag
require(above(residual),'rejected endpoint scalar constraint')
require(sp.Rational(5,6144)<sp.Rational(3,100)**2,'pair HS norm')
require(sp.Rational(18,1024)<sp.Rational(133,1000)**2,'energy-weighted pair norm')
finish('lapse_history.py',{
 'incoming_state':'same AP ground; no instantaneous resets',
 'smooth_lapse_pulse_support':'[-1/100,0]','terminal_time':'1/100',
 'allowed_finite_amplitude':'|epsilon| <= 1e-4','chosen_amplitude':'1e-8',
 'lapse_lower_for_allowed_amplitudes':'0.95',
 'first_spectral_moment_lower':outward(M1lower),
 'second_spectral_moment_upper':outward(M2upper),
 'strict_linear_response_magnitude_lower':outward(chi_mag),
 'actual_K16_response_tail_upper':outward(tail),
 'finite_amplitude_terminal_negative_dipole_magnitude_lower':outward(signal_mag),
 'mean_scalar_constraint_dipole_residual_lower':outward(residual),
 'actual_full_field_endpoint_normal_density_limit':True,
 'limiting_endpoint_Hadamard_all_final_energy_moments':True,
 'all_order_cutoff_energy_graph_convergence_for_metric_pulse':False,
 'fixed_static_natural_ground_range_theorem_applies_to_this_history':False,
 'this_metric_pulse_is_a_mean_Einstein_solution':False,
 'normal_ordering_phase_equals_covariant_metric_CTP_phase':False,
 'SI_calibration':False
},inputs=['physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/SHARP_CHARGES.md',
          'physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/ground_datum.json'])
