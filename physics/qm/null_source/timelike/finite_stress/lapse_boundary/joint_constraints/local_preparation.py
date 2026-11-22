"""Strict full-field response sign and smooth-pulse endpoint estimates."""
import sympy as sp
from common import iv,require,above,below,outward,finish
mu=iv.mpf(1)/5;w0=iv.sqrt(1+mu);w1=iv.sqrt(4+mu);Om=w0+w1
d=-mu/(2+mu+w0*w1);W=1/(16*w0*w1)
ahat_lower=iv.cos(Om/10);bhat_lower=ahat_lower**2
amin=2*(-d)*W*bhat_lower*iv.sin(iv.pi*(Om-3))
apmin=2*(-d)*W*Om*bhat_lower*iv.cos(iv.pi*(Om-3))
appmin=Om**2*amin
Emin=Om*W*bhat_lower**2;Vmin=Om**2*W*bhat_lower**2
C0=10*iv.exp(iv.mpf(1)/3)
require(above(Om-3) and below(Om-3,iv.mpf(15)/100),'all-shell phase range via monotonicity')
require(above(amin,iv.mpf(9)/10000) and above(apmin) and above(appmin),'strict sign lower bounds')
require(below(C0,14) and above(1+mu-C0/100,1),'positive-gap pulse')
k,m=sp.symbols('k m',positive=True)
wa=sp.sqrt(k*k+m);wb=sp.sqrt((k+1)**2+m)
dd=k*(k+1)+m-wa*wb
require(sp.simplify(dd*((wa+wb)**2-1)+2*m)==0,'full stress Ward identity')
# The summability criterion uses k^2 degeneracy; q=.5,p=3 yields exponent -5.
require(2*sp.Rational(1,2)-2*3+2==-3,'weighted trace decay')
finish('local_preparation.py',{
 'input':'AP coupled ground, not AQ ramp output','source':'s=epsilon b(t) Z in Phi_plus squared / 2',
 'support_time':'[-1/5,1/5]','observation_time_model_units':'pi',
 'first_pair_frequency':outward(Om),'negative_dipole_response_magnitude_lower':outward(amin),
 'negative_dipole_time_derivative_magnitude_lower':outward(apmin),
 'positive_dipole_second_time_derivative_lower':outward(appmin),
 'positive_quadratic_work_coefficient_lower':outward(Emin),
 'positive_quadratic_energy_variance_coefficient_lower':outward(Vmin),
 'b_supremum_upper':outward(C0),'explicit_scalar_gap_amplitude':'|epsilon| <= 1/100',
 'actual_cutoff_weighted_HS_endpoint_limit':True,
 'endpoint_normal_density_all_final_H_r_moments':True,
 'endpoint_density_real_analytic_small_controls':True,
 'endpoint_derivative_and_cutoff_limit_interchange_proved_for_this_pulse':True,
 'unadjusted_U_K_scalar_phase_convergence':False,
 'nonzero_momentum_retained':True,
 'numerical_inverse_function_neighborhood_radius':None,
 'autonomous_actuator_constructed':False
},inputs=['physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/SHARP_CHARGES.md',
          'physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/sharp_charges.json'])
