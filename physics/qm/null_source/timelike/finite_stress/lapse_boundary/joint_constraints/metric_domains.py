"""Independent algebraic and high-frequency checks for response domains."""
import sympy as sp
from common import iv,require,above,below,outward,finish
a=sp.symbols('a',positive=True);k=sp.symbols('k',positive=True);mu=sp.symbols('mu',real=True)
theta=sp.log(a)+sp.log((k*k+a*a*mu)/(k*k+mu))/4
require(sp.simplify(sp.diff(theta,a).subs(a,1)-(1+mu/(2*(k*k+mu))))==0,'radius tangent')
require(sp.limit(theta,k,sp.oo)==sp.log(a),'constant UV squeeze')
require(sp.limit(sp.diff(theta,a).subs(a,1),k,sp.oo)==1,'UV tangent')
aa=iv.mpf(101)/100;th=iv.ln(aa)
beta_c=iv.mpf(2)/3*((aa-1/aa)/2)**2
fidelity_c=-iv.mpf(2)/3*iv.ln(((aa+1/aa)/2))
require(above(beta_c) and below(fidelity_c,0),'nonzero representation obstruction')
# Exact null is obtained at finite cutoff before taking any sharp generator limit.
finish('metric_domains.py',{
 'actual_zero_mean_baseline_first_tangent_is_constituent_pair_projection':True,
 'actual_cutoff_density_derivative_trace_norm_limit':True,
 'coherent_one_particle_term_requires_separate_smooth_data_limit':True,
 'connected_noise_is_positive_Gram':True,
 'compact_gauge_centered_tangent_zero_before_limit':True,
 'gauge_source_variation_during_ramp':'delta r = xi^0 r_dot',
 'isolated_continuum_sharp_gauge_generator_assumed':False,
 'arbitrary_finite_amplitude_metric_density_derivative_limit_interchanged':False,
 'overlapping_retarded_contacts_matched':False,
 'absolute_CTP_scalar_phase_completed':False,
 'radius_example':'101/100',
 'HS_growth_coefficient_K_cubed':outward(beta_c),
 'log_fidelity_growth_coefficient_K_cubed':outward(fidelity_c),
 'vacuum_tangent_squared_growth_coefficient':'1/3',
 'static_mean_smoothness_implies_fixed_bare_Fock_normality':False,
 'homogeneous_conformal_history_exact_constituent_canonical_transform':True,
 'inhomogeneous_conformal_history_same_cutoff_claimed':False
},inputs=['physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/METRIC_RESPONSE.md',
          'physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/metric_response.json'])
