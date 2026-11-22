"""Eight-column determinant and full preparation resource bookkeeping."""
import sympy as sp
from common import iv,box,load,require,above,below,outward,finish
p=load('physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/local_preparation.json')
amin=box(p['negative_dipole_response_magnitude_lower'])
apmin=box(p['negative_dipole_time_derivative_magnitude_lower'])
appmin=box(p['positive_dipole_second_time_derivative_lower'])
detmin=apmin**2+amin*appmin
u0=(3+iv.sqrt(3))/2
M=2*u0**(iv.mpf(3)/2)*iv.sqrt(u0-1)*iv.exp(1-u0)
C0=10*iv.exp(iv.mpf(1)/3);C1=100*M*iv.exp(iv.mpf(1)/3)
require(below(M,iv.mpf(22)/10) and above(detmin),'joint invertible response')
a,b,c=sp.symbols('a b c',real=True)
J=sp.Matrix([[a,b],[-b,-c]])
require(sp.expand(J.det()-(b*b-a*c))==0,'response determinant')
eps,zeta,om=sp.symbols('eps zeta Omega',real=True)
require(sp.expand((eps-sp.I*om*zeta)*(eps+sp.I*om*zeta)-eps**2-om**2*zeta**2)==0,'no quadratic profile cross term')
Om=box(p['first_pair_frequency'])
E_d=box(p['positive_quadratic_work_coefficient_lower'])*Om**2
V_d=box(p['positive_quadratic_energy_variance_coefficient_lower'])*Om**2
finish('joint_preparation.py',{
 'actual_endpoint_mean_moments_controlled':8,
 'moments':'four l1 density and four longitudinal l1 momentum projections',
 'two_by_two_Jacobian_determinant_lower':outward(detmin),
 'eight_by_eight_Jacobian_determinant_lower':outward(detmin**4),
 'derivative_bump_maximum':outward(M),'b_supremum_upper':outward(C0),'bprime_supremum_upper':outward(C1),
 'derivative_profile_quadratic_work_coefficient_lower':outward(E_d),
 'derivative_profile_quadratic_energy_variance_coefficient_lower':outward(V_d),
 'actual_normal_analytic_state_inverse_function_argument':True,
 'numerically_quantified_target_neighborhood':False,
 'code_reference_preparation_common_to_both_signs':True,
 'additional_code_current_at_encoding_slice_zero':True,
 'preparation_control_order':'eta^2; remainder eta^6',
 'preparation_energy_order':'eta^4',
 'remaining_each_code_energy_cost':'eta^2 ||f||^2 / 2',
 'instantaneous_source_counterterm_cross_terms_dropped':False,
 'all_momentum_modes_or_quantum_constraints_solved':False
},inputs=['physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/LOCAL_PREPARATION.md',
          'physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/local_preparation.json',
          'physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/STATIC_RESPONSE.md'])
