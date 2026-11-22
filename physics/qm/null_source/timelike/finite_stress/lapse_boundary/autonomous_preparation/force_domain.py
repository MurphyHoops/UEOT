"""Sharp-force lower bound and a distinct finite-energy non-Hadamard example."""
import sympy as s
from common import finish,require,iv,outward,above,below,load
O='physics/qm/null_source/timelike/finite_stress/lapse_boundary/conformal_action/'
load(O+'quantum_controller.json');load(O+'autonomous_record.json')
k,r,rd=s.symbols('k r rd',positive=True)
pair=sum(2*k*k*(rd/(4*(k*k+sgn*r)))**2*(k*k+sgn*r) for sgn in [-1,1])
require(s.factor(pair-rd*rd*k**4/(4*(k**4-r*r)))==0,'two-sign pair variance')
x=s.symbols('x',positive=True)
u2=630*x**4*(1-x)**4
rp2=s.Rational(1,25)*s.exp(8-2/(x*(1-x)))*(1-2*x)**2/(x**4*(1-x)**4)
require(s.simplify(u2*rp2-s.Rational(126,5)*s.exp(8-2/(x*(1-x)))*(1-2*x)**2)==0,'packet cancellation')
force_coeff=21/(625*iv.e)
require(above(force_coeff,'.0123'),'strict sharp-force growth')
z2=iv.pi**2/6;z4=iv.pi**4/90;z8=iv.pi**8/9450
gamma=iv.mpf('.01');z3_upper=iv.mpf(5)/4
graph_upper=gamma**2*(2*z2+2*z3_upper+z4/2)+gamma**4*(2*z8+z3_upper**2)
require(below(graph_upper,'.000634'),'explicit graph-nearby example')
finish('force_domain.py',{
 'sharp_force_lower_bound_exact':'21*(K-1)/(625*e)',
 'sharp_force_growth_coefficient_interval':outward(force_coeff),
 'joint_scalar_counterterm_cancels_high_pair_sector':False,
 'finite_total_second_moment_does_not_imply_sharp_force_second_moment':True,
 'sharp_force_divergence_used_as_non_Hadamard_diagnosis':False,
 'separate_free_counterexample_beta':'gamma*k^(-3)',
 'free_H_mean':'gamma^2*zeta(3)',
 'free_H_variance':'2*gamma^2*zeta(2)+2*gamma^4*zeta(8)',
 'free_covariance_difference_leading_eigenvalue':'-gamma*k^(-4)',
 'normal_and_in_D_H_but_non_Hadamard':True,
 'Hadamard_finite_mode_sequence_converges_in_D_H_graph_norm':True,
 'example_gamma':'.01','example_graph_distance_squared_upper_interval':outward(graph_upper),
 'actual_AB_outside_field_input_declared_non_Hadamard':False,
 'operator_valued_Hadamard_stress_propagation_proved':False
},inputs=[O+'QUANTUM_CONTROLLER.md',O+'quantum_controller.json',O+'AUTONOMOUS_RECORD.md',O+'autonomous_record.json'])
