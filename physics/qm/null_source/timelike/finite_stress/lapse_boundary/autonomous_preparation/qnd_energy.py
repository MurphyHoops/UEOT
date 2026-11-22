"""Exact clock energy-QND instrument, moment calibration and state change."""
import sympy as s
from common import finish,require,iv,outward,above,below,load
P='physics/qm/null_source/timelike/finite_stress/lapse_boundary/autonomous_preparation/'
O='physics/qm/null_source/timelike/finite_stress/lapse_boundary/conformal_action/'
ae=load(P+'energy_accounting.json');load(O+'quantum_controller.json')
# H2 outside-envelope moments already proved in AB. Use exact rationals.
p=s.Integer(10);M=s.Integer(1);u1=s.Integer(12);u2=s.Integer(504)
mu_kin=(p*p+u1)/(2*M)
var_kin=(4*p*p*u1+u2-u1*u1)/(4*M*M)
require(mu_kin==56 and var_kin==1290,'original outside packet moments')
center=s.Rational(113,2);m2=var_kin+(mu_kin-center)**2
require(m2==s.Rational(5161,4),'both centered second moments')
R=m2
x=s.symbols('x',real=True)
require(s.expand(x*x/4-(x-1)-(x-2)**2/4)==0,'sharp scalar clipping remainder')
gap=s.Rational(1,2)/R-m2/(4*R*R)
require(gap==s.Rational(1,5161),'exact calibrated energy probability gap')
ER=6+45*iv.pi**2/22;VR=90-6*iv.pi**2/11+577*iv.pi**4/1573
D=iv.pi/(2*iv.sqrt(5161))
require(below(D,'.022'),'nonselective full Z-state disturbance upper bound')
lo=center-R;hi=center+R
require(lo==s.Rational(-4935,4) and hi==s.Rational(5387,4),'plateau thresholds')
require(lo<-1 and 57<hi,'strict-change spectral-support exclusions')
finish('qnd_energy.py',{
 'target':'entire original M=1 Z generator H, not H_source and not the added-clock H_Q',
 'fixed_original_Z_input':{'M':'1','controller_support':['-2','-1'],'controller_phase_momentum':'10','source_codes':['vacuum','one k1 quantum']},
 'Z_energy_means_exact':['56','57'],'Z_energy_variances_exact':['1290','1290'],
 'center_exact':'113/2','centered_second_moment_exact':'5161/4',
 'response_R_exact':'5161/4','response':'w(E)=[1+clip((E-113/2)/R,-1,1)]/2',
 'record_gap_lower_bound_exact':'1/5161',
 'record_gap_lower_bound_interval':outward(iv.mpf(1)/5161),
 'theta_continuous_bounded':True,'theta_smooth_claimed':False,
 'actual_cutoff_G_defined_as_theta_HK':True,
 'endpoint_T':'1/2','clock_m':'1','clock_Omega':'2*pi',
 'complete_HQ_energy_mean_intervals':[outward(56+ER),outward(57+ER)],
 'complete_HQ_energy_variance_interval':outward(1290+VR),
 'complete_HQ_energy_means_exact':['62+45*pi^2/22','63+45*pi^2/22'],
 'complete_HQ_energy_variance_exact':'1380-6*pi^2/11+577*pi^4/1573',
 'nonselective_entire_Z_energy_law_preserved':True,
 'target_energy_register_covariance_strictly_positive_proved_analytically':True,
 'optimal_affine_inference_MSE_strictly_between':'0 and 1290',
 'nonselective_physical_Z_energy_variance':'1290 unchanged',
 'numerical_covariance_or_regression_residual_computed':False,
 'nonselective_entire_HQ_energy_law_preserved_for_endpoint_preparation':True,
 'post_instrument_complete_energy_register_covariance_positive':True,
 'post_instrument_complete_energy_inference_MSE_strict_lower_floor_interval':outward(VR),
 'pre_PVM_joint_spectral_measure_of_HQ_and_bare_bit_claimed':False,
 'universal_response_w_HQ_claimed':False,
 'global_Z_state_change_strictly_positive_for_two_pure_codes':True,
 'global_Z_half_trace_distance_from_unread_upper_bound_interval':outward(D),
 'numerical_positive_state_change_lower_bound_computed':False,
 'source_only_marginal_strict_change_claimed':False,
 'unread_unitary_register_uncomputes_at_T':'1',
 'old_M1_physical_P_collision_closed':False,
 'geometric_constraint_charge_identified':False,
 'local_covariant_action_and_total_stress_constructed':False
},inputs=[P+'COLLISION.md',P+'collision.json',P+'ENERGY_ACCOUNTING.md',P+'energy_accounting.json',O+'QUANTUM_CONTROLLER.md',O+'quantum_controller.json'])
