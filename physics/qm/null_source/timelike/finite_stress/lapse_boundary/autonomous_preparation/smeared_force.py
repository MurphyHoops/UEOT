"""Time-smearing domains and resource inequalities; analytic operator proof is AH."""
import sympy as s
from common import finish,require,iv,outward,below,box,load
P='physics/qm/null_source/timelike/finite_stress/lapse_boundary/autonomous_preparation/'
O='physics/qm/null_source/timelike/finite_stress/lapse_boundary/conformal_action/'
z=load(O+'quantum_controller.json');load(P+'resource_budget.json');load(P+'force_domain.json')
M=iv.mpf(1);gp=iv.mpf('.4');omega=17*iv.sqrt(2);v=iv.mpf(1)/4
E1=iv.mpf(58);E2=iv.mpf(4654);mu1=iv.sqrt(2*v/iv.pi)
a=iv.sqrt(E2);b=omega*iv.sqrt(E1);c=omega**2/4
Eout=E1+omega*iv.sqrt(E1)*mu1+omega**2*v/4
E2out=a*a+2*a*b*mu1+(b*b+2*a*c)*v+4*b*c*v*mu1+3*c*c*v*v
force2=2*M*gp*gp*(56+box(z['vacuum_potential_absolute_bound']))
require(below(force2,'17.921'),'compact force second moment')
require(below(Eout,170) and below(E2out,50000),'finite retained energy resources')
aa,bb,cc,t=s.symbols('a b c t')
require(s.expand((aa+bb*t+cc*t*t)**2-(aa*aa+2*aa*bb*t+(bb*bb+2*aa*cc)*t*t+2*bb*cc*t**3+cc*cc*t**4))==0,'second-moment polynomial')
require(4426+4*56+4==4654,'shifted second spectral moment')
finish('smeared_force.py',{
 'definition':'F(g)=-integral g_prime(t) U(t)^dagger p_x U(t) dt on Q(H)',
 'self_adjoint_closure_on_D_H_proved_analytically':True,
 'domain_contains_Q_H':True,
 'actual_FK_strong_resolvent_limit_proved_analytically':True,
 'actual_all_outcome_normal_instrument_limit_proved_analytically':True,
 'sharp_force_strong_action_on_entire_Q_H_claimed':False,
 'comparison_operator':'N=H+2',
 'commutator_sign':'i[F(g),N]=F(g_prime)',
 'energy_regularization':'N_epsilon=N/(1+epsilon*N)',
 'polynomial_first_and_second_energy_moment_bounds_proved':True,
 'example_M':'1','example_test':'r(-3/2+5*t)',
 'test_support':['.3','.5'],'test_replaces_quantum_controller':False,
 'L1_g_prime_exact':'.4','L1_g_second_upper':'17','reader_sigma':'1',
 'force_second_moment_upper_interval':outward(force2),
 'readout_second_moment_upper_interval':outward(force2+1),
 'initial_N_mean':'58','initial_N_second_moment':'4654',
 'post_reader_N_mean_upper_interval':outward(Eout),
 'post_reader_N_second_moment_upper_interval':outward(E2out),
 'two_sign_codes_have_identical_force_spectral_law':True,
 'force_sign_discrimination_claimed':False,
 'reader_own_energy_or_local_autonomous_implementation_constructed':False,
 'full_four_dimensional_stress_and_noise_constructed':False
},inputs=[P+'FORCE_DOMAIN.md',P+'force_domain.json',P+'RESOURCE_BUDGET.md',P+'resource_budget.json',O+'QUANTUM_CONTROLLER.md',O+'quantum_controller.json'])
