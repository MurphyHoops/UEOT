"""Uniform vacuum-potential/squeeze bounds and a normal finite-energy input."""
import sympy as s
from common import finish,require,iv,outward,above,below
z=s.symbols('z',real=True)
h=(s.sqrt(1+z)+s.sqrt(1-z)-2)/2+z*z/8
for j in range(4):require(s.diff(h,z,j).subs(z,0)==0,'vacuum cancellation order '+str(j))
fourth=-s.Rational(15,32)*((1+z)**(-s.Rational(7,2))+(1-z)**(-s.Rational(7,2)))
require(s.simplify(s.diff(h,z,4)-fourth)==0,'exact fourth Taylor derivative')
require(s.Rational(15,16)/s.factorial(4)==s.Rational(5,128),'uniform Taylor coefficient')
rstar=iv.mpf('.2');c=5*rstar**4/(128*(1-rstar)**iv.mpf('3.5'))
# zeta(5) bounded independently by finite sum plus an integral tail.
cut=100
z5=sum((iv.mpf(1)/j**5 for j in range(1,cut+1)),iv.mpf(0))
z5upper=z5+iv.mpf(1)/(4*cut**4)
lower_energy=c*z5upper
require(below(lower_energy,iv.mpf('.001')),'explicit semibounded energy budget')
theta_l2=rstar**2*iv.pi**2/(48*(1-rstar)**2)
# For r(x)=.2*bump(x), |bump'|<=3*4^2=48.
rprime=48*rstar
theta_prime_l2=rprime**2*iv.pi**2/(48*(1-rstar)**2)
require(above(theta_prime_l2),'finite nonzero connection budget')
x=s.symbols('x',real=True)
density=2*s.sin(s.pi*(x+2))**2
norm=s.integrate(density,(x,-2,-1))
kin=s.integrate(2*(s.pi**2*s.cos(s.pi*(x+2))**2+100*s.sin(s.pi*(x+2))**2),(x,-2,-1))/2
require(norm==1 and s.simplify(kin-50-s.pi**2/2)==0,'actual normalized H1 controller preparation')
kk=s.symbols('k',positive=True);rr=s.symbols('r',real=True)
for sign in [-1,1]:
 theta=s.log(1+sign*rr/kk**2)/4
 require(s.simplify(s.diff(theta,rr)-sign/(4*(kk**2+sign*rr)))==0,'exact squeeze derivative')
# A distinct H2 preparation: exact normalization and the two spectral moments.
yy=s.symbols('yy',real=True)
env=s.sqrt(630)*yy**2*(1-yy)**2
require(s.integrate(env**2,(yy,0,1))==1,'H2 packet normalization')
for end in (0,1):
 require(env.subs(yy,end)==0 and s.diff(env,yy).subs(yy,end)==0,'zero value and derivative traces')
energy_gradient=s.integrate(s.diff(env,yy)**2,(yy,0,1))
energy_curvature=s.integrate(s.diff(env,yy,2)**2,(yy,0,1))
require(energy_gradient==12 and energy_curvature==504,'exact H2 envelope integrals')
hreal=50*env-s.diff(env,yy,2)/2
himag=-10*s.diff(env,yy)
mean=s.integrate(env*hreal,(yy,0,1))
second=s.integrate(hreal*hreal+himag*himag,(yy,0,1))
require(mean==56 and second==4426 and second-mean**2==1290,'finite exact total-energy variance')
# Noncommutative energy square: no H-p commutation assumption.
HH,pp=s.symbols('HH pp',commutative=False)
ll,vv=s.symbols('ll vv',real=True)
energy_square=s.expand((HH-ll*pp+ll**2/2)**2)
moments={0:s.Integer(1),1:s.Integer(0),2:vv,3:s.Integer(0),4:3*vv**2}
averaged=s.expand(sum(energy_square.coeff(ll,j)*moments[j] for j in range(5)))
require(s.expand(averaged-(HH**2+vv*(pp**2+HH)+3*vv**2/4))==0,'exact noncommuting Gaussian second-energy moment')
e1,e2,p2=s.symbols('e1 e2 p2',real=True)
require(s.expand(e2+vv*(p2+e1)+3*vv**2/4-(e1+vv/2)**2-(e2-e1**2+vv*p2+vv**2/2))==0,'variance cancellation')
sigma=iv.mpf('.1');vnoise=1/(4*sigma**2)
reader_mean=iv.mpf(56)+vnoise/2
reader_variance_lower=iv.mpf(1290)+vnoise**2/2
reader_variance_upper=reader_variance_lower+vnoise*2*(56+lower_energy+1)
require(below(reader_variance_upper,'4452.507076'),'uniform actual reader total variance bound')
finish('quantum_controller.py',{'model':'one global quantum control coordinate plus full source/probe Fock fields on fixed ESU',
 'controller_mass_example':1,
 'terminal_reader_width_example':'.1',
 'terminal_reader_energy_backaction_exact':'1/(8 sigma^2)',
 'terminal_reader_variance_increment_exact':'v_lambda <p_probe,1^2> + v_lambda^2/2',
 'terminal_reader_total_mean_energy_bounds':outward(reader_mean),
 'terminal_reader_total_variance_lower_bound':outward(reader_variance_lower)[0],
 'terminal_reader_total_variance_upper_bound':outward(reader_variance_upper)[1],
 'terminal_reader_own_energy_supply_constructed':False,'finite_c_r_example':0,'r_amplitude_bound':'.2',
 'vacuum_potential_absolute_bound':outward(lower_energy),
 'self_adjoint_H_lower_bound':-outward(lower_energy)[1],
 'uniform_theta_l2_squared_bound':outward(theta_l2),
 'uniform_theta_derivative_l2_squared_bound':outward(theta_prime_l2),
 'vacuum_potential_tail_K100_bound':outward(c/(4*cut**4)),
 'initial_controller_support':[-2,-1],'control_coupling_support':[0,1],
 'initial_momentum_modulation':10,
 'initial_total_form_energy_exact':'50+pi^2/2',
 'second_H2_preparation_mean_total_energy':int(mean),
 'second_H2_preparation_second_total_energy_spectral_moment':int(second),
 'second_H2_preparation_total_energy_variance':int(second-mean**2),
 'second_preparation_in_D_H':True,'second_preparation_in_D_H_squared_claimed':False,
 'initial_total_form_energy_bounds':outward(50+iv.pi**2/2),
 'moving_core_actual_canonical_cutoff_form_limit_proved_analytically':True,
 'autonomous_full_field_total_energy_conserved':True,
 'normalizable_ground_state_claimed':False,
 'prescribed_pulse_gain_inherited':False,
 'joint_state_stays_Gaussian_claimed':False,
 'consistent_truncation_of_full_local_control_field_proved':False,
 'full_four_dimensional_local_controller_and_terminal_reader':False},
 inputs=['physics/qm/null_source/timelike/finite_stress/lapse_boundary/conformal_action/PROBE_PHASE.md',
         'physics/qm/null_source/timelike/finite_stress/lapse_boundary/conformal_action/LOCAL_FIELD_PROBE.md'])
