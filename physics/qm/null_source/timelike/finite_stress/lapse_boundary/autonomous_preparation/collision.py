"""Outside preparation and full-field moving-frame collision certificate."""
import sympy as s
from common import finish,require,iv,outward,above,below,load
P='physics/qm/null_source/timelike/finite_stress/lapse_boundary/conformal_action/'
load(P+'quantum_controller.json')
z=s.symbols('z',real=True)
u=s.sqrt(630)*z**2*(1-z)**2
moments=[s.integrate(f,(z,0,1)) for f in (u**2,s.diff(u,z)**2,s.diff(u,z,2)**2,(z-s.Rational(1,2))**2*u**2)]
require(moments==[1,12,504,s.Rational(1,44)],'exact envelope moments')
for end in (0,1):
 require(u.subs(z,end)==s.diff(u,z).subs(z,end)==0,'H2 endpoint traces')
lam=s.Rational(1,2)
def poisson_power(n):
 return sum(s.functions.combinatorial.numbers.stirling(n,j,kind=2)*lam**j for j in range(n+1))
def shifted_power(n):
 return s.expand(sum(s.binomial(n,j)*2**(n-j)*poisson_power(j) for j in range(n+1)))
require(shifted_power(2)==s.Rational(27,4),'h2 Poisson moment')
require(shifted_power(4)==s.Rational(1025,16),'h4 Poisson moment')
L=iv.pi/(8*iv.sqrt(3)); q1=iv.exp(2*L)*iv.sqrt(27)/2; q2=iv.exp(6*L)*iv.sqrt(1025)/4
require(below(q1,5) and below(q2,40),'uniform finite-cutoff number moments')
a=iv.mpf(4)/5; R1=iv.mpf(16)/5; R2=iv.mpf(736)/5
c1=R1*iv.pi/(4*iv.sqrt(3)*a)
c2=(R2+R1**2/a)*iv.pi/(4*iv.sqrt(3)*a)
Le=5*R1*(iv.mpf(1)/5)**3*(iv.mpf(5)/4)/(32*a**(iv.mpf(7)/2))
require(below(c1,2) and below(c2,100),'coarse squeeze derivative bounds')
require(below(R1/(2*iv.sqrt(a)),2) and below(Le,1),'frequency and subtracted scalar force')
I=iv.mpf(1)/25
mlo=iv.exp(-iv.mpf(4)/3)*iv.cos(iv.mpf(1)/2)**2/50-(iv.exp(I)-1-I)
dcl=iv.exp(-iv.mpf(1)/200-iv.exp(2*I)/4)*iv.sin(mlo)
require(above(mlo) and above(dcl,'.0024'),'reference actual Dyson record bound')
M=iv.mpf(10)**16;delta=iv.mpf('1e-7')
eps=1310*delta+2640/(M*delta)+250/M
dactual=dcl-2*eps
require(below(eps,'.000134') and above(dactual,'.0021'),'outside actual positive record')
finish('collision.py',{
 'model_family':'Z fixed ESU full-field autonomous controller, c_r=0',
 'original_M1_p10_outside_example_closed':False,
 'new_fixed_parameter_example':{'M':'1e16','delta':'1e-7','v':'5','X0':'-3/2','T':'1/2'},
 'input':'outside product; source k1 coherent q=+/-1,p=0; all other field modes vacuum',
 'normal_CP_instrument_full_source_reference_scope':True,
 'approximation_bound_scope':'two declared coherent codes; not unconstrained diamond norm',
 'envelope_moments_exact':['1','12','504','1/44'],
 'reference_number_h2_exact':'27/4','reference_number_h4_exact':'1025/16',
 'reference_q1_bound_interval':outward(q1),'reference_q2_bound_interval':outward(q2),
 'reference_momentum_mean_lower_bound_interval':outward(mlo),
 'classical_binary_contrast_lower_bound_interval':outward(dcl),
 'coarse_total_vector_error_interval':outward(eps),
 'actual_binary_contrast_lower_bound_interval':outward(dactual),
 'finite_K_residual_and_endpoint_frame_retained':True,
 'actual_strong_propagator_limit_used':True,
 'same_complete_total_energy_law_for_both_codes':True,
 'source_sign_is_total_energy_or_geometry_charge':False,
 'Gaussian_reader_all_outcomes_retained':True,
 'reference_pulse_inserted_into_actual_H':False,
 'autonomous_terminal_reader_constructed_in_this_entry':False
},inputs=[P+'QUANTUM_CONTROLLER.md',P+'quantum_controller.json',P+'PROBE_PHASE.md'])
