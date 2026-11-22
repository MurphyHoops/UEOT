"""AQ: all-mode analytic ramp constants; no numerical mode evolution."""
from common import finish,require,iv,exact,outward,above,below,load,box
import sympy as s
r=exact(1)/5;kap=1-r;tau=iv.mpf(100)
Ilo=exact(3)/10*iv.exp(-exact(36)/91)
require(above(Ilo,exact(1)/5),"Bump integral lower bound")
L=exact(1)/16
C=(iv.exp(L)+iv.exp(-L))/2
S=(iv.exp(L)-iv.exp(-L))/2
cf=C/(4*kap**(exact(3)/2))+3*C/(80*kap**(exact(5)/2))+S/(160*kap**(exact(5)/2))
cm=3*C/(8*kap**(exact(3)/2))+3*C/(80*kap**(exact(5)/2))+S/(160*kap**(exact(5)/2))
require(below(cf,".43") and below(cm,".60"),"Exact ramp beta constants")
rat=s.Rational(3,8)*s.Rational(501,500)/s.Rational(71,100)+s.Rational(3,80)*s.Rational(501,500)/s.Rational(57,100)+s.Rational(1,160)*s.Rational(63,1000)/s.Rational(57,100)
require(rat==s.Rational(1286055,2158400) and rat<s.Rational(3,5),"Rational intermediate certificate")
require(below(C,exact(501)/500) and below(S,exact(63)/1000),"Hyperbolic rational envelopes")
require(above(kap**(exact(3)/2),exact(71)/100) and above(kap**(exact(5)/2),exact(57)/100),"Gap rational envelopes")
c=exact(43)/100
z2=iv.pi**2/6;z4=iv.pi**4/90;z8=iv.pi**8/9450
# Positive series plus integral tails; no floating zeta value is assumed exact.
M=1000
z3p=sum((exact(1)/k**3 for k in range(1,M+1)),iv.mpf(0))
z3=iv.mpf([z3p.a+(exact(1)/(2*(M+1)**2)).a,z3p.b+(exact(1)/(2*M*M)).b])
d=c*c/tau**2
N=2*d*z4;E=2*iv.sqrt(exact(6)/5)*d*z3
VE=4*(exact(6)/5)*d*(z2+d*z8)
D=iv.sqrt(N/2)
require(below(E*tau**2,".51") and below(D*tau,".448"),"Energy and state errors")
p="physics/qm/null_source/timelike/finite_stress/lapse_boundary/autonomous_preparation/"
old=load(p+"stationary_comparator.json")
m=box(old["probe_magnitude"])
record=iv.exp(-exact(7)/25)*iv.sin(m)
require(above(record,".069"),"Actual prepared-state readout gap")
wp=iv.sqrt(1+r);wm=iv.sqrt(1-r);T=exact(1)/2
zT=((1+r)*iv.cos(wp*T)-(1-r)*iv.cos(wm*T))/2
Vout=VE+exact(14)/25+25*(exact(14)/25+zT*zT)+exact(625)/2
er=box(old["vacuum_energy_same_ESU_convention"])
# 0 <= E_exc <= E, so report intervals rather than adding an upper bound as an equality.
exc=iv.mpf([0,E.b])
work=er+exc
outmean=er+exc+13
require(below(Vout,328),"Prepared retained-system energy variance bound")
# Exact ground-family susceptibility; contact and spectral terms retained together.
Ksus=100
sus=iv.mpf(0)
for k in range(1,Ksus+1):
    sus+=exact(1)/(4*k)-k*k/8*((k*k+r)**(-exact(3)/2)+(k*k-r)**(-exact(3)/2))
stail=15*r*r/(128*kap**(exact(7)/2)*Ksus**4)
susbox=iv.mpf([sus.a-stail.b,sus.b+stail.b])
require(below(susbox,0),"Finite negative ground susceptibility at nonzero r")
Nsym,R,B,H0,harm=s.symbols("N R B H0 harm",real=True)
H=Nsym*(H0+R*B+R**2*harm/8)
require(s.diff(H,Nsym,R)==B+R*harm/4,"Mixed lapse-source column")
require(s.diff(H,R,R)==Nsym*harm/4 and s.diff(H,Nsym,Nsym)==0,"Source contacts")
finish("external_ramp.py",{
"scope":"Actual external-source local linear preparation; no autonomous or Einstein completion",
"model_tau":100,"r_final":"1/5","SI_time_calibration":False,
"bump_integral_lower_bound":outward(Ilo),
"final_beta_bound_coefficient":outward(cf),
"uniform_intermediate_beta_bound_coefficient":outward(cm),
"accepted_simple_beta_bounds":{"final":".43/(tau*k^3)","all_times":".60/(tau*k^3)"},
"adapted_tail_vacuum_Duhamel_bound":"1/(16*sqrt(K)); retained scalar phase tail O(tau/K^4)",
"actual_cutoff_unitary_and_adjoint_strong_limits":True,
"phase_datum":"same inherited c_r=0 energy subtraction, full integral e_K retained",
"excitation_number_upper":outward(N),
"excitation_energy_upper":outward(E),
"excitation_energy_variance_upper":outward(VE),
"half_trace_distance_upper":outward(D),
"same_datum_external_mean_work_enclosure":outward(work),
"renormalized_work_rate_uniformly_summable":True,
"sharp_work_insertion_finite_variance_claimed":False,
"actual_prepared_binary_probability_gap_lower":outward(record),
"postrecord_retained_energy_mean_enclosure":outward(outmean),
"postrecord_retained_energy_variance_upper":outward(Vout),
"final_coupled_all_energy_moments":True,
"intermediate_coupled_all_energy_moments_claimed":False,
"active_time_instantaneous_third_energy_moment":"diverges logarithmically when rdot>0; mean and second moment finite",
"bare_H0_common_form_domain_claimed":False,
"cutoff_energy_convergence":"varying-operator graph recovery, fixed graph only in common diagonal representation",
"true_varying_equation_Hadamard":True,
"same_state_smooth_source_noise_constructed":True,
"finite_cutoff_lapse_source_contacts_retained":True,
"static_ground_family_susceptibility":outward(susbox),
"static_susceptibility_tail_bound":outward(stail),
"ground_family_response_is_actual_fixed_initial_CTP_Hessian":False,
"full_renormalized_arbitrary_lapse_response_constructed":False,
"source_sign_codes_energy_and_stress_laws_identical":True,
"all_record_outcomes_retained":True,
"external_controller_stress_dynamical":False,
"physical_reader_own_stress_constructed":False,
"exact_prepared_state_static_Einstein_test_completed":False
},[p+"stationary_comparator.json",p+"STATIONARY_COMPARATOR.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/conformal_action/QUANTUM_CONTROLLER.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/conformal_action/quantum_controller.json"],
proof="EXTERNAL_RAMP.md")
