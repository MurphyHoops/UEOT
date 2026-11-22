"""Stable square, exact record/cost identities and outward finite-K budget."""
import sympy as sp
from common import iv,box,load,require,above,below,outward,finish
p='physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/'
prep=load(p+'prepared_record.json');load(p+'scaled_record.json')
V=2*iv.pi**2;K=64;T=iv.mpf(8);a=iv.mpf(4)
eta=iv.mpf(1)/10**13;g=iv.mpf(1)/10**40;ur=iv.mpf(1)/10**16
M0=iv.mpf(16);M1=iv.mpf(343);L0=iv.mpf(357);L1=iv.mpf(10000)
require(below(14/iv.mpf('.9'),M0.a) and below(308/iv.mpf('.9'),M1.a),'profile amplitudes')
require(below(308/iv.mpf('.9')+2*14*iv.mpf('.4')/iv.mpf('.9')**2,L0.a),'first profile derivative')
require(below(8624/iv.mpf('.9')+2*308*iv.mpf('.4')/iv.mpf('.9')**2,L1.a),'second profile derivative')
vy=K*(K+1)/(4*V)
vx=(a+T*T/(4*a))/V+sum(iv.mpf(k*k)/iv.sqrt(k*k-1) for k in range(2,K+1))/(2*V)
vp=sum(iv.mpf(k*k)/iv.sqrt(k*k+iv.mpf(1)/5) for k in range(1,K+1))/(2*V)
amp=iv.exp(2*29*ur/iv.sqrt(iv.mpf(6)/5))
require(below(vy,55) and below(vx,65) and below(amp*vp+iv.mpf('1e-18'),60),'reference even moment envelopes')
C1=iv.sqrt(3)*V*T*60/2*(iv.sqrt(55)*(M0+M1)+iv.sqrt(65)*ur*(L0+L1))
C2=iv.sqrt(105)*V*T*60**2/4*(M0*M0+M1*M1)
require(below(C1,iv.mpf('4e7')) and below(C2,iv.mpf('2e11')),'whole-joint Duhamel constants')
delta=g*C1+g*g*C2
require(below(delta,iv.mpf('5e-33')),'actual norm error')
mu=box(prep['receiver_mean_unit_strength_lower'])
tail=(iv.mpf(22)/5)**2/((K+1)**2-1)*(iv.mpf(3)/(8*(K+1)**2)+iv.sqrt(5)/(16*(K+1)**3))
muK=mu-tail
require(above(muK,iv.mpf('3.3864e-5')),'actual spectral signal')
den=iv.sqrt(2*(iv.mpf('.01')+eta**2*iv.mpf(9)/16))
arg=eta**2*muK/den
gap=2*arg/iv.sqrt(iv.pi)*iv.exp(-arg*arg)
actual=gap-2*delta
require(above(gap,iv.mpf('2.70e-30')) and above(actual,iv.mpf('2.69e-30')),'complete actual binary record')
Ecl=V*(1+ur*ur)/(2*g*g)
quartic=3*g*g*V*(M0*M0+M1*M1)*vp*vp/4
Ezp=sum(iv.mpf(k*k)*(iv.sqrt(k*k+iv.mpf(1)/5)+iv.sqrt(k*k-iv.mpf(1)/5)+2*k)/2 for k in range(1,K+1))
Ezp+=sum(iv.mpf(k*k)*iv.sqrt(k*k-1)/2 for k in range(2,K+1))
Epos=Ecl+Ezp+1/(8*a)+quartic
require(below(Ezp,iv.mpf('1e8')) and below(quartic,iv.mpf('6e-71')) and below(Epos,iv.mpf('1.02e81')),'complete positive Hamiltonian initial mean')
postE=Epos+eta**2/2
v=25*eta**2;dvar=2*v*postE+v*v/2
require(below(dvar,iv.mpf('1e57')),'actual reader variance increment envelope')
y0,y1,f0,f1,gg,phi=sp.symbols('y0 y1 f0 f1 gg phi',real=True)
orig=(y0*y0+y1*y1)/2+gg*(y0*f0+y1*f1)*phi**2/2+gg**2*(f0*f0+f1*f1)*phi**4/4
squares=((y0+gg*f0*phi**2/2)**2+(y1+gg*f1*phi**2/2)**2)/2+gg**2*(f0*f0+f1*f1)*phi**4/8
require(sp.expand(orig-squares)==0,'complete potential stable square')
finish('clock_actuator.py',{
 'K':K,'g':'1e-40','eta':'1e-13','clock_zero_mode_position_variance':'4',
 'initial_time':'-1','encoding_time':'pi','read_time':'pi+3',
 'same_fixed_Hamiltonian_all_eight_programs':True,
 'normal_clock_zero_mode_not_massless_vacuum':True,
 'finite_K_selfadjoint_complete_Hamiltonian':True,
 'controller_point_variance_envelopes':{'X':outward(vx),'Y':outward(vy),'body_before_amplification':outward(vp)},
 'Duhamel_linear_constant_upper':outward(C1),'Duhamel_quadratic_constant_upper':outward(C2),
 'complete_joint_vector_error_upper':outward(delta),
 'independent_K64_signal_tail_upper':outward(tail),'reference_K64_signal_lower':outward(muK),
 'reference_binary_gap_lower':outward(gap),'actual_complete_binary_gap_lower':outward(actual),
 'controller_classical_energy':outward(Ecl),'initial_zero_point_sum':outward(Ezp),
 'initial_quartic_mean_upper':outward(quartic),'full_initial_positive_Hamiltonian_mean_upper':outward(Epos),
 'actual_reader_energy_increment_upper':outward(v/2),
 'actual_reader_variance_increment_upper':outward(dvar),
 'actual_total_variance_claimed_equal_to_reference_budget':False,
 'same_complete_energy_law_for_two_body_codes':True,
 'autonomous_complete_energy_spectral_conservation_between_interventions':True,
 'finite_K_local_Ward_residual_retained':True,
 'finite_g_exact_compact_switch_off':False,
 'actual_eight_unbounded_constraint_means_repaired':False,
 'external_source_CTP_equals_program_overlap':False,
 'uniform_interacting_UV_limit':False,'autonomous_reader':False,
 'fixed_ESU_small_gravitational_backreaction':False,'SI_calibration':False
},inputs=[p+'SOURCE_CTP.md',p+'QUANTIFIED_PREPARATION.md',p+'prepared_record.json',p+'scaled_record.json'])
