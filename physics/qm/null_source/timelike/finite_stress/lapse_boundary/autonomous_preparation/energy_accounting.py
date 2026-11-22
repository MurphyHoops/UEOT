"""Exact total resources, mean projection cost and full-source distance."""
import sympy as s
from common import finish,require,iv,outward,above,below,load,box
P='physics/qm/null_source/timelike/finite_stress/lapse_boundary/autonomous_preparation/'
ac=load(P+'resource_budget.json');ad=load(P+'autonomous_memory.json')
z,m,om=s.symbols('z m om',positive=True)
u=s.sqrt(630)*z**2*(1-z)**2;q=z-s.Rational(3,2)
q2=s.integrate(q**2*u**2,(z,0,1));q4=s.integrate(q**4*u**2,(z,0,1))
cross=s.integrate(-s.diff(u,z,2)*q**2*u,(z,0,1))
require(q2==s.Rational(45,44) and q4==s.Rational(2603,2288) and cross==12,'exact harmonic-clock moments')
mean=6/m+m*om**2*q2/2
second=126/m**2+om**2*cross/2+m**2*om**4*q4/4
variance=90/m**2-3*om**2/22+577*m**2*om**4/25168
require(s.simplify(second-mean**2-variance)==0,'independent exact clock variance')
ER=6+45*iv.pi**2/22;VR=90-6*iv.pi**2/11+577*iv.pi**4/1573
EZ=iv.mpf('1.25e13')+iv.mpf('1.46');VZ=iv.mpf('4.8e13')+iv.mpf('2.804');B2=iv.mpf('1e8')
tot=EZ+B2+ER;vartot=VZ+B2+VR
E1=iv.exp(iv.mpf(1)/10)
projection=iv.mpf(1)/5*iv.sqrt(3*E1)*iv.sqrt(2*(B2+iv.mpf(3)/2*E1-1)+1)
require(below(projection,5200),'complete endpoint projection mean budget')
gaussian_var_up=iv.mpf('312.5')+78*E1
rs=iv.mpf(1)/5
ctail=rs**2/(4*(1-rs**2/16))*(iv.pi**2/6-1)
require(below(ctail,'.00647'),'reference high-source occupation')
eps=box(ac['final_vector_error_bound_interval'])
fullD=eps+iv.sqrt(3)/50+iv.sqrt(ctail)
require(below(fullD,'.116'),'full-source state-distance budget')
a=s.symbols('a',positive=True)
require(s.simplify(((s.sqrt(1+a)-1/s.sqrt(1+a))/2)**2-a**2/(4*(1+a)))==0,'signed squeeze plus factor')
require(s.simplify((a**2/(4*(1+a))+a**2/(4*(1-a)))/2-a**2/(4*(1-a**2)))==0,'source rotation half and both squeeze signs')
finish('energy_accounting.py',{
 'clock_mean_exact':'6+45*pi^2/22','clock_variance_exact':'90-6*pi^2/11+577*pi^4/1573',
 'clock_mean_interval':outward(ER),'clock_variance_interval':outward(VR),
 'full_unitary_mean_interval':outward(tot),'full_unitary_variance_interval':outward(vartot),
 'full_unitary_mean_components':['1.25e13','1.46','1e8','6+45*pi^2/22'],
 'full_unitary_variance_components':['4.8e13','2.804','1e8','90-6*pi^2/11+577*pi^4/1573'],
 'entire_energy_law_preserved_during_unitary':True,
 'terminal_PVM_clock_energy_law_preserved_for_endpoint_preparation':True,
 'terminal_PVM_total_mean_change_absolute_upper_bound_interval':outward(projection),
 'terminal_PVM_actual_strict_nonzero_energy_change_proved':False,
 'terminal_PVM_total_second_moment_proved':False,
 'different_Gaussian_P_reader':{'mean_increment_exact':'12.5','variance_increment_lower':'312.5','variance_increment_upper_interval':outward(gaussian_var_up)},
 'reference_high_source_N_upper_bound_interval':outward(ctail),
 'actual_full_source_half_trace_distance_from_free_upper_bound_interval':outward(fullD),
 'actual_high_source_number_bound_inferred_from_trace_norm':False,
 'terminal_nonselective_reader_preserves_full_source_marginal':True,
 'local_stress_or_Hadamard_error_proved':False
},inputs=[P+'resource_budget.json',P+'autonomous_memory.json',P+'COLLISION.md',P+'AUTONOMOUS_MEMORY.md'])
