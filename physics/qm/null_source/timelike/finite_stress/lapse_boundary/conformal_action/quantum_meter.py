"""Proper-rest meter probabilities, complete instruments, Ward and covariance."""
import sympy as s
from common import finish,require,iv,outward,above,below
from model import HISTORY,chart,extrema
rows,du=chart()
kap=extrema(rows,'kappa')
flow=iv.exp(iv.mpf(1)/100)-iv.exp(-iv.mpf(1)/100)
delta=50*flow/kap
require(above(delta) and below(delta,iv.pi/2),'positive unsaturated readout')
gap=iv.sin(delta)/2
dist=(1-iv.cos(delta/2))/2
memory=iv.sin(delta/2)
require(above(gap,'0.4'),'strict calibrated source contrast')
# Exact four-branch moments for a balanced source and +x memory.
Ec,f=s.symbols('Ec f',real=True)
energies=[Ec+30*f,Ec+30*f,Ec+1+5*f,Ec+1+55*f]
weights=[s.Rational(1,4)]*4
mu=sum(w*x for w,x in zip(weights,energies))
var=s.expand(sum(w*x*x for w,x in zip(weights,energies))-mu*mu)
require(s.simplify(mu-(Ec+s.Rational(1,2)+30*f))==0,'total mean')
require(s.simplify(var-(s.Rational(1,4)+s.Rational(625,2)*f*f))==0,'total variance')
# Quantum Kraus completeness and source channel, exact symbolic phases.
p,m=s.symbols('p m',real=True)
kp=(s.exp(-s.I*p)-s.I*s.exp(-s.I*m))/2
km=(s.exp(-s.I*p)+s.I*s.exp(-s.I*m))/2
require(s.simplify(s.expand_complex(s.conjugate(kp)*kp+s.conjugate(km)*km)-1)==0,'Kraus completeness')
require(s.simplify(s.expand_complex(s.conjugate(kp)*kp)-(1+s.sin(p-m))/2)==0,'pointer sign')
# Positive projected covariance is a congruence of the complete E/A covariance.
ve,va,cov,fu,fv=s.symbols('ve va cov fu fv',real=True)
C=s.Matrix([[ve,cov],[cov,va]])
Mu=s.Matrix([[1,fu],[s.Rational(1,3),0]])
Mv=s.Matrix([[1,fv],[s.Rational(1,3),0]])
noise=Mu*C*Mv.T
require(noise[0,0]==ve+cov*fu+fv*(cov+fu*va),'full density cross block')
require(s.expand(noise[0,1]-(ve+fu*cov)/3)==0,'density pressure cross block')
# Proper-rest statewise conservation.
ee,aa,a=s.symbols('ee aa a',real=True)
rho=(ee+f*aa)/a**4
press=ee/(3*a**4)
der=s.diff(rho,f)*f+s.diff(rho,a)*a
require(s.simplify(der+3*(rho+press))==0,'matter apparatus Ward')
finish('quantum_meter.py',{
 'clock_window':[0.54,0.56],'u_reference':0.55,
 'rest_energy_parameters_times_a_reference':{'mean':30,'coupling':25},
 'phase_difference_bounds':outward(delta),'source_record_gap_bounds':outward(gap),
 'excited_p_plus_bounds':outward(iv.mpf('0.5')+gap),
 'vacuum_p_plus':'1/2','calibrated_source_trace_distance_bounds':outward(dist),
 'conditional_memory_trace_distance_bounds':outward(memory),
 'full_total_variance':'1/4+(625/2) exp(2(u-0.55))',
 'finite_time_exact_reduced_evolution':True,'all_outcomes_retained':True,
 'complete_reader_autonomously_implemented':False,
 'four_dimensional_local_coupling':False},inputs=[HISTORY])
