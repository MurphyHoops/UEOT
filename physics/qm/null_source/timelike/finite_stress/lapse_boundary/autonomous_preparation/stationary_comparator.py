"""AP: exact algebra and interval certificate; no old science imports or ODE."""
from common import finish,require,iv,exact,outward,above,below
import sympy as s
r=exact(1)/5;a=1-r;V=2*iv.pi**2
wp=iv.sqrt(1+r);wm=iv.sqrt(1-r);T=exact(1)/2;sig=exact(1)/10
theta_bound=r/(4*a)
hs=r*r*((iv.exp(theta_bound)+iv.exp(-theta_bound))/2)**2*(iv.pi**2/6)/(8*a*a)
require(below(hs,".013"),"Fock implementer HS bound")
K=100
ep=iv.mpf(0)
for k in range(1,K+1):
    z=r/k**2
    ep+=k**3*((iv.sqrt(1+z)+iv.sqrt(1-z)-2)/2+z*z/8)
tail=5*r**4/(512*a**(exact(7)/2)*K**4)
er=iv.mpf([ep.a-tail.b,ep.b+tail.b])
require(below(er,0) and above(er,"-.000142"),"Finite energy convention")
m=(wp*iv.sin(wp*T)-wm*iv.sin(wm*T))/2
vp=(wp+wm)/4;wE=(wp**3+wm**3)/4
gap=iv.exp(-(vp+sig**2)/2)*iv.sin(m)
require(above(gap,".071") and below(gap,".08"),"Actual binary calibration")
zT=((1+r)*iv.cos(wp*T)-(1-r)*iv.cos(wm*T))/2
v=1/(4*sig**2)
outmean=er+exact(1)/2+v/2
outvar=wE+v*(wE+zT**2)+v*v/2
p2=2*r*r/(3*V)
require(above(p2),"Static pressure rejection")
x,y,px,py,R,xi=s.symbols("x y px py R xi",real=True)
H=(px**2+py**2+x**2+y**2)/2+R*x*y
change=s.expand(H.subs(y,y+xi)-H)
require(s.expand(change-(xi*(y+R*x)+xi**2/2))==0,"Same-H Gaussian energy increment")
q0,V0=s.symbols("q0 V0",positive=True)
# Independent algebra at t=0 and on-shell classical conservation.
dq=s.Matrix([px,py,-x-R*y,-y-R*x])
gradH=s.Matrix([s.diff(H,z) for z in [x,y,px,py]])
require(s.expand(gradH.dot(dq))==0,"Classical energy conservation")
pressure=(px**2+py**2+x**2+y**2)/(6*V0)-R*x*y/(3*V0)
require(s.expand(pressure-H/(3*V0)+2*R*x*y/(3*V0))==0,"Complete pressure trace")
dp=s.diff(pressure,x)*px+s.diff(pressure,y)*py+s.diff(pressure,px)*(-x-R*y)+s.diff(pressure,py)*(-y-R*x)
ddp=sum(s.diff(dp,z)*zz for z,zz in zip([x,y,px,py],dq))
require(s.expand(ddp.subs({x:q0,y:0,px:0,py:0})-2*R**2*q0**2/(3*V0))==0,"Pressure second derivative")
k=s.symbols("k",positive=True)
pvar=R**2*k**2*(1/(k**2+R)+1/(k**2-R))/18
require(s.factor(pvar-R**2*k**4/(9*(k**4-R**2)))==0,"Sharp pressure variance")
inputs=[
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/conformal_action/QUANTUM_CONTROLLER.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/conformal_action/quantum_controller.json",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/conformal_action/LOCAL_FIELD_PROBE.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/conformal_action/PROBE_PHASE.md"]
finish("stationary_comparator.py",{
"scope":"Fixed-ESU local linear comparison; new correlated state, not AL nonlinear model or original minimal geometry",
"r":"1/5","model_T":"1/2","model_sigma":"1/10","SI_time_calibration":False,
"implementer_HS_squared_upper":outward(hs),
"vacuum_energy_same_ESU_convention":outward(er),
"energy_partial_sum_K":K,"energy_tail_bound":outward(tail),
"probe_magnitude":outward(m),"probe_variance":outward(vp),
"binary_probability_gap":outward(gap),
"total_energy_mean":outward(er+exact(1)/2),"total_energy_variance":outward(wE),
"nonselective_same_H_energy_increase":"25/2",
"nonselective_same_H_energy_mean":outward(outmean),
"nonselective_same_H_energy_variance":outward(outvar),
"pressure_second_derivative":outward(p2),
"sharp_pressure_variance_lower_bound":"K/225; diverges",
"stress_noise":"Full matrix W, complete tensor, spacetime tests; actual centered K-vector strong convergence and varying-H_K graph recovery",
"code_energy_laws_identical":True,"code_stress_statistics_identical":True,
"source_sign_record_is_energy_or_geometry_charge_record":False,
"initial_mixed_block":"derived coupled-ground covariance",
"specified_conditional_and_nonselective_reader_states_Hadamard":True,
"coupled_ground_all_actual_H_moments":True,"bare_H0_ground_mean_finite":False,
"finite_past_ground_preparation_proved_here":False,
"arbitrary_spatial_lapse_CTP_constructed":False,
"static_Einstein_solution_for_these_codes":False,
"all_record_outcomes_retained":True,
"autonomous_reader_own_stress_included":False,
"absolute_covariant_vacuum_stress_fixed_by_e_only":False,
"old_local_free_field_probe_theorems_claimed_new":False
},inputs,proof="STATIONARY_COMPARATOR.md")
