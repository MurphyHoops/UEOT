"""Covariant static datum: exact identities and independently summed intervals."""
import sympy as sp
from common import iv,require,above,below,outward,box,load,finish
r=iv.mpf(1)/5;kappa=1-r;V=2*iv.pi**2;K=256
e=iv.mpf(0);ep=iv.mpf(0);epp=iv.mpf(0)
for k in range(1,K+1):
    x=r/k**2
    e+=k**3*((iv.sqrt(1+x)+iv.sqrt(1-x))/2-1+x*x/8)
    ep+=iv.mpf(k)/4*((1+x)**(-iv.mpf(1)/2)-(1-x)**(-iv.mpf(1)/2))+r/(4*k)
    epp+=-( (1+x)**(-iv.mpf(3)/2)+(1-x)**(-iv.mpf(3)/2) )/(8*k)+iv.mpf(1)/(4*k)
te=5*r**4/(512*(1-r*r)*K**4)
tep=5*r**3/(128*(1-r*r)**2*K**4)
tepp=15*r*r/(128*kappa**(iv.mpf(7)/2)*K**4)
e=iv.mpf([(e-te).a,e.b]);ep=iv.mpf([(ep-tep).a,ep.b]);epp=iv.mpf([(epp-tepp).a,epp.b])
F=4*e-2*r*ep+r*r/8;Fp=2*ep-2*r*epp+r/4
rho=e/V;p=(e-2*r*ep+r*r/8)/(3*V)
G=3*V/(4*iv.pi*F);Lam=3-8*iv.pi*G*rho
C2=24*(r*Fp/F-1)
require(below(e,0) and below(ep,0) and below(epp,0),'source signs')
require(above(F) and above(G) and above(rho+p) and above(C2,24),'mean data positivity')
old=load('physics/qm/null_source/timelike/finite_stress/lapse_boundary/autonomous_preparation/stationary_comparator.json')
old_e=box(old['vacuum_energy_same_ESU_convention'])
require(old_e.a<=e.a and e.b<=old_e.b,'independent refined interval must lie in old energy enclosure')
# Exact algebra is separate from interval correlations.
ee,ee1,ee2,rr,v=sp.symbols('e e1 e2 r V',nonzero=True)
ff=4*ee-2*rr*ee1+rr**2/8
gg=3*v/(4*sp.pi*ff);ll=3-8*sp.pi*gg*ee/v
pp=(ee-2*rr*ee1+rr**2/8)/(3*v)
require(sp.simplify(ll-1-8*sp.pi*gg*pp)==0,'pressure mean identity')
rho1=(-4*ee+2*rr*ee1-rr**2/8)/v
rho2=(20*ee-14*rr*ee1+4*rr**2*ee2+rr**2/8)/v
require(sp.simplify(-12-16*sp.pi*gg*rho1)==0,'first radius derivative')
target=24*(rr*(2*ee1-2*rr*ee2+rr/4)/ff-1)
require(sp.simplify(36-16*sp.pi*gg*rho2-target)==0,'second radius derivative')
alpha=1/(4320*v)
require(sp.simplify(-36*alpha*v+sp.Rational(1,120))==0,'R2 Casimir cancellation')
finish('ground_datum.py',{
 'r':'1/5','constituent_K':K,'energy':outward(e),'energy_source_derivative':outward(ep),
 'energy_second_source_derivative':outward(epp),'tail_bounds':[outward(te),outward(tep),outward(tepp)],
 'F':outward(F),'F_prime':outward(Fp),'rho':outward(rho),'pressure':outward(p),
 'rho_plus_pressure':outward(rho+p),'G_N_model_units':outward(G),'Lambda_model_units':outward(Lam),
 'static_scalar_constraint_second_radius_derivative':outward(C2),
 'same_unit_radius_inherited_ground_energy':True,
 'new_covariant_finite_curvature_and_source_datum_declared':True,
 'restricted_radius_cutoff_matching_log_retained':True,
 'mean_static_equations_exact':True,'actual_AQ_ramp_state_used':False,
 'finite_past_preparation_or_stability_established':False,
 'arbitrary_metric_finite_cutoff_covariance_established':False,
 'finite_slice_R2_CTP_boundary_completion_established':False,
 'SI_calibration':False
},inputs=['physics/qm/null_source/timelike/finite_stress/lapse_boundary/autonomous_preparation/stationary_comparator.json'])
