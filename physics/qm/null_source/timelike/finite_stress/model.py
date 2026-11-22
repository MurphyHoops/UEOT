"""Canonical normalization, continuum ordering and critical scales."""
import sympy as s
from common import *
a,pv,v0=s.symbols("a pv v0",positive=True)
pa=3*a**2*pv
assert s.simplify(-pa**2/(6*v0*a)+3*a**3*pv**2/(2*v0))==0
x=s.symbols("x",positive=True);psi=s.Function("psi")(x)
phi=psi/s.sqrt(2*x)
kin=s.sqrt(2*x)*3/(2*v0)*x*s.diff(s.diff(x*phi,x)/(2*x),x)/(2*x)
target=3/(8*v0)*s.diff(psi,x,2)-9/(32*v0*x**2)*psi
assert s.simplify(kin-target)==0
ell,u=s.symbols("ell u",positive=True)
g=3/(8*v0*ell**2)
assert s.simplify((4*g-v0*u).subs(ell**2,3/(2*v0**2*u)))==0
assert above(ELLC) and above(D) and below(4*ALPHA*16000/D,exact(8)**(iv.mpf(4)/3))
y=s.symbols("y",real=True)
low=1-s.sqrt(1-y**2)-y*s.asin(y)
high=1+s.sqrt(1-y**2)+y*s.asin(y)
assert s.series(low,y,0,3).removeO()==-y**2/2
assert s.series(high,y,0,3).removeO()==2+y**2/2
finish("model.py",{
 "canonical_transformation_verified":True,
 "continuum_kinetic":"c*d_x^2-3*c/(4*x^2), c=3/(8*V0)",
 "continuum_constant_weight_equivalents":[-1,3],
 "continuum_bad_P_squared_threshold":outward(3/(4*V0)),
 "critical_ell_squared":outward(ELLC2),"critical_ell":outward(ELLC),
 "critical_delta":outward(DELTA),"critical_gamma_kinetic":outward(GAMMA),
 "critical_alpha":outward(ALPHA),"critical_d":outward(D),
 "critical_density_equals_U0":True,
 "same_as_standard_closed_F_quantization":False,
 "new_physical_inputs":["positive-volume semilattice","ell","dust sign/clock","spectral inverse","square-root ordering","two-zero-mode reduction"],
 "self_adjointness":"Carleman on c00; common bounded-P-perturbation domain",
 "full_original_AE_model_restored":False,"uniform_finite_stress_continuum_limit":False})
