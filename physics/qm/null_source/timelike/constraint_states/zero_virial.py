"""Exact Gaussian ordering, actual-state floor and free-mode dilation."""
import sympy as s
from common import *
q,p,v,m=s.symbols("q p v m",real=True)
# Weyl product (q*p) star (q*p), including its second-order Moyal term.
f=q*p
star=s.expand(f*f+s.I/2*(s.diff(f,q)*s.diff(f,p)-s.diff(f,p)*s.diff(f,q))
 -s.Rational(1,8)*(s.diff(f,q,2)*s.diff(f,p,2)-2*s.diff(f,q,p)**2+s.diff(f,p,2)*s.diff(f,q,2)))
assert star==q*q*p*p+s.Rational(1,4)
one=(v+m*m)/(4*v)+s.Rational(1,4)
assert s.simplify(one-(s.Rational(1,2)+m*m/(4*v)))==0
lam0,zeta=s.symbols("lam0 zeta",real=True)
chi=s.sech(lam0)*s.exp(-zeta*(1-s.sech(lam0)))
assert s.simplify(-s.diff(chi,lam0,2).subs(lam0,0)-(1+zeta))==0
a,lam=s.symbols("a lam",positive=True)
kin=p*p/(2*a**3)
assert s.diff(kin.subs(p,s.exp(-lam)*p),lam).subs(lam,0)==-p*p/a**3
Sbar=2*VP+K2*L
VD=1+K2*L/(4*VP)
floor=Sbar**2/(4*A**6*VD)
rho_floor=floor/(V0**2*A**6)
assert above(floor,4) and below(floor,6)
assert above(rho_floor)
finish("zero_virial.py",{
 "mean_P1sq_plus_P2sq":outward(Sbar),"variance_desheared_D":outward(VD),
 "proper_energy_constraint_variance_lower":outward(floor),
 "proper_energy_constraint_RMS_lower":outward(iv.sqrt(floor)),
 "proper_density_constraint_variance_lower":outward(rho_floor),
 "proper_density_constraint_RMS_lower":outward(iv.sqrt(rho_floor)),
 "correlated_or_entangled_geometry_allowed":True,"G_positive_required":False,
 "fixed_complete_original_zero_marginal_required":True,
 "variable_volume_floor":"same formula with A replaced by a_max when radius support<=a_max",
 "exact_form_exclusion_requires_actual_dilation_invariant_extension_domain":True,
 "P_only_interaction_assumed_to_commute_with_dilation":False,
 "full_quantum_gravity_or_experimental_bound_claimed":False})
