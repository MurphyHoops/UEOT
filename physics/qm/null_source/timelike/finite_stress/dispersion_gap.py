"""Outward bounds for the conserved-P probability-weighted dispersion diagnostic."""
import sympy as s
from common import *
y,p,v0,u=s.symbols("y p v0 u",positive=True)
F=1-3*y/(2*u)+p**2*y**3/(2*v0*u)
ym=s.sqrt(v0)/p
assert s.simplify(s.diff(F,y).subs(y,ym))==0
assert s.simplify(F.subs(y,ym)-(1-s.sqrt(v0)/(u*p)))==0
t=s.symbols("t",positive=True)
series=s.series(s.asin(s.sqrt(t))**2-t,t,0,5).removeO()
poly=t**2/3+s.Rational(8,45)*t**3+s.Rational(4,35)*t**4
assert s.simplify(series-poly)==0
for n in range(1,8):
    assert s.Rational(4**n,2*n*n*s.binomial(2*n,n))>0
zeta=iv.mpf("1e-12")
rcrit=1/(M2*U0**2)
dx=iv.sqrt(iv.ln(1/zeta)/NU0)
den=iv.sqrt(RHI)-dx
bstar=1-iv.sqrt(rcrit)/den
pstar=(1-zeta)/2
assert above(bstar) and below(bstar,1)
p4=bstar**2/3+8*bstar**3/45+4*bstar**4/35
relative=pstar*(bstar/3+8*bstar**2/45+4*bstar**3/35)
rstar=den**2
Vmin=(K2*rstar/(3*V0))**(iv.mpf(3)/4)
mean_gap=V0*U0*pstar*Vmin*p4
assert above(mean_gap)
finish("dispersion_gap.py",{
 "reference_constraint_mean_negative_magnitude_lower":outward(mean_gap),
 "linear_mean_bound_uniform_on_finite_history_windows":True,
 "reference_defined_only_as_comparison_form":True,
 "r_critical":outward(rcrit),"Gaussian_noise_radius_in_sqrt_K2":outward(dx),
 "event_probability_lower":outward(pstar),"conditional_fraction_lower_on_event":outward(bstar),
 "P_probability_weighted_m_lower":outward(pstar*bstar),
 "P_probability_weighted_m2_lower":outward(pstar*bstar**2),
 "P_probability_weighted_normalized_dispersion_gap_lower":outward(pstar*p4),
 "P_probability_weighted_relative_polymer_gap_lower":outward(relative),
 "all_Gaussian_records_retained":True,
 "reference":"4 gamma sqrt(v) (arcsin sqrt(h))^2 sqrt(v), h=(2-S-S*)/4",
 "global_volume_weighted_ratio_claimed":False,
 "ratio_diagnostics_are_linear_observable_means":False,
 "same_state_reference_constraint_linear_mean_claimed":True,
 "metric_or_experimental_error_claimed":False,
 "full_GR_AE_reference_equivalence_claimed":False})
