"""Three parameter regimes with exact recurrence and cap algebra."""
import sympy as s
from common import *
n,alpha,b,d,eps,z=s.symbols("n alpha b d eps z",positive=True)
wm,w,wp=s.symbols("wm w wp")
lhs=alpha*s.sqrt(n*(n-1))*wm/s.sqrt(n-1)+(b*n-d*n**s.Rational(1,3)+eps/n-z)*w/s.sqrt(n)+alpha*s.sqrt(n*(n+1))*wp/s.sqrt(n+1)
expected=wp+wm+(b/alpha-d/alpha*n**s.Rational(-2,3)+eps/(alpha*n**2)-z/(alpha*n))*w
assert s.simplify(lhs/(alpha*s.sqrt(n))-expected)==0
y,mu,v0=s.symbols("y mu v0",positive=True)
poly=3*v0*y**2-2*mu*y**3
assert s.simplify(s.diff(poly,y).subs(y,v0/mu))==0
assert s.simplify(poly.subs(y,v0/mu)-v0**3/mu**2)==0
assert s.simplify(s.diff(poly,y,2).subs(y,v0/mu)+6*v0)==0
eta=s.symbols("eta",positive=True)
assert s.simplify((v0**3/(eta*v0*s.Symbol("u",positive=True))**2)/(v0*s.Symbol("m2",positive=True))-1/(eta**2*s.Symbol("m2",positive=True)*s.Symbol("u",positive=True)**2))==0
rcrit=1/(M2*U0**2)
assert below(rcrit,RHI.a)
finish("phase_diagram.py",{
 "recurrence_exact_including_curvature":True,
 "subcritical":"0<q<4gamma: no nonzero normal H<=0 state has any positive volume moment",
 "subcritical_H2_assumption_needed":False,
 "supercritical":"q>4gamma: physical momentum support must satisfy P^2<V0^3/(q-4gamma)^2",
 "supercritical_cap_endpoint_excluded":True,
 "necessary_cap_is_sufficient":False,
 "critical_only_for_exact_original_P_law_and_finite_volume_in_this_family":True,
 "critical_normalized_momentum_threshold":outward(rcrit),
 "finite_error_critical_uniqueness_claimed":False,
 "coherence_error_from_geometry_encoding_included_in_tail_bound":False,
 "all_quantum_gravity_models_excluded":False})
