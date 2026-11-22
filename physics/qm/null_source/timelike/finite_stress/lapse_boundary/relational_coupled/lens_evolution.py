"""Exact lens cancellation and actual small-K coefficient witness."""
import sympy as s
from common import *
base="physics/qm/null_source/timelike/finite_stress/lapse_boundary/"
new=base+"relational_coupled/"
load(new+"ordering_domain.json")
u=s.symbols("u",real=True)
a=s.Function("a")(u);b=s.Function("b")(u);beta=s.Function("beta")(u)
theta=s.diff(b,u)/(2*a*b)
require(s.simplify(2*a*theta-s.diff(b,u)/b)==0,"Dilation term cancels")
quad=a*theta**2*b**2+beta*b*b+s.diff(theta,u)*b*b/2
pinney=s.diff(a,u)*s.diff(b,u)/a-4*a*beta*b+4*a*a/b**3
require(s.simplify(quad.subs(s.diff(b,u,2),pinney)-a/b**2)==0,"Full quadratic coefficient positive")
g=s.symbols("g",positive=True)
aa=1/(2*g);bb=s.Rational(59,320)-s.Rational(9,8)*g
require(s.simplify(4*aa*bb-(s.Rational(59,160)/g-s.Rational(9,4)))==0,"Actual auxiliary linear equation")
require(s.simplify(-s.diff(aa,g)/4/aa-1/(4*g))==0,"Actual first derivative coefficient")
# Wronskian-based Pinney identity in the s variable.
r1,r2,v1,v2,w=s.symbols("r1 r2 v1 v2 w",real=True)
B=s.sqrt(r1*r1+r2*r2);dot=r1*v1+r2*v2
Bss=(v1*v1+v2*v2-w*(r1*r1+r2*r2))/B-dot**2/B**3
require(s.simplify((Bss+w*B)*B**3-(r1*v2-r2*v1)**2)==0,"Positive scale from fundamental pair")
history="physics/qm/null_source/timelike/joint_history/history.json"
A=box(load(history)["cases"]["unfiltered"]["A"]);J=interval("-.01",".01")
H2=iv.mpf(3)/2
g2=iv.mpf(19)/120+iv.ln(A*A/4)/8+iv.euler/4-H2/4+J/4
d32=iv.mpf(59)/720-g2/2
require(above(g2,"2.57") and below(g2,"2.59") and below(d32,0),"Actual low-K inverted scalar potential")
finish("lens_evolution.py",dict(
 complete_evolution_all_compact_positive_g_windows=True,
 ordering_range="each fixed eta >= -1/4, own Friedrichs form",
 K2_g=outward(g2),K2_d3=outward(d32),
 auxiliary_scale_positive_by_Wronskian=True,auxiliary_ODE_numerically_integrated=False,
 negative_cubic_potential_retained=True,all_source_terms_retained=True,
 original_snapshot_selfadjoint_realization_extended=True,
 negative_g_complete_evolution_proved=False,
 actual_u_original_snapshot_strong_domain_transport_proved=False,
 full_field_limit_claimed=False),
 [history,new+"ordering_domain.json",new+"COUPLED_FORMS.md",new+"SNAPSHOT_DOMAIN.md",
 new+"coefficient_window.json"],proof="LENS_EVOLUTION.md")
