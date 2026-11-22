"""Canonical current identities and constants in the higher-domain proof."""
import sympy as s
from common import *
k,alpha=s.symbols("k alpha",real=True,positive=True)
a=s.Function("a")(k);b=s.Function("b")(k);pot=s.Function("pot")(k)
L=lambda q:-alpha*s.diff(s.diff(q,k)/k,k)+pot*q
current=-s.I*alpha/k*(s.diff(a,k)*b-a*s.diff(b,k))
rate=-s.I*L(a)*b+s.I*a*L(b)
require(s.simplify(rate+s.diff(current,k))==0,"Geometry current identity")
test=s.Function("test")(k)
require(s.simplify(-s.diff(test*current,k)+s.diff(test,k)*current+test*s.diff(current,k))==0,"Weighted weak current row")
n=s.symbols("n",nonnegative=True)
require(s.expand((n+s.Rational(3,2))**2-(n+1)*(n+2))==s.Rational(1,4),"Raising bound")
require(s.expand((n-s.Rational(1,2))**2-n*(n-1))==s.Rational(1,4),"Lowering bound")
require(s.simplify(3*(n+s.Rational(1,2))-(2*n+1))==n+s.Rational(1,2),"Combined row bound")
require(below(45*iv.sqrt(5),101),"Source cube commutator")
minimum=1-iv.sqrt(3)/3
require(above(minimum),"kappa <= 1 + 4 kappa^3/9")
R=s.symbols("R",positive=True);fr=R/(1+R*k)
require(s.simplify(s.diff(fr,k)+fr**2)==0,"Inverse regularization current derivative")
bph=s.symbols("bph",real=True);density=s.Function("density")(k)
Jph=2*alpha*bph*density
require(s.simplify(-Jph/k**2+2*alpha*bph*density/k**2)==0,"Initial inverse-current coefficient")
finish("weighted_evolution.py",dict(
 comparison_source_power_integers="p>=3; Qp propagation of the same unitary",
 source_commutator_bound="3 p 5^(p/2)",
 source_cube_commutator_upper=outward(45*iv.sqrt(5)),
 zero_mode_dilation_extra_bound="2 p",
 trace_C1_source_class="Q6",
 general_Q3_weighted_density_trace_continuous=True,
 global_tau_derivative_or_kappa_minus_two_moment_from_Q3=False,
 exact_operator_valued_local_current=True,
 legal_global_inverse_regularization="R/(1+R*kappa)",
 current_is_included_in_weighted_hierarchy=True,
 complete_joint_density_remains_closed=True,
 raw_snapshot_strong_domain_transport_assumed=False),
 ["physics/qm/null_source/timelike/finite_stress/lapse_boundary/relational_coupled/ALL_SIGN_EVOLUTION.md",
 "physics/qm/null_source/timelike/finite_stress/lapse_boundary/relational_coupled/ORDERING_DOMAIN.md",
 "physics/qm/null_source/timelike/finite_stress/lapse_boundary/relational_coupled/GEOMETRIC_MOMENTUM.md"])
