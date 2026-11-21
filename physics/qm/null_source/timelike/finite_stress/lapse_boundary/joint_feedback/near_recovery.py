"""Exact packet identities and uniform scaled bounds for a normal near-recovery family."""
import sympy as s
from common import *
P="physics/qm/null_source/timelike/finite_stress/lapse_boundary/"
paths=[P+"relational_coupled/negative_recovery.json",P+"quiet_window.json",
       P+"relational_coupled/NEGATIVE_RECOVERY.md",P+"joint_feedback/WEIGHTED_EVOLUTION.md",
       P+"joint_feedback/POSITIVE_WINDOW.md"]
neg,quiet=load(paths[0]),load(paths[1])
require(neg["actual_K"]==131072 and quiet["new_initial_slow_amplitude_exact"]=="exp(-20000)","Same actual inputs")
d,h,R,ic,il=s.symbols("delta h R i_c i_l",positive=True)
m=(1-d)*h;w=d*h/(R-m)
require(s.simplify((1-w)*m+w*R-h)==0,"Exact geometry mean")
q=s.symbols("q")
require(s.simplify((1-w)*m*q+w*R*q-q*h)==0,"Phase kinetic budget uses full mean")
require(s.simplify((1-w)*q+w*q-q)==0,"Inverse-kappa velocity current has constant phase coefficient")
require(s.Rational(2,9)-s.Rational(2,64)>s.Rational(1,6),"Central kinetic lower margin")
# For d<=1/64, a=|eta-3/4|>=0, Q exceeds both positive forms plus one.
require(770*64-22991>0,"Q shape budget")
require(s.Rational(1,1)/(1-s.Rational(1,64))**2-1 < s.Rational(3,64),"Inverse central upper")
require(s.Rational(1,1)/(1-s.Rational(1,8))**3<2,"Central inverse cube")
require(s.Rational(1,1)/(1-s.Rational(1,8))**5<2,"Central inverse fifth")
hu=iv.exp(-19980)
require(below(hu,iv.mpf("1e-100")),"Tiny actual h without floating underflow")
require(below(exact(2)*hu/(1-hu),exact(1)/4),"Uniform w<delta/4")
require(below(exact(4)*hu**2,1),"Remote inverse contribution <delta")
# F(1)*h^3 <= -3/(6d) + small; d<=1/64.
positive_one=2*iv.exp(60)*hu**2+iv.exp(30)*hu**4+2*hu**6+exact(4)/64*hu**4
require(below(positive_one,1),"Scaled lower endpoint positive terms")
require(3*64/6-1>1,"Lower endpoint lies below target")
# At upper endpoint Q>q_c+q_l+1, Q>=64000. Drop favorable gaps conservatively.
upper_errors=exact(".0008")/64**3*hu**12/64000+4*hu**2+2*iv.exp(60)*hu**2
require(below(upper_errors,1),"Scaled upper endpoint errors")
require(14*64000-5*64000-1>1,"Upper endpoint lies above target")
finish("near_recovery.py",dict(actual_K=131072,delta_rule="min(1/64,theta/8)",
 inverse_mean_relative_error={"strict_lower":"delta/2","strict_upper":"4 delta <= theta/2"},
 momentum_root="one IVT root in [1, 10 sqrt(Q/delta) h^-2]",
 relative_first_jet_error_can_be_arbitrarily_small=True,
 exact_normal_first_jet_recovery=False,geometry_mean_and_velocity_match=True,
 full_initial_generator_budget_retained=True,
 geometric_variance_lower="1/(6h)",third_moment_lower="h^-3/(24 delta)",
 positive_source_window="min(T0, theta L/(2 C2))",
 window_uniform_in_tolerance=False,geometry_history_recovered=False,
 all_actual_states_normal=True,sharp_delta_limit_normal=False,
 scientific_claim_checked_by_script="finite algebra and uniform bounds; analytic existence and domains in proof"),
 paths)
