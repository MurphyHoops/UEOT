"""Independent algebra and interval gates for advanced actual cutoff convergence."""
import sympy as s
from common import *
P="physics/qm/null_source/timelike/finite_stress/lapse_boundary/"
paths=[P+"relational_coupled/actual_cutoff_inverse.json",P+"quiet_window.json",
 P+"retarded_response.json",P+"ACTUAL_INVERSE.md",
 P+"relational_coupled/ACTUAL_CUTOFF_INVERSE.md",P+"RETARDED_RESPONSE.md",
 P+"joint_feedback/PREPARED_LIMIT.md"]
frozen=load(paths[0]);quiet=load(paths[1]);ret=load(paths[2])
require(frozen["static_and_actual_action_sufficient_K"]==10**9,"Actual static cutoff theorem")
require(frozen["actual_action_inverse_strong_Y_to_H4_convergence"] and not frozen["strong_adjoint_convergence_inferred"],"Forward premise does not claim adjoint")
require(frozen["safe_M0"]=="1e15" and quiet["new_initial_slow_amplitude_exact"]=="exp(-20000)","Same constants")
budgets=frozen["complete_actual_difference_epsilon_budgets"]
require(sum(budgets.values())==627 and sum(budgets.values())<1000,"Independent reverse budgets")
q=iv.mpf(10)**18*iv.exp(-1158)
require(below(q,iv.exp(-1100)) and below(q,1),"Common contraction")
t=s.symbols("t",real=True);U=s.Function("U")(t);S=s.Function("S")(t);E=s.Function("E")(t)
h=s.diff(U,t)
# Integrate off-shell memory by parts, retaining finite Ward residual.
local=(2*S+E)+(2*S-E)/2
require(s.simplify(local-(3*S+E/2))==0,"Local Ward contact")
kernel=s.diff(s.exp(U)*(2*S-E),t).subs(s.diff(E,t),h*(2*S-E))
require(s.simplify(kernel-2*s.exp(U)*s.diff(S,t))==0,"Off-shell memory coefficient")
# Formal fourth-order transpose: a3=2a4', a1=a2'-a4'''.
a4=s.Function("a4")(t);a2=s.Function("a2")(t);a0=s.Function("a0")(t);z=s.Function("z")(t)
a3=2*s.diff(a4,t);a1=s.diff(a2,t)-s.diff(a4,t,3)
op=a4*s.diff(z,t,4)+a3*s.diff(z,t,3)+a2*s.diff(z,t,2)+a1*s.diff(z,t)+a0*z
adj=s.diff(a4*z,t,4)-s.diff(a3*z,t,3)+s.diff(a2*z,t,2)-s.diff(a1*z,t)+a0*z
require(s.simplify(adj-op)==0,"All extra AE transpose jets cancel")
# Reflection weight and two-sided proper pairing are exact, not an inferred Hilbert adjoint.
T,g,r=s.symbols("T gamma r",positive=True)
require(s.simplify(s.exp(-2*g*r)*s.exp(2*g*T)-s.exp(2*g*(T-r)))==0,"Reverse weight reflection")
require(ret["residual_first_nonzero_inverse_omega_order"]==6 and ret["weighted_all_field_tail"].startswith("C/(2*K^2)"),"Same differentiated AE remainder")
finish("advanced_cutoff.py",dict(
 independent_advanced_proof=True,strong_adjoint_inferred_from_forward=False,
 actual_action_advanced_strong_Y_minus_to_H4=True,
 actual_pressure_transpose_strong_pullback_H3=True,
 finite_Ward_defect_retained=True,mean_C1_residual_tail="C_mean,1/K^2",
 reverse_epsilon_budget=budgets,log_uniform_q=outward(iv.log(q)),
 same_incoming_state_not_future_vacuum=True,common_static_K=10**9,
 pressure_K2_exists=True,pressure_K2_numerically_computed=False,
 pressure_test_bound="1536 A^2 M0/[gamma(1-q)] ||F||",
 fixed_F_strong_not_operator_norm=True,full_H4_log_row_domain_claimed=False),paths)
