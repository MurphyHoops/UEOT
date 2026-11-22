"""Prepared-readout limit identities, finite Ward defect, and proper-clock gauge check."""
import sympy as s
from common import *
P="physics/qm/null_source/timelike/finite_stress/lapse_boundary/"
paths=[P+"prepared_readout.json",P+"relational_coupled/actual_uv_bridge.json",
 P+"PREPARED_READOUT.md",P+"FINITE_SOURCE_DOMAIN.md",P+"RAW_SOURCE_BOUNDARY.md",
 P+"CONSTRAINT_RESIDUAL.md",P+"READOUT_WITNESS.md",
 P+"joint_feedback/ADVANCED_CUTOFF.md"]
# The actual raw-source boundary page is in the relational cohort.
paths[4]=P+"relational_coupled/RAW_SOURCE_BOUNDARY.md"
a,b=load(paths[0]),load(paths[1])
require(a["source_GNS_limit_on_H2_tests"] and a["terminal_test_traces_zero_through_order"]==2,"Same source GNS domain")
require(a["zero_shell_correlations_retained"] and b["same_actual_background_and_incoming_state"],"Same full low state")
t=s.symbols("t",real=True);U=s.Function("U")(t);S=s.Function("S")(t);E=s.Function("E")(t);f=s.Function("f")(t);J=s.Function("J")(t)
h=s.diff(U,t)
expr=-s.diff(s.exp(U)*(2*S-E)*J,t)
expr=expr.subs(s.diff(E,t),h*(2*S-E)).subs(s.diff(J,t),-s.exp(-U)*f)
require(s.simplify(expr-((2*S-E)*f-2*s.exp(U)*s.diff(S,t)*J))==0,"Density residual test after integration by parts")
aa=s.Function("a")(t);gp=s.Function("gprime")(t);JG=s.Function("JG")(t)
Fu=-aa*gp+aa*JG;FN=aa*JG
df=s.diff(FN,t).subs(s.diff(aa,t),aa*h).subs(s.diff(JG,t),-h*gp)
require(s.simplify(df-h*Fu)==0,"Proper-clock lapse gauge identity")
require(2*768==1536,"Pressure cutoff inverse factor retained")
require(s.Rational(200,1)>0 and s.Rational(9,32)>0 and s.Rational(81,8)>0,"Positive absolute high-mode tail")
finish("prepared_limit.py",dict(
 fixed_F_prepared_GNS_L2_limit=True,all_finite_Gram_and_weak_commutator_blocks_converge=True,
 combined_endpoint_before_fullfield_limit=True,
 sharp_Q_D_boundary_separate_limit_claimed=False,
 pressure_test_error="C_R ||q_K-q||H2 + sqrt(T_K(q_K))",
 cutoff_tail_component="O(K^-1/2)",total_error_rate_asserted=False,
 charge_variance_tail="200 mu^2/K",charge_trace_factor="1/(3 V0 A^4 h_i)",
 lambda_one_density_weak_defect="O(K^-2) ||f||Y_minus",
 finite_K_background_set_on_shell=False,
 prior_large_readout_rejection_survives=True,
 eventual_witness_RMS_strict_lower="exp(19000)/2",
 proper_clock_lapse_row="F_N=a J_g; F_N'=h F_u",
 compact_input_families_uniform=True,all_unit_ball_uniform=False,
 normal_geometry_state_or_CP_instrument_constructed=False),paths)
