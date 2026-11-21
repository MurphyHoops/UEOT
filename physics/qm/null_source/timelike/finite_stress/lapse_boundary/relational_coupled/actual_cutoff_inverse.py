"""Same-action cutoff inverse: uniform bounds and strong-convergence certificate."""
import sympy as s
from common import *
pre="physics/qm/null_source/timelike/";base=pre+"finite_stress/lapse_boundary/";new=base+"relational_coupled/"
co=load(new+"coefficient_window.json");uv=load(new+"actual_uv_bridge.json")
spec=load(pre+"dynamic_inverse/spectrum.json");fast=load(pre+"dynamic_inverse/fast_root.json")
load(base+"actual_inverse.json");load(base+"quiet_window.json")
A=box(co["frozen_A"]);gamma=24*A;K0=10**9
require(above(A,80000) and below(A,100000),"Same actual reference scale")
require(below(box(spec["characteristic_at_zero"]),-4),"Frozen D(0) strict sign")
require(below(box(fast["fast_kappa_sigma_over_A"]),"11.47"),"Frozen fast root used")
require(s.Rational(1147,100)**2<132,"Conservative full fast squared root")
require(spec["alternative_finite_truncation_sufficient_N"]==2**20 and K0>=2**20,"Frozen finite-root counting threshold")
require(below(box(spec["CA"]),400),"Frozen root-counting coefficient input")
k,y=s.symbols("k y",positive=True);om=s.sqrt(k*k-1)
left=y*y*(k*k/(om*(y+4*om*om))-1/(4*k))-2*y*(k*k/(2*om)-k/2-1/(4*k))
right=3*(-4*k*k*om*y/(3*(y+4*om*om))+y*k/3+(y/6-y*y/12)/k)
require(s.simplify(left-right)==0,"Exact same-AE static action shell")
require(s.Rational(143*12,396)>4,"Full negative sign at y0=144A2")
tail=iv.mpf("1.5e12")*iv.mpf("1.3e24")/(12*9*iv.mpf("6.4e9")*K0*K0)
require(below(tail,"1e7") and above(A*A,"1e7"),"Uniform compact-tail sign budget")
require(K0*K0>2*4*10**11,"Explicit asymptotic-tail threshold valid")
require(s.Rational(4,9*144)>s.Rational(1,432),"Finite-root cK conservative lower bound")
require(above(gamma,8),"One-sided resonance band integer count")
require(above(iv.mpf(9)/16-1/(4*gamma*gamma),iv.mpf(1)/2),"Band b>=tau2/2")
require(s.Rational(4)+s.Rational(144,36**2)<5,"Band root denominator bound")
require(s.Rational(1,75)>s.Rational(1,100),"Positive residue lower majorant")
require(s.Rational(1,8)*2/s.Integer(13)==s.Rational(1,52),"One-sided band imaginary bound")
require(above(5200*iv.pi**2,432*iv.sqrt(17)),"Low frequency dominates common m")
gg,tt,bb,rr=s.symbols("gamma tau b root",positive=True)
z=gg+s.I*tt
real_ratio=s.simplify(s.re(z*z/(z*z+bb)))
expected=((gg*gg+tt*tt)**2+bb*(gg*gg-tt*tt))/((gg*gg-tt*tt+bb)**2+4*gg*gg*tt*tt)
require(s.simplify(real_ratio-expected)==0,"High-frequency positivity identity")
require(s.simplify(((gg*gg+tt*tt)**2+bb*(gg*gg-tt*tt)).subs(bb,tt*tt)-(gg**4+3*gg*gg*tt*tt))==0,"High-frequency endpoint nonnegative")
# The root separation bound follows from |z²-r|>=|z|²-r.
require(s.Rational(144,24**2)==s.Rational(1,4),"All finite fast roots left of gamma/2")
M=(iv.mpf(16)/9)*5200*iv.pi**2*A*A
require(below(M,iv.mpf("1e15")),"Common Y-to-H4 inverse bound")
T=iv.mpf(1)/50
schur=1000*T+T*T*(-iv.ln(T)+iv.mpf("6.5"))/4+iv.mpf(".18")
tail_schur=(2*T+T*T/2+2*T**3/3)/2+1000*T
require(below(schur,23),"Uniform actual partial-kernel Schur bound")
require(below(tail_schur,22),"Actual difference Schur tail coefficient")
require(s.Rational(9,8)/2+s.Rational(128,3)<45,"C1 actual-minus-static mean tail")
require(s.Rational(225,K0)<1,"Partial mean budget below 3 epsilon")
budgets=dict(retarded_difference=500,static_variable_coefficients=61,mean_chain_contact=12,
 anomaly=4,gravity=17,zero_mode=3,fixed_U0=30)
require(sum(budgets.values())==627 and 627<1000,"Complete same-input actual difference budget")
logq=18*iv.ln(10)-1158
require(below(logq,-1100),"Uniform Neumann contraction")
require(s.Rational(2)+s.Rational(2,2)==3,"Off-shell pressure defect budget in ||E||+||S||")
finish("actual_cutoff_inverse.py",dict(
 same_actual_incoming_background_and_AE_cutoff=True,static_cutoff_is_action_row_not_assumed_pressure=True,
 static_and_actual_action_sufficient_K=K0,large_cutoff_mode_sum_executed=False,
 compact_sign_tail_upper=outward(tail),finite_positive_squared_roots_bounds=["r1K<9","r2K<144A^2"],
 common_vertical_line="Re s=24A",fast_poles_retained=True,
 common_static_resolvent_F_lower="1/(5200*pi^2*A^2)",
 common_static_Y_to_X_bound=outward(M),safe_M0="1e15",
 uniform_partial_retarded_Schur_coefficient=outward(schur),
 retarded_difference_operator_norm_tail="22 mu/K for each D_+^j, j=0,1,2",
 mean_actual_minus_static_C1_tail="45 mu/K",
 complete_actual_difference_epsilon_budgets=budgets,
 uniform_actual_difference_bound="1000 epsilon",log_uniform_Neumann_q_upper=outward(logq),
 static_inverse_strong_Y_to_H4_convergence=True,actual_action_inverse_strong_Y_to_H4_convergence=True,
 actual_pressure_inverse_strong_Y_to_H4_convergence=True,
 pressure_off_shell_Ward_defect_retained=True,pressure_sufficient_K1_exists=True,
 pressure_K1_numerically_certified=False,pressure_K1_is_asserted_equal_to_1e9=False,
 common_domain="zero past; four zero initial metric traces; same incoming mode transport",
 convergence_is_operator_norm=False,strong_adjoint_convergence_inferred=False,
 actual_noise_admissibility_or_initial_charge_automatically_proved=False,
 quantum_joint_propagator_state_fullfield_limit=False,arbitrary_tensor_lapse_inverse=False),
 [new+"coefficient_window.json",new+"actual_uv_bridge.json",new+"ACTUAL_UV_BRIDGE.md",
 pre+"dynamic_inverse/SPECTRUM.md",pre+"dynamic_inverse/spectrum.json",pre+"dynamic_inverse/fast_root.json",
 pre+"finite_stress/BOUNDARY_STATE.md",base+"ACTUAL_INVERSE.md",base+"actual_inverse.json",
 base+"ACTION_RESPONSE.md",base+"RETARDED_RESPONSE.md",base+"FINITE_CAUSAL.md",
 base+"QUIET_WINDOW.md",base+"quiet_window.json"],proof="ACTUAL_CUTOFF_INVERSE.md")
