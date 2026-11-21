"""Actual negative-branch raw source cube and controlled/large-tail gates."""
import sympy as s
from common import *
pre="physics/qm/null_source/timelike/";base=pre+"finite_stress/lapse_boundary/";new=base+"relational_coupled/"
co=load(new+"coefficient_window.json");gm=load(new+"geometric_momentum.json")
sb=load(new+"source_budgets.json");bs=load(pre+"finite_stress/boundary_state.json")
load(base+"actual_inverse.json");load(base+"quiet_window.json")
require(sb["log_initial_h_strict_upper"]==-19980,"Same actual quiet initial expansion")
K=131072;d=K*(K+1)*(2*K+1)//3-2
M={n:10**12+10*K*(n+d*(2*n+3)//2) for n in [2,4,6]}
require(all(m<10**23 for m in M.values()),"Three actual occupation-support norms")
product=M[2]*M[4]*M[6]
require(product<10**69 and below(69*iv.ln(10),160),"Finite raw cube bound")
A=box(co["frozen_A"]);U0=box(co["frozen_U0"]);n=iv.mpf(K)
H=iv.ln(n)+iv.euler+1/(2*n)-1/(12*n*n)+1/(120*n**4)+interval(-1,0)/(252*n**6)
C=19+15*(iv.ln(A*A/4)+2*iv.euler);BK=-(K*(K+1)+H)/4
require(below(H,13) and below(-BK,"1e10") and below(C,400),"Recheck momentum constants at K131072")
g=C/120-H/4;b0=-1/(2*g);V0=2*iv.pi**2
can=(C-1)/240;Cr=iv.mpf(K*(K+1)*(K*(K+1)-1))/4-H/8
d0=V0*A**4*U0-3*V0*A*A/2-can-Cr
d1=3*V0*A*A/2-g+iv.mpf(K*(K+1))/4+iv.mpf(29)/120
d3=iv.mpf(59)/720-g/2
require(below(g,0) and above(b0,3) and below(b0,4),"Actual negative kinetic coefficient")
require(above(d3,".14") and below(d3,1) and above(d1) and below(d1,iv.exp(30)),"Actual scalar tail coefficients")
require(below(d0,0) and below(-d0,iv.exp(50)),"All fixed U0 and vacuum scalar terms retained")
require(below(iv.ln(iv.mpf("6.3e11"))-1158,-1130),"Rechecked pure geometry reference budget")
h=iv.exp(-19980)
require(below(iv.mpf("2.3")*h**6+iv.mpf(".02")*iv.exp(160)*h**3,1),"Controlled-tail contradiction")
require(below(iv.exp(iv.mpf(160)/3)+iv.exp(50),iv.exp(60)),"Fixed old raw mean plus d0 bound")
require(below(8*iv.exp(-iv.mpf(2)/3),10),"Explicit normalized geometry bump derivative")
require(s.Rational(512,3)*200+s.Rational(1000,9)*200+1<60000,"Bump q constant")
require(s.Rational(512,27)+s.Rational(1000,729)<21,"Bump ordering coefficient")
hh,RR,qs,ql,Q=s.symbols("h R qs ql Q",positive=True)
w=hh/(2*RR-hh)
require(s.simplify((1-w)*hh/2+w*RR-hh)==0,"Exact same expansion mean")
Rup=10*s.sqrt(Q)/hh**2
lower=-4*qs/hh**3-3*s.exp(60)/hh+s.Rational(7,100)*hh*RR**2-2*s.exp(60)*hh/RR**2-4*ql*hh/RR**4
target=7*Q-4*qs-3*s.exp(60)*hh**2-s.exp(60)*hh**8/(50*Q)-ql*hh**12/(2500*Q**2)
require(s.simplify(lower.subs(RR,Rup)*hh**3-target)==0,"Finite large-tail upper bracket")
require(below(3*iv.exp(60)*h*h+iv.mpf(".02")*iv.exp(60)*h**8/60000+iv.mpf(".0004")*h**12/60000,1),"Strict upper-bracket remainder")
require(below(3*iv.exp(60)*h*h+iv.exp(30)*h**4+h**6,1),"Strict low-packet sign budget")
require(below(h**6+iv.mpf(".02")*iv.exp(160)*h**3,iv.mpf(".4")),"Large-tail necessary lower resource margin")
finish("negative_recovery.py",dict(
 actual_K=K,real_nonzero_mode_count=d,occupation_support_norm_bounds={str(n):M[n] for n in M},
 raw_source_cube_integer_bound=product,raw_source_cube_log_upper=160,
 raw_source_cube_is_same_original_phi_marginal=True,
 kinetic_b0=outward(b0),g_at_initial=outward(g),d0_at_initial=outward(d0),
 d1_at_initial=outward(d1),d3_at_initial=outward(d3),
 actual_larger_K_momentum_budget_reverified=True,
 old_Pi_reference_abs_upper="exp(-1130)",old_log_h_upper=-19980,
 unchanged_raw_source_and_T3_le_2h3_recovery="REJECTED in stated combined-budget/mean domain",
 arbitrary_mixed_entangled_states_allowed_in_rejection=True,
 normal_common_core_initial_state_with_same_raw_source_and_two_geometric_means_exists=True,
 witness_joint_rank_at_most=2,root_bracket="1<R*<10*sqrt(60000+21*abs(eta-3/4))*h^-2",
 root_defined_once_by_continuity_not_reselected_in_time=True,
 witness_T3_lower="h^-3/2",witness_R_lower="h^-2/3",witness_variance_lower="h^-1/12",
 log_variance_strict_lower=outward(19980-iv.ln(12)),
 log_relative_variance_strict_lower=outward(3*19980-iv.ln(12)),
 full_old_mean_history_recovered=False,semiclassical_geometry_recovered=False,
 autonomous_preparation_constructed=False,source_cube_is_renormalized_continuum_energy=False),
 [new+"coefficient_window.json",new+"geometric_momentum.json",new+"source_budgets.json",
 new+"all_sign_evolution.json",base+"ACTUAL_INVERSE.md",base+"actual_inverse.json",
 base+"QUIET_WINDOW.md",base+"quiet_window.json",base+"ACTION_LIFT.md",
 pre+"finite_stress/BOUNDARY_STATE.md",pre+"finite_stress/boundary_state.json"],
 proof="NEGATIVE_RECOVERY.md")
