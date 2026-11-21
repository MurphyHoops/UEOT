"""Source-bound finite-slice and preparation resource budgets."""
import sympy as s
from common import *
p="physics/qm/null_source/timelike/";base=p+"finite_stress/lapse_boundary/";new=base+"relational_coupled/"
hist=load(p+"joint_history/history.json");thin=load(p+"finite_stress/boundary_state.json")
fast=load(p+"dynamic_inverse/fast_root.json");quiet=load(base+"quiet_window.json");actual=load(base+"actual_inverse.json")
A=box(hist["cases"]["unfiltered"]["A"]);sig=box(thin["example_sigma"]);Ez=box(thin["mean_unfiltered_zero_energy"]);prob=box(thin["shell_N2_probability"])
require(above(A,80000) and below(A,100000) and above(sig,"2e-7") and below(sig,"2.2e-7"),"Actual A and thin width")
require(above(Ez,800000) and below(Ez,1000000) and above(prob) and below(prob,1),"Actual source energy and shell")
require(quiet["new_initial_slow_amplitude_exact"]=="exp(-20000)","Same once-selected quiet amplitude")
require(actual["background_norm_upper_symbolic"]=="exp(-1158)","Same actual history bound")
sf=box(fast["fast_conformal_growth_rate"]);slow=box(fast["old_positive_root_reused"])
require(above(sf,936000) and below(sf,937000) and below(slow,3),"Frozen roots")
bump1=iv.exp(iv.mpf(4)/3)*8*iv.exp(-2)
bump2=iv.exp(iv.mpf(4)/3)*(4*4**4*iv.exp(-4)+12*3**3*iv.exp(-3)+6*2**2*iv.exp(-2))
require(below(bump1,10) and below(bump2,200),"Explicit normalized bump derivative budgets")
emax=Ez+2*iv.sqrt(3)/A+sig
require(below(emax,1000000),"Full zero energy support")
zq=iv.sqrt(2)*2/(iv.mpf(80000)**3)*(10/iv.mpf("2e-7")+emax*200/iv.mpf("2e-7")**2)
zd=1+iv.sqrt(2)*2*emax*10/iv.mpf("2e-7")
zp=2*iv.mpf(100000)**3*emax
require(below(zq,"1e8") and below(zd,"1e15") and below(zp,"1e22"),"W7 support-vector norms rechecked")
I=iv.mpf("1e-14")
qz=iv.mpf("5e9")*(iv.mpf("1e8")+2*I*iv.mpf("1e15")+I**2*iv.mpf("1e22"))
require(below(qz,"1e18"),"Actual transported zero Q norm")
K=100000
M=iv.mpf(3)*K*(K+1)/2;V=iv.mpf(16)*K/3
qosc=iv.sqrt(M*M+V)+10
require(below(qosc,"2e10") and below(qz+qosc,"1e19") and below(iv.mpf("1e19"),iv.exp(50)),"All modes Q second moment budget")
dn=6*(iv.mpf(K*(K+1)*(2*K+1))/6+2)
require(below(dn,"3e15") and below(iv.mpf("5e15"),iv.exp(40)),"Actual dilation mean")
Jn=iv.mpf("1e15")+I*iv.mpf("1e22");Ln=iv.mpf("1e22")/(2*80000**2)
require(below(Jn,"2e15") and below(Ln,"1e12"),"Polynomial source flow coefficients")
delta=iv.mpf("1e-6")
qprepared=iv.mpf("1e19")+iv.mpf("2e15")/(2*delta)+iv.sqrt(3)*iv.mpf("1e12")/(4*delta**2)
require(below(qprepared,iv.exp(60)),"Same original incoming preparation source budget")
c=iv.exp(-20000);eps=iv.exp(-1158)
require(below(iv.exp(202)*c,1),"Initial nonlinear E4 remainder less than c")
hcoef=iv.mpf("1.1")*sf+1
hpcoef=iv.mpf(".9")*sf**2-9-1
ratio=hpcoef/hcoef
require(above(ratio,500000) and below(iv.ln(hcoef)-20000,-19980),"Positive derivative ratio and logarithmic h budget")
# Full old canonical target, with all counterterm derivatives retained.
Cmax=400;Hmax=13;BKmax=iv.mpf("1e10")
ct=2*eps*(BKmax+Hmax*2*eps/4)+(Cmax+29)*eps/60+(3*Cmax+59)*eps**3/180+Hmax*3*eps/4+(30*eps**2+Cmax*eps)/120
require(below(ct,iv.mpf("3e10")*eps),"Counterterm momentum budget")
pu=3*20*iv.mpf("1e10")*eps+ct+2*eps*iv.mpf("1e19")+iv.mpf("5e15")
require(below(pu,iv.exp(60)),"Same bulk Pu target budget")
n,z=s.symbols("n z",real=True)
shell=(n+4)**2+s.Rational(1,4)*(2*z+4*n+16)
require(shell.subs({n:0,z:0})==20 and shell.subs({n:2,z:16})==50 and shell.subs({n:2,z:0})==42,"Exact non-Gaussian shell fourth moment")
# Exact radial variance lower bound used by the subsequent preparation gate.
mu2lower=iv.exp(-iv.mpf(2)/3)/64
require(above(mu2lower,iv.mpf(1)/128),"Elementary bump variance lower bound")
finish("source_budgets.py",dict(
 finite_K_max_for_budgets=100000,original_Q_second_moment_sqrt_upper="exp(50)",
 original_Q_second_moment_sqrt_power_bound="1e19",
 prepared_delta0="1e-6",prepared_Q_second_moment_sqrt_upper="exp(60)",
 all_nonzero_Q_GNS_norm_upper="2e10",exact_k2_Q_squared_coefficients=[20,50,42],
 same_source_zero_shell_cross_not_discarded=True,
 original_bulk_Pu_target_abs_upper="exp(60)",log_initial_h_strict_upper=-19980,
 initial_h_prime_over_h_strict_lower=500000,certified_ratio_coefficient=outward(ratio),
 arbitrary_pointer_Q_bound="1e19+2e15*x+1e12*x^2; x=(E t^4)^(1/4)",
 Gaussian_source_Q_bound=outward(qprepared),source_flow_same_input_nonselective_equivalence_only=True,
 elementary_mu2_lower=outward(mu2lower),apparatus_energy_identification=False),
 [p+"joint_history/history.json",p+"finite_stress/boundary_state.json",p+"dynamic_inverse/fast_root.json",
 base+"quiet_window.json",base+"actual_inverse.json",base+"READOUT_WITNESS.md",base+"readout_witness.py",
 base+"QUIET_WINDOW.md",base+"ACTUAL_INVERSE.md",base+"INCOMING_PREPARATION.md",
 base+"incoming_preparation.json",base+"ACTION_LIFT.md",
 p+"finite_stress/GEOMETRY_MATCHING.md"],proof="SOURCE_BUDGETS.md")
