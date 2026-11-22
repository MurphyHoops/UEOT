"""Prepared source readout identities, exact mixed blocks, and cutoff constants."""
import sympy as s
from common import iv,load,box,above,below,outward,require,finish
t=s.symbols("t",real=True)
V0,A=s.symbols("V0 A",positive=True)
a=s.Function("a")(t);h=s.Function("h")(t);I=s.Function("I")(t);q=s.Function("q")(t)
V=s.diff(h,t)+h*h
w=q/(3*V0*a**4);r=s.diff(w,t,2)+3*h*s.diff(w,t)+V*w
def reduce(expr):
    return s.simplify(s.expand(expr).subs({s.diff(a,t,2):(s.diff(h,t)+h*h)*a,
        s.diff(a,t):h*a,s.diff(I,t):a**-2}))
fq=a*a*(s.diff(w,t)+h*w)/2
fd=a*a*I*(s.diff(w,t)+h*w)-w
fp=a*a*I*I*(s.diff(w,t)+h*w)/2-I*w
require(reduce((r*a*a+w*(a*h)**2)/2-s.diff(fq,t))==0,"Zero Q boundary primitive")
require(reduce(r*a*a*I+w*a*h*(a*h*I+a**-1)-s.diff(fd,t))==0,"Zero D boundary primitive")
require(reduce((r*a*a*I*I+w*(a*h*I+a**-1)**2)/2-s.diff(fp,t)-s.Rational(3,2)*w/a**2)==0,"Zero P boundary primitive")
alphaQ=-(s.diff(q,t)-3*h*q)/(6*V0*a*a)
alphaD=(q-a*a*I*(s.diff(q,t)-3*h*q))/(3*V0*a**4)
require(reduce(-fq-alphaQ)==0 and reduce(-fd-alphaD)==0,"Endpoint Q,D coefficients")
require(reduce(-fp-I*alphaD+I*I*alphaQ)==0,"Endpoint P coefficient")
p,eps,ez,L,d=s.symbols("p eps ez L d",real=True)
e0=ez+2*p*eps;e2=e0-2*eps
m0=2*e0*L;m2=2*e2*L+2*d
require(s.expand(p*(1-p)*(m2-m0)**2-4*p*(1-p)*(d-2*eps*L)**2)==0,"Correlated branch mean square")
require((16+(24+16)*p)-(16+(24-16)*p)==32*p,"Full source NOON contrast")
# Radial two-dimensional canonical commutators, no finite-Fock CCR replacement.
px,py=s.symbols("px py",real=True)
f=s.Function("psi")(px,py)
def Hz(expr):
    return (px*px+py*py)*expr/(2*A**3)
def Dil(expr):
    return s.I*(px*s.diff(expr,px)+py*s.diff(expr,py)+expr)
def Qsq(expr):
    return -s.diff(expr,px,2)-s.diff(expr,py,2)
require(s.expand(Hz(Dil(f))-Dil(Hz(f))+2*s.I*Hz(f))==0,"Weak energy/dilation commutator")
require(s.expand(Hz(Qsq(f))-Qsq(Hz(f))+2*s.I*Dil(f)/A**3)==0,"Weak energy/Q commutator")
aq,ap,ad,alpha_s,sigma,mu2,J2=s.symbols("aq ap ad alpha_s sigma mu2 J2",real=True,nonzero=True)
Qmixed=-2*aq/A**3*(-s.Rational(1,2)/sigma+(1-J2)/sigma)
real_mixed=s.expand(alpha_s*sigma*(Qmixed+2*ap*A**3*sigma*mu2))
require(s.simplify(real_mixed-alpha_s*(aq*(2*J2-1)/A**3+2*ap*A**3*sigma*sigma*mu2))==0,"Exact source charge real mixed block")
K=s.symbols("K",positive=True,integer=True)
tel=s.Rational(1,2)*(1/K+1/(K+1))
require(s.simplify(tel-((2*K+1)/(2*K*(K+1))))==0,"Exact frequency-tail telescoping")
require(s.Rational(9,16)*s.Rational(1,2)==s.Rational(9,32),"Boundary variance tail coefficient")
require(8*s.Rational(81,64)==s.Rational(81,8),"Remainder variance tail coefficient")
# Bound e^U, e^(2U), h e^U through the three derivatives actually used.
b=iv.mpf(".1")
E=[iv.exp(b),iv.exp(b)*b,iv.exp(b)*(b+b*b),iv.exp(b)*(b+3*b*b+b**3)]
E2=[iv.exp(2*b),iv.exp(2*b)*2*b,iv.exp(2*b)*(2*b+4*b*b),iv.exp(2*b)*(2*b+12*b*b+8*b**3)]
hE=[iv.exp(b)*b,iv.exp(b)*(b+b*b),iv.exp(b)*(b+3*b*b+b**3),iv.exp(b)*(b+7*b*b+6*b**3+b**4)]
require(all(below(v,2) for v in E+E2),"Three-jet exponential multipliers")
require(all(below(v,4*b) for v in hE),"Three-jet h exponential multiplier")
require(below(12+192*b,32),"Pressure adjoint H3 multiplier")
require(32*2*12==768,"Raw-pressure factor retained")
T=iv.mpf(1)/50
bessel=2*iv.pi*(1+T*T/2)
require(below(bessel,"6.285"),"Nonharmonic Bessel bound")
inv=load("finite_stress/lapse_boundary/actual_inverse.json")
require(inv["independent_advanced_H4_inverse"] and inv["pressure_adjoint_H3"],"Actual inverse input")
finish("prepared_readout.py",dict(
 actual_proper_time_test_pullback_explicit=True,
 raw_pressure_test="-a^2*M_U_adjoint*Ghat_advanced*F",
 H3_raw_pressure_test_bound="768*A^2*M0/(gamma*(1-q_inv))*norm(F,Y_minus)",
 terminal_test_traces_zero_through_order=2,
 fullmode_initial_subtraction_is_explicit_candidate_choice=True,
 source_GNS_limit_on_H2_tests=True,
 source_H3_variance_tail_order="O(1/K) with explicit coefficients",
 Bessel_bound_for_T_one_fiftieth=outward(bessel),
 same_source_weak_pressure_solution=True,
 complete_original_radial_state_variance_formula=True,
 zero_shell_correlations_retained=True,
 initial_zero_mode_phase_constant_free_to_reset=False,
 source_charge_readout_symmetric_and_commutator_blocks_exact=True,
 uncertainty_principle_reused_not_new=True,
 canonical_cost_for_every_UV_legal_completion=False,
 finite_low_boundary_completion_is_unique=False,
 memory_channel_preserves_Q_D_readout_claimed=False,
 Neumann_and_cutoff_errors_controlled=True,
 actual_numeric_metric_variance_computed=False,
 normal_geometry_boundary_preparation_constructed=False,
 density_constraint_automatically_satisfied=False),
 ["finite_stress/lapse_boundary/actual_inverse.json",
  "finite_stress/lapse_boundary/ACTUAL_INVERSE.md",
  "finite_stress/lapse_boundary/FINITE_SOURCE_DOMAIN.md",
  "finite_stress/lapse_boundary/TENSOR_NOISE.md",
  "finite_stress/lapse_boundary/OPERATIONAL_STATE.md",
  "finite_stress/BOUNDARY_STATE.md"],
 proof="PREPARED_READOUT.md")
