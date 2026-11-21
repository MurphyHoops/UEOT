"""Actual-source boundary identities and exact ultraviolet coefficients."""
import sympy as s
from common import require,finish
t=s.symbols("t",real=True)
om,V0=s.symbols("omega V0",positive=True)
h=s.Function("h")(t);a=s.Function("a")(t)
x=s.Function("x")(t);q=s.Function("q")(t)
V=s.diff(h,t)+h*h
Q=x*x/2;D=s.diff(Q,t);H0=(s.diff(x,t)**2+om*om*x*x)/2
kg={s.diff(x,t,2):(V-om*om)*x}
lhs=(s.diff(Q,t,2)-3*h*D+(h*h-2*s.diff(h,t))*Q+H0).subs(kg)
rhs=s.Rational(3,2)*((s.diff(x,t)-h*x)**2-om*om*x*x/3)
require(s.expand(lhs-rhs)==0,"Exact oscillator pressure identity")
w=q/(3*V0*a**4)
ageom={s.diff(a,t,2):(s.diff(h,t)+h*h)*a,s.diff(a,t):h*a}
bulk=(s.diff(w,t,2)+3*h*s.diff(w,t)+V*w).subs(ageom)
target=(s.diff(q,t,2)-5*h*s.diff(q,t)+(5*h*h-3*s.diff(h,t))*q)/(3*V0*a**4)
require(s.simplify(bulk-target)==0,"Actual Q integral weight")
bQ=(s.diff(w,t)+3*h*w).subs(ageom)
require(s.simplify(bQ-(s.diff(q,t)-h*q)/(3*V0*a**4))==0,"Lower endpoint Q coefficient")
require(s.simplify(-w+q/(3*V0*a**4))==0,"Lower endpoint D coefficient")
# The pressure pair leading factor -omega/(3 V0 a^4) times the
# first two lower-endpoint Fourier terms q/(2 i omega), q'/(2 i omega)^2.
q0,q1,ai=s.symbols("q0 q1 ai",real=True,nonzero=True)
lead0=-om*q0/(3*V0*ai**4*2*s.I*om)
lead1=-om*q1/(3*V0*ai**4*(2*s.I*om)**2)
require(s.simplify(lead0+s.Rational(1,6)*q0/(s.I*V0*ai**4))==0,"Initial pressure amplitude")
require(s.simplify(lead1-q1/(12*V0*ai**4*om))==0,"First derivative pressure amplitude")
cubic=s.simplify(4*lead0*s.conjugate(lead0)/3)
linear=s.simplify(4*om**2*lead1*s.conjugate(lead1))
require(s.simplify(cubic-q0*q0/(27*V0**2*ai**8))==0,"K^3 variance coefficient")
require(s.simplify(linear-q1*q1/(36*V0**2*ai**8))==0,"K variance coefficient")
# Product identities behind the improved actual H0 envelope.
F,Fp=s.symbols("F Fp")
raw=(-s.I*om*F+Fp)**2+om*om*F**2
require(s.expand(raw-(-2*s.I*om*F*Fp+Fp*Fp))==0,"H0 leading pair cancellation")
finish("finite_source_domain.py",dict(
 actual_nonstatic_high_frequency_derivative_order_used=4,
 single_source_sharp_start_K_cubed_coefficient="q_i^2/(27*V0^2*a_i^8)",
 single_source_sharp_start_K_coefficient_when_q_i_zero="q_i_prime^2/(36*V0^2*a_i^8)",
 exact_finite_K_initial_block="(-q_i*delta_D_i+(q_i_prime-h_i*q_i)*delta_Q_i)/(3*V0*a_i^4)",
 combined_source_and_negative_initial_block_L2_limit=True,
 combined_pair_tail_power=-2,
 double_zero_condition_applies_to_source_term_separately=True,
 double_zero_claimed_necessary_for_full_joint_initial_data=False,
 initial_block_contains_the_source=True,
 this_block_derived_as_physical_geometry_preparation=False,
 standalone_sharp_boundary_operators_claimed_to_exist=False),
 ["dynamic_inverse/STATE_MATCHING.md","nonlinear_history/KERNELS.md",
  "finite_stress/lapse_boundary/TENSOR_NOISE.md",
  "finite_stress/lapse_boundary/RETARDED_RESPONSE.md",
  "finite_stress/lapse_boundary/FINITE_CAUSAL.md"],
 proof="FINITE_SOURCE_DOMAIN.md")
