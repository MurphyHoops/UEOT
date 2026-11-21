"""Exact fixed-AE trace/action identities; no predecessor imports or ODE."""
import sympy as s
from common import require,finish
t=s.symbols("t",real=True)
h=s.Function("h")(t);V=s.Function("V")(t);X=s.Function("X")(t)
om=s.symbols("omega",positive=True)
def duad(expr):
    return s.diff(expr,t,2)-2*s.diff(h*expr,t)
def reduce(expr):
    return s.simplify(s.expand(expr).subs(s.diff(h,t),V-h*h))
e=s.diff(X,t,2)/2-s.diff(h*X,t)+2*om**2*X
p=s.diff(X,t,2)/2-s.diff(h*X,t)+s.Rational(2,3)*om**2*X
require(s.simplify(-e+3*p-duad(X))==0,"Bare trace identity")
Ae=h*h/2;Ap=Ae-V/3
Ce=V*V/8+h*h*V/4-h*s.diff(V,t)/4
Cp=-V*V/8+h*h*V/4-h*s.diff(V,t)/4+s.diff(V,t,2)/12
ed=om+Ae/om+Ce/om**3
pd=om/3+Ap/om+Cp/om**3
require(reduce(ed-3*pd+duad(1/(2*om)+V/(4*om**3)))==0,"Omega subtractor trace")
K1,K3=s.symbols("K1 K3")
require(reduce((-Ae+3*Ap)*K1+(-Ce+3*Cp)*K3-duad(K1/2+K3*V/4))==0,"Exact omega-to-k conversion")
E1=Ae-s.Rational(1,2);P1=Ap-s.Rational(1,6)
E3=Ce+Ae/2-s.Rational(1,8);P3=Cp+Ap/2-s.Rational(1,24)
require(reduce(E1-3*P1+E3-3*P3-duad(-s.Rational(3,4)-V/4))==0,"Reference k=1 retained")
eps=s.symbols("eps")
w=s.Function("w")(t);Q=s.Function("Q")(t)
var=s.diff(s.diff(Q,t,2)-2*s.diff((h+eps*s.diff(w,t))*Q,t),eps)
require(s.simplify(var+2*s.diff(Q*s.diff(w,t),t))==0,"Action seagull variation")
a,V0,rho0,U0=s.symbols("a V0 rho0 U0",positive=True)
zero=s.diff(2*V0*a**4*s.exp(4*eps*w)*rho0*s.exp(-6*eps*w),eps).subs(eps,0)
vac=s.diff(-4*V0*a**4*s.exp(4*eps*w)*U0,eps).subs(eps,0)
require(s.simplify(zero+4*V0*a**4*rho0*w)==0,"Zero-mode action variation")
require(s.simplify(vac+16*V0*a**4*U0*w)==0,"U0 action variation")
# Noncommuting expansion: d is D^2, b=2hD, c=-2D(h.).
d,b,c,k,r=s.symbols("d b c k r",commutative=False)
lhs=(d+c)*(k+r)*(d+b)-d*k*d
rhs=d*k*b+c*k*d+c*k*b+(d+c)*r*(d+b)
require(s.expand(lhs-rhs)==0,"Exact principal comparison identity")
z=s.symbols("z",positive=True)
tau=s.symbols("tau",positive=True)
transform=s.integrate(s.exp(-z*tau)*s.sin(2*om*tau)/(2*om**2),(tau,0,s.oo))
require(s.simplify(transform-1/(om*(z*z+4*om*om)))==0,"Retarded Q sign and normalization")
finish("action_response.py",dict(
 fixed_AE_trace_Q_rewrite=True,
 reference_k1_and_omega_to_k_conversion_retained=True,
 full_two_field_thermal_coefficient=8,
 zero_mode_U0_and_dynamic_log_contacts_retained=True,
 causal_Q_kernel="2*theta(t-s)*Im(conj(v(t))^2*v(s)^2)",
 static_Q_Laplace_symbol="1/(omega*(z^2+4*omega^2))",
 action_pressure_relation="H_U/(3*V0*A^2)=exp(2U)*(I+J_U/2)*L_U; zero initial charge",
 noncommuting_principal_comparison_exact=True,
 relative_norm_smaller_than_one_proved=False,
 actual_all_field_causal_inverse_proved=False,
 retarded_kernel_claimed_time_symmetric=False,
 new_finite_renormalization_choice=False),
 ["nonlinear_history/KERNELS.md",
  "finite_stress/lapse_boundary/ACTION_BOUNDARY.md",
  "finite_stress/lapse_boundary/RETARDED_RESPONSE.md",
  "finite_stress/lapse_boundary/CAUSAL_DOMAINS.md"],
 proof="ACTION_RESPONSE.md")
