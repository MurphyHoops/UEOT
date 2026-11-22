"""Explicit candidate ordering and selfadjoint finite-K principal reference."""
import sympy as s
from common import require,finish
k=s.symbols("k",positive=True);g=s.symbols("g",real=True,nonzero=True)
f=k**(-s.Rational(1,2));psi=s.Function("psi")(k)
P=lambda y:-s.I*s.diff(y,k)
A0=lambda y:f*P(P(f*y))
target=-s.diff(psi,k,2)/k+s.diff(psi,k)/k**2-3*psi/(4*k**3)
require(s.simplify(A0(psi)-target)==0,"Exact symmetric congruence ordering")
require(s.simplify(A0(k**s.Rational(1,2)))==0 and s.simplify(A0(k**s.Rational(3,2)))==0,"Two square-integrable endpoint branches")
x=s.symbols("x",positive=True);phi=s.Function("phi")
xx=s.Rational(2,3)*k**s.Rational(3,2)
lift=k**s.Rational(1,4)*phi(xx)
out=s.simplify(A0(lift)/k**s.Rational(1,4))
desired=-s.Subs(s.Derivative(phi(x),x,2),x,xx)-5*phi(xx)/(36*xx**2)
require(s.simplify(out-desired)==0,"Unitary Liouville inverse-square reference")
require(s.simplify(s.diff(xx,k)*k**(-s.Rational(1,2))-1)==0,"L2 Jacobian")
require(1-4*s.Rational(5,36)==s.Rational(4,9),"Strict Hardy form floor")
weyl_const=-s.Rational(1,4)*s.diff(1/k,k,2)
require(s.simplify((-3/(4*k**3)-weyl_const)/(2*g)+1/(8*g*k**3))==0,"Actual ordering ambiguity")
B,H,Q=s.symbols("B H Q",real=True)
Ak=B-H*k*k/4;phase=s.exp(s.I*(B*k-H*k**3/12+k*Q))
D=lambda y:P(y)-(Ak+Q)*y
require(s.simplify(D(phase*psi)-phase*P(psi))==0,"Finite-K connection transport sign")
p,q=s.symbols("p q",real=True)
require(s.expand((p+k*q)**2/2-p*p/2-k*p*q-k*k*q*q/2)==0,"Source H0 transport and Q cancellation")
uu,g0,u0=s.symbols("uu g0 u0",real=True)
gfun=g0+(uu-u0)/4
require(s.simplify(s.diff(2*s.log(gfun/g0),uu)-1/(2*gfun))==0,"Same-sign principal clock integral")
finish("relational_domain.py",dict(
 selected_principal_clock_unitary_propagator_constructed=True,
 explicit_candidate_kinematic_measure_and_ordering=True,
 original_classical_action_uniquely_fixes_quantum_ordering=False,
 constraint_congruence_confused_with_unitary_conjugation=False,
 principal_Liouville_potential="-5/(36*x^2)",
 principal_Hardy_form_lower="4/9 times norm(phi_prime)^2",
 principal_Friedrichs_selfadjoint_realization_constructed=True,
 kappa_zero_boundary_physically_unique=False,
 finite_K_source_connection_unitary_domain_transport=True,
 full_remaining_relational_operator_explicit=True,
 fixed_u_real_nonzero_principal_scalar_factor_selfadjoint=True,
 complete_relational_Hamiltonian_selfadjointness_proved=False,
 u_dependent_unitary_propagator_constructed=False,
 full_field_renormalized_operator_limit_proved=False,
 full_physical_inner_product_and_state_constructed=False),
 ["finite_stress/lapse_boundary/ACTION_LIFT.md",
  "finite_stress/lapse_boundary/QUANTUM_ENDPOINT.md",
  "finite_stress/lapse_boundary/INCOMING_PREPARATION.md"],
 proof="RELATIONAL_DOMAIN.md")
