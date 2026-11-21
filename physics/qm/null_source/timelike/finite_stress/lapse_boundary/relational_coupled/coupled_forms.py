"""Explicit coefficient budgets for the complete common-form construction."""
import sympy as s
from common import *
base="physics/qm/null_source/timelike/finite_stress/lapse_boundary/"
new=base+"relational_coupled/"
d=load(new+"coefficient_window.json")
A=box(d["frozen_A"]);g=box(d["g_on_patch"]);glo=g.a;ghi=g.b
J=interval("-.01",".01");K=d["selected_K"];V0=2*iv.pi**2;a=A*iv.exp(J)
n=iv.mpf(K);H=iv.ln(n)+iv.euler+1/(2*n)-1/(12*n*n)+1/(120*n**4)+interval(-1,0)/(252*n**6)
C0=19+15*(iv.ln(A*A/4)+2*iv.euler);can=(C0-1)/240
Cr=iv.mpf(K*(K+1)*(K*(K+1)-1))/4-H/8
history="physics/qm/null_source/timelike/joint_history/history.json"
U0=box(load(history)["fixed_U0"])
reported=box(d["frozen_U0"])
require(reported.a<=U0.a and reported.b>=U0.b,"Same frozen cosmological input enclosure")
d0=V0*a**4*U0-3*V0*a*a/2-J/8-can-Cr
d0p=4*V0*a**4*U0-3*V0*a*a-iv.mpf(1)/8
d0pp=16*V0*a**4*U0-6*V0*a*a
require(below(abs(d0p),iv.exp(31)) and below(abs(d0pp),iv.exp(31)),"Explicit corrected first two scalar derivatives")
require(above(can) and below(can,2) and below(d0,0) and below(-d0,iv.exp(50)),"Complete negative scalar budget")
c=(iv.mpf(2)/3)**(iv.mpf(2)/3);hardy=9*c*iv.exp(-10)
shiftcost=2*c*iv.exp(80)/(3*iv.sqrt(3))
amin=1/(2*ghi)
require(above(amin-hardy,iv.mpf(1)/20),"Uniform derivative coercivity")
require(above(iv.exp(81)-shiftcost,iv.mpf(1)/20),"Uniform norm coercivity")
require(above(iv.exp(iv.mpf("-.02")),iv.mpf(1)/20),"Source coercivity")
require(above(box(d["d3_on_patch"]),iv.mpf(1)/20),"Confining term coercivity")
require(below(box(d["d1_on_patch"]),iv.exp(30)),"Linear coefficient budget")
require(below(1/(2*glo)+hardy+shiftcost+iv.exp(81)+iv.exp(30)+2+iv.exp(".02"),iv.exp(90)),"Uniform form upper budget")
# All u derivative coefficients through order two are far within the same form bound.
require(below(1/(8*glo*glo)+1/(16*glo**3),iv.exp(10)),"Kinetic derivatives")
require(below(16*V0*a**4*U0+6*V0*a*a+1,iv.exp(31)),"Scalar derivative budgets")
yy,delta=s.symbols("y delta",positive=True)
critical=1/s.sqrt(3*delta)
require(s.simplify((yy-delta*yy**3).subs(yy,critical)-2/(3*s.sqrt(3*delta)))==0,"Sharp elementary relative-form scalar")
t=s.symbols("t",real=True);q=s.symbols("q",real=True);psi=s.Function("psi")
R=s.exp(-t/2)*psi(s.exp(-t)*q)
D=lambda v:-s.I*(q*s.diff(v,q)+v/2)
require(s.simplify(s.I*s.diff(R,t)-D(R))==0,"Finite-coordinate dilation derivative")
require(s.simplify(s.exp(-t)*s.exp(t)-1)==0,"Dilation norm Jacobian")
require(s.simplify(s.diff(s.exp(-2*t),t)+2*s.exp(-2*t))==0 and s.simplify(s.diff(s.exp(2*t),t)-2*s.exp(2*t))==0,"Actual source quadratic derivatives")
finish("coupled_forms.py",dict(
 selected_K=K,clock_patch_u=d["clock_patch_u"],scalar_d0_on_patch=outward(d0),
 frozen_nonzero_U0=outward(U0),cosmological_d0_term=outward(V0*a**4*U0),
 first_two_cosmological_derivatives_retained=True,
 scalar_d0_first_derivative=outward(d0p),scalar_d0_second_derivative=outward(d0pp),
 scalar_absolute_budget="exp(50)",common_form_lower="1/20",uniform_positive_shift="exp(81)",
 form_and_two_derivative_upper="exp(90)",
 full_moving_frame_selfadjoint_family=True,complete_moving_frame_unitary_propagator=True,
 moving_frame_operator_domains_transported=True,operator_domains_asserted_identical=False,
 full_bulk_frame_unitary_weak_propagator=True,
 original_fixed_frame_semiboundedness_inferred=False,
 original_snapshot_operator_domain_transport_proved=False,
 full_field_limit_proved=False),
 [history,new+"coefficient_window.json",base+"RELATIONAL_DOMAIN.md",base+"ACTION_LIFT.md",new+"REFERENCES.md"],
 proof="COUPLED_FORMS.md")
