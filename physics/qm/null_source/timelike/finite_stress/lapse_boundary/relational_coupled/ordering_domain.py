"""Exact ordering, ground-state and endpoint identities; analytic domains in proof."""
import sympy as s
from common import *
base="physics/qm/null_source/timelike/finite_stress/lapse_boundary/"
new=base+"relational_coupled/"
k=s.symbols("k",positive=True);a=s.symbols("alpha",positive=True)
eta=(a-1)**2-s.Rational(1,4)
f=s.Function("f")(k);psi=k**a*f
A=lambda z:-s.diff(k**(-s.Rational(1,2))*z,k,2)*k**(-s.Rational(1,2))+eta*k**-3*z
target=-k**(a-1)*s.diff(f,k,2)+(1-2*a)*k**(a-2)*s.diff(f,k)
require(s.simplify(A(psi)-target)==0,"Ground-state differential identity")
require(s.simplify(eta+ s.Rational(1,4)-(a-1)**2)==0,"Endpoint indicial roots")
nu=(a-1)*s.Rational(2,3)
require(s.simplify((-5+16*eta)/36-(nu**2-s.Rational(1,4)))==0,"Liouville inverse-square coefficient")
require(s.simplify(((a-1)**2-s.Rational(1,4)).subs(a,s.Rational(3,2)))==0,"Original congruence member")
require(s.simplify(eta.subs(a,s.Rational(5,2))-2)==0,"Limit-point threshold")
lam=s.symbols("lambda",positive=True);ff=s.exp(-lam*k*k/2)
require(s.simplify(s.diff(ff,k)+lam*k*ff)==0,"First CS equality profile")
# Critical log-ground-state identity; no use of H_0^1 at eta=-1/4.
x=s.symbols("x",positive=True);y=s.symbols("y",real=True)
F=s.Function("F");z=s.sqrt(x)*F(s.log(x))
expr=s.expand(s.diff(z,x)**2-z*z/(4*x*x))
require(s.simplify(x*expr-(F(s.log(x))*s.Subs(s.diff(F(y),y),y,s.log(x))+s.Subs(s.diff(F(y),y),y,s.log(x))**2))==0,"Critical logarithmic core form")
finish("ordering_domain.py",dict(
 ordering_parameter_range="eta >= -1/4",critical_domain_is_closed_ground_state_form=True,
 uncertainty="q_eta >= alpha^2 <kappa^-1>^2/<kappa> >= alpha^2/<kappa>^3",
 alpha="1+sqrt(1+4 eta)/2",bound_allows_entanglement_and_normal_mixtures=True,
 source_connection_commutes_with_geometry_moments=True,
 first_CS_bound_sharp=True,mean_only_constant_claimed_optimal=False,
 supercritical_semibounded_route_rejected=True,all_supercritical_selfadjoint_extensions_rejected=False,
 complete_positive_confining_finite_K_evolution_extended=True,
 unique_physical_ordering_selected=False),
 [new+"coefficient_window.json",new+"COUPLED_FORMS.md",new+"SNAPSHOT_DOMAIN.md",
 base+"RELATIONAL_DOMAIN.md"],proof="ORDERING_DOMAIN.md")
