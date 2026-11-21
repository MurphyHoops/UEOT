"""Exact identities and interval scope for the finite-K clock boundary."""
import sympy as s
from common import *
base="physics/qm/null_source/timelike/finite_stress/lapse_boundary/"
new=base+"relational_coupled/"
co=load(new+"coefficient_window.json");load(new+"all_sign_evolution.json")
load(new+"ordering_domain.json")
tau,t,k,nu=s.symbols("tau t k nu",real=True,positive=True)
f=s.Function("f")(k);phase=s.exp(-2*s.I*t*k*k)
A=lambda z:-s.diff(z,k,2)+(nu*nu-s.Rational(1,4))*z/k**2
target=phase*(A(f)+8*s.I*t*k*s.diff(f,k)+4*s.I*t*f+16*t*t*k*k*f)
require(s.simplify(A(phase*f)-target)==0,"Hankel product rule")
v=s.symbols("v",real=True)
anti=s.exp(v)*(v*v-2*v+3)
require(s.simplify(s.diff(anti,v)-s.exp(v)*(1+v*v))==0,"Integrable past residual")
require(s.limit(anti,v,-s.oo)==0,"Past antiderivative endpoint")
q,N=s.symbols("q N",positive=True);R=(N/q)**s.Rational(1,3)
require(s.simplify(2*s.sqrt(R*N*q)+3*N/R-5*q**s.Rational(1,3)*N**s.Rational(2,3))==0,"Fractional inverse-moment cutoff balance")
kap,alpha=s.symbols("kap alpha",positive=True)
F=s.Function("F")(kap)
require(s.simplify(s.diff(kap**(2*alpha-1)*F**2,kap)-(2*alpha-1)*kap**(2*alpha-2)*F**2-2*kap**(2*alpha-1)*F*s.diff(F,kap))==0,"Critical-safe integration by parts")
eps=s.symbols("eps",nonzero=True,real=True)
g=eps*s.exp(v)/4
require(s.simplify((eps*s.exp(v))/(2*g)-2)==0,"Exact logarithmic kinetic coefficient")
x=s.symbols("x",positive=True);fp=s.Function("fp")(x)
Ax=lambda z:-s.diff(z,x,2)+(nu**2-s.Rational(1,4))*z/x**2
Dx=lambda z:-s.I*(x*s.diff(z,x)+z/2)
require(s.simplify(s.I*(Ax(x*x*fp)-x*x*Ax(fp))-4*Dx(fp))==0,"Geometry commutator")
require(s.Rational(8,3)+s.Rational(16,3)==8,"Polynomial energy exponent")
require((8+2)//2==5 and 5+1==6,"Fixed-form and interaction exponents")
require(s.Rational(4,3)*144==192 and s.Rational(4,3)*s.Rational(20,3)==s.Rational(80,9),"Comparison commutator constants")
require(s.simplify(s.limit(s.exp(-s.symbols("n",positive=True)/2)*s.symbols("n",positive=True)**6,s.symbols("n",positive=True),s.oo))==0,"Summable interpolation summand vanishes")
# Use the already outward-rounded coefficient intervals over u in [-.01,.01].
# Subtracting J/4 widens the actual g(0) enclosure, which remains sufficient.
J=interval("-.01",".01")
bounds={}
for K,z in [("65536",box(co["g_on_patch"])),("131072",box(co["negative_controls"]["131072"]["g"]))]:
    uc=-4*(z-J/4);bounds[K]=outward(uc)
    require(below(uc,"-.01") or above(uc,".01"),"Boundary outside certified quiet window")
finish("g_zero_boundary.py",dict(
 scope="fixed finite K; kappa>0; fixed eta>=-1/4; declared Friedrichs realization; either side of g=0",
 boundary_u_enclosures=bounds,all_scalar_counterterms_and_fixed_U0_retained=True,
 full_coupled_wave_operators_complete=True,
 forward_and_reverse_strong_limits_are_mutual_unitaries=True,
 normal_state_bounded_kappa_probability_tends_to_zero=True,
 positive_kappa_moments_diverge_in_extended_sense=True,
 same_slice_normal_trace_norm_boundary_limit=False,
 phase_corrected_scattering_chart_exists=True,
 physical_two_side_boundary_identification_selected=False,
 original_snapshot_strong_domain_assumed=False,
 critical_endpoint_included=True,
 polynomial_comparison_energy_power=8,fixed_form_norm_power=5,interaction_form_norm_power=6,
 spatial_K_limit_proved=False,curvature_singularity_claimed=False),
 [new+"coefficient_window.json",new+"all_sign_evolution.json",new+"ordering_domain.json",
 new+"REFERENCES.md",base+"RELATIONAL_DOMAIN.md"],proof="G_ZERO_BOUNDARY.md")
