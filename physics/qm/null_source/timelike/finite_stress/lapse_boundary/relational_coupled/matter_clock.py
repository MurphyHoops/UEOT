"""Exact action, boundary, spectral-sign and positive-clock identities."""
import sympy as s
from common import *
base="physics/qm/null_source/timelike/finite_stress/lapse_boundary/"
new=base+"relational_coupled/"
load(new+"coupled_forms.json");load(new+"geometric_momentum.json")
u,k,T=s.symbols("u k T",real=True)
A,g,B,H,n=s.symbols("A g B H n",real=True,nonzero=True)
a=A*s.exp(u);AK=B-H*k*k/4
f=s.Function("f")(u,k);Pu=lambda z:-s.I*s.diff(z,u)
Pk=lambda z:-s.I*s.diff(z,k)
Dk=lambda z:Pk(z)-AK*z
require(s.simplify(-2*a*k*Pu(a*f)+(k*a*a*Pu(f)+Pu(k*a*a*f)))==0,"Symmetric congruence u term")
require(s.simplify(-2*a*Dk(Dk(a*f))/(2*g)+(a*a/g)*Dk(Dk(f)))==0,"Congruence kinetic square")
require(s.simplify(AK.subs(k,-k)-AK)==0,"Conjugation-reflection preserves even connection")
d0,d1,d3=s.symbols("d0 d1 d3",real=True)
V=d0+d1*k*k+d3*k**4
require(s.simplify(V.subs(k,-k)-V)==0,"Even geometric scalar potential")
R_u=lambda z:-(k*a*a*Pu(z)+Pu(k*a*a*z))
phase=s.exp(s.I*n*u)
require(s.simplify(R_u(phase*f)-phase*R_u(f)+2*n*a*a*k*phase*f)==0,"Both spectral signs on every extension")
# Boundary Lagrange identity, with conjugate test represented independently.
v=s.Function("v")(u);w=s.Function("w")(u);b=k*a*a
Ru=lambda z:s.I*(2*b*s.diff(z,u)+s.diff(b,u)*z)
Ru_bar=lambda z:-s.I*(2*b*s.diff(z,u)+s.diff(b,u)*z)
require(s.simplify(v*Ru(w)-Ru_bar(v)*w-2*s.I*s.diff(b*v*w,u))==0,"Exact endpoint boundary form")
om=s.symbols("omega",positive=True)
sol=s.exp(s.I*om*T)/s.sqrt(2*om)
require(s.simplify(-s.I*s.diff(sol,T)-om*sol)==0,"Positive clock momentum sign")
current=-s.I*(s.conjugate(sol)*s.diff(sol,T)-s.diff(s.conjugate(sol),T)*sol)
require(s.simplify(current-1)==0,"Positive KG current normalization")
require(s.simplify(-s.diff(sol,T,2)-om**2*sol)==0,"Quadratic constraint solution")
# Symbolic integral by parts multiplier, not numerical group averaging.
kk,lam=s.symbols("clock_k lambda",real=True)
require((kk**2-lam).subs(lam,kk**2)==0,"Mass-shell annihilation multiplier")
finish("matter_clock.py",dict(
 finite_K_original_phi_action_retained=True,ordering_eta=0,kappa_domain="whole real line",
 geometric_u_patch="bounded open interval whose closure avoids g_K=0",
 selfadjoint_spatial_extensions_exist=True,deficiency_indices=["countably infinite","countably infinite"],
 selfadjoint_extension_uniquely_selected=False,explicit_deficiency_basis_computed=False,
 every_extension_spectrum_unbounded_both_directions=True,
 nonzero_finite_positive_spectral_band_exists=True,preassigned_band_nonempty_claimed=False,
 original_kinematic_constraint_selfadjoint_realization=True,
 kinematic_zero_eigenspace_empty=True,zero_is_continuous_spectrum=True,
 positive_normal_solution_space=True,explicit_positive_constraint_annihilating_rigging_form=True,
 compact_test_rigging_range="dense; no surjectivity claimed",
 positive_clock_phase="exp(+i Omega (T-T0)) for P_T=-i partial_T",
 positive_band_Abel_group_average_of_original_C_identified=True,
 gauge_invariant_test_orbit_and_rigging_extension=True,
 Abel_scope="bounded a-congruence, selected extension, positive Fourier interval away zero",full_RA_Q_observable_intertwining_claimed=False,
 same_old_bare_source_embedded=False,same_old_mean_history_recovered=False,
 u_clock_quantization_equivalence_proved=False,autonomous_clock_instrument_constructed=False),
 [new+"coupled_forms.json",new+"geometric_momentum.json",new+"REFERENCES.md",
 base+"ACTION_LIFT.md",base+"ENDPOINT_DOMAIN.md"],proof="MATTER_CLOCK.md")
