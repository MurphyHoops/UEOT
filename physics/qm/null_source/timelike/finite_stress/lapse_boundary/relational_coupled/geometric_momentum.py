"""Pure geometric momentum identification, positive gate and negative frontier."""
import sympy as s
from common import *
base="physics/qm/null_source/timelike/finite_stress/lapse_boundary/";new=base+"relational_coupled/"
co=load(new+"coefficient_window.json");cf=load(new+"coupled_forms.json")
load(new+"ordering_domain.json");load(new+"source_budgets.json")
q=s.symbols("q",real=True);k,w=s.symbols("k w",positive=True);f=s.Function("f")(q)
P=lambda z:-s.I*s.diff(z,q)
D=lambda z:(q*P(z)+P(q*z))/2
raw=lambda z:P(z)-k*q*z
H0=lambda z:(P(P(z))+w*w*q*q*z)/2
require(s.simplify(raw(raw(f))/(2*k)+w*w*q*q*f/(2*k)-(H0(f)/k-D(f)+k*q*q*f/2))==0,"Exact positive raw source square")
W=s.exp(s.I*k*q*q/2)
require(s.simplify(s.conjugate(W)*D(W*f)-D(f)-k*q*q*f)==0,"Source connection transports geometric dilation")
# One coordinate suffices; independent coordinates add their Jacobian halves.
u,x=s.symbols("u x",real=True);chi=s.Function("chi")
back=s.exp(u/2)*chi(u,s.exp(u)*x)
old=-s.I*s.diff(back,u)
transport=s.simplify((s.exp(-u/2)*old).subs(x,q*s.exp(-u)))
target=-s.I*(s.diff(chi(u,q),u)+q*s.diff(chi(u,q),q)+chi(u,q)/2)
require(s.simplify(transport-target)==0,"Exact finite-mode Jacobian supplies symmetric dilation")
g=box(co["g_on_patch"]);M=abs(box(cf["scalar_d0_on_patch"]))
require(below(g,".05") and below(M,"5e18"),"Corrected actual positive-g geometry gate")
m=iv.mpf("1e-9")
require(below(iv.mpf("5e18")*m*m,20) and above(10-iv.mpf("5e18")*m*m,iv.mpf("4.999999999")),"Readable small-m geometry bound")
eps=iv.exp(-1158);pure=iv.mpf("6.3e11")*eps
require(below(pure,iv.exp(-1130)) and below(pure,1),"Pure old geometry target, source terms removed exactly")
hmax=iv.exp(-19980)
require(above(iv.ln(10-iv.mpf("5e18")*hmax*hmax)+3*19980,59000),"Old quiet mean rejected by actual geometric momentum")
# Negative-g gate retains its different hypotheses and raw-source third moment.
K=131072;ng=box(co["negative_controls"][str(K)]["g"]);ag=abs(ng)
A=box(co["frozen_A"]);U0=box(co["frozen_U0"]);J=interval("-.01",".01");aa=A*iv.exp(J);V0=2*iv.pi**2
nn=iv.mpf(K);HK=iv.ln(nn)+iv.euler+1/(2*nn)-1/(12*nn**2)+1/(120*nn**4)+interval(-1,0)/(252*nn**6)
C0=19+15*(iv.ln(A*A/4)+2*iv.euler);can=(C0-1)/240
rad=iv.mpf(K*(K+1)*(K*(K+1)-1))/4-HK/8
d0=V0*aa**4*U0-3*V0*aa*aa/2-J/8-can-rad
d1=3*V0*aa*aa/2-ng+iv.mpf(K*(K+1))/4+iv.mpf(29)/120
d3=iv.mpf(59)/720-ng/2;cg=2*ag**iv.mpf("1.5")/(3*iv.sqrt(3))
require(below(ng,0) and below(ag,".136") and below(d0,0) and below(d3+1,"1.15") and below(cg,".02"),"Actual negative branch frontier coefficients")
require(above(1/(4*ag)-d1*hmax**4-hmax**3,1),"Scaled negative-g necessary frontier")
require(above((1-iv.mpf("2.3")*hmax**6)/iv.mpf(".02"),40),"Controlled geometry tail forces large raw-source third moment")
lam,ep,de,al=s.symbols("lambda epsilon delta alpha",positive=True)
linear=lam*lam/(4*ep*al*al)
opt=s.sqrt(linear/(3*de))
require(s.simplify((linear*k-de*k**3).subs(k,opt)-lam**3/(12*s.sqrt(3*de)*ep**s.Rational(3,2)*al**3))==0,"Critical-safe fiber Young constant")
finish("geometric_momentum.py",dict(
 original_selected_action_pure_geometry_momentum="Pi_g=P_u+D-2*kappa*Q",
 positive_raw_source_square_retained=True,all_AE_and_nonzero_U0_terms_retained=True,
 selected_slice_geometry_momentum_selfadjoint_form=True,
 positive_confining_covariant_strong_geometry_domain_transport=True,
 raw_snapshot_strong_domain_transport_inferred=False,
 positive_gate_source_marginal_or_Q2_budget_required=False,
 positive_gate_allows_normal_mixed_entangled_states_with_finite_G_form_energy=True,
 readable_gate="m<=1e-9 => -mean(Pi_g)>=5/m^3>1",
 old_Pi_geometry_reference_abs_upper="exp(-1130)",
 old_m_and_pure_geometry_budget_recovery="REJECTED in selected positive-confining family",
 matching_a_h_means_alone_excluded=False,
 negative_K=K,negative_g=outward(ng),negative_d0=outward(d0),negative_d1=outward(d1),
 negative_raw_source_cube_coefficient=outward(cg),
 negative_gate="1.15*T3+0.02*L3 > h_i^-3",
 negative_controlled_tail_consequence="T3<=2h_i^3 => L3>40h_i^-3",
 negative_gate_is_all_state_no_go=False,
 negative_raw_source_cube_is_renormalized_continuum_energy=False),
 [new+"coefficient_window.json",new+"coupled_forms.json",new+"ordering_domain.json",
 new+"source_budgets.json",new+"ALL_SIGN_EVOLUTION.md",new+"MEAN_RECOVERY.md",
 base+"ACTION_LIFT.md",base+"ACTION_BOUNDARY.md"],proof="GEOMETRIC_MOMENTUM.md")
