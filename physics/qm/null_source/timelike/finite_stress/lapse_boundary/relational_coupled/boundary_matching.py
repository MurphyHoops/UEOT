"""Matching phase, canonical source trace and action-degeneracy identities."""
import sympy as s
from common import *
base="physics/qm/null_source/timelike/finite_stress/lapse_boundary/"
new=base+"relational_coupled/"
load(new+"g_zero_boundary.json")
# Exact finite-dimensional representative of the two orthogonal spectral packets.
v=s.Matrix([1,1])/s.sqrt(2);M=s.diag(-1,1)
require((M.conjugate().T*M)==s.eye(2),"Nontrivial unitary phase matching")
require((v.conjugate().T*M*v)[0]==0,"Orthogonal matched normal outputs")
lam1,lam2=s.symbols("lambda1 lambda2",real=True);AA=s.diag(lam1,lam2)
require(M*AA-AA*M==s.zeros(2),"Preserved spectral probabilities")
c,t,u,uc,kappa=s.symbols("c t u uc kappa",real=True)
g=(u-uc)/4;chi=s.Function("chi")(u)
require(s.simplify(s.diff(g*chi,u)-g*s.diff(chi,u)-chi/4)==0,"Degenerate coefficient must be varied before restriction")
require(s.diff(g,u)*kappa==kappa/4,"Original lapse derivative Dg")
require(s.simplify(s.diff(g*chi**2/2,u)-g*chi*s.diff(chi,u)-chi**2/8)==0,"Retained coefficient variation")
f=s.Function("f")(u);th=s.Function("theta", real=True)(u)
P=lambda z:-s.I*s.diff(z,u)
phase=s.exp(s.I*th)
require(s.simplify(phase*P(s.conjugate(phase)*f)-(P(f)-s.diff(th,u)*f))==0,"Unitary multiplier derivative sign")
finish("boundary_matching.py",dict(
 arbitrary_unitary_profile_matchings_exist=True,
 relational_punctured_operator_selfadjoint_domain_family=True,
 same_relational_formal_operator=True,relational_kinematic_kernel_empty=True,
 matching_uniquely_selected_by_original_lapse_action=False,
 convention_covariance_alone_implies_commutation=False,
 additional_scale_invariant_matching_is_decomposable_in_hankel_spectrum=True,
 same_profile_source_and_geometry_spectral_laws_can_give_orthogonal_outputs=True,
 original_raw_phi_source_marginal_has_normal_trace_norm_boundary_limit=True,
 full_joint_state_has_normal_boundary_limit=False,
 unbounded_source_moment_convergence_inferred_from_trace_norm=False,
 every_reference_source_history_preserved=False,
 selected_original_lapse_constraint_selfadjointness_from_unbounded_kappa_congruence=False,
 hard_extra_primary_constraint_has_nonzero_normal_slice_kernel=False,
 hard_extra_primary_constraint_derived_as_required_quantum_law=False,
 profile_charge_spectral_residual_invariance_is_conditional=True),
 [new+"g_zero_boundary.json",new+"geometric_momentum.json",new+"PHYSICAL_SLICE.md",
 new+"REFERENCES.md",base+"ACTION_LIFT.md"],proof="BOUNDARY_MATCHING.md")
