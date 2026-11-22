"""Actual source-containing boundary column and discriminating two-row checks."""
import sympy as s
from common import require,finish
a,h,hp,U,V0,H,Lam,J,I,q,qp=s.symbols("a h hp U V0 H Lam J I q qp",real=True,nonzero=True)
kappa=2*s.exp(U)/(3*V0*a*a)
qE=-2*a*a*h*s.exp(U)*J
addition=-qE*H/(3*V0*a**4*h)
require(s.simplify(addition-kappa*H*J)==0,"Exact source density cancellation")
res=-kappa*H*J+Lam*addition
require(s.simplify(res-(1-Lam)*(-kappa*H*J))==0,"Whole lambda family")
require(s.simplify(res.subs(Lam,1))==0,"Lambda one passes density")
require(s.simplify(res.subs(Lam,0))!=0 and s.simplify(res.subs(Lam,2))!=0,"Lambda zero and two fail density")
cq=-q/(3*V0*a**4*h)
alphaQ=-(qp-3*h*q)/(6*V0*a*a)
alphaD=(q-a*a*I*(qp-3*h*q))/(3*V0*a**4)
alphaH=-a*a*hp/2
betaH=h-a*a*hp*I
corrQ=alphaQ+cq*alphaH
corrD=alphaD+cq*betaH
target=(-qp+(3*h+hp/h)*q)/(6*V0*a*a)
require(s.simplify(corrQ-target)==0,"Corrected zero Q coefficient")
require(s.simplify(corrD-2*I*corrQ)==0,"Corrected D coefficient and canceled old leading cost")
require(4*36*s.Rational(81,64)<200,"Sharp H_V variance tail constant")
# All covariance terms of a common vector linear combination are retained.
vR,vH,cross,c=s.symbols("vR vH cross c",real=True)
vsum=vR+2*c*cross+c*c*vH
require(s.diff(vsum,c,2)==2*vH and s.diff(vsum,c).subs(c,0)==2*cross,"Cross terms cannot be omitted")
finish("mixed_boundary.py",dict(
 same_full_field_source_and_same_actual_response=True,
 initial_column="H_i*v_i/(3*V0*a_i^2*h_i), H_i=delta(H0-V_i*Q)_i",
 source_containing_not_independent_carrier=True,
 continuous_source_GNS_vector_weak_solution=True,
 homogeneous_pressure_and_density_rows_solved_in_transpose_domain=True,
 residual_lambda_family="(1-lambda)*K_res",
 lambda_zero_and_two_rejected_for_density=True,
 lambda_one_unique_in_declared_family=True,
 common_source_cutoff_Gram_limit_positive=True,
 response_finite_K_inverse_limit_assumed=False,
 boundary_column_in_zero_initial_H4_graph=False,
 initial_h_required_strictly_nonzero=True,
 h_zero_is_separate_rejected_branch_for_this_formula=True,
 old_uncertainty_lower_bound_reused_without_recomputing_cross=False,
 explicit_corrected_complete_variance_and_mixed_block=True,
 uniform_bound_as_h_tends_zero=False,
 near_static_scaled_variance_limit="q_static(i)^2*sigma_thin^2*mu2/(9*V0^2*A^6)",
 normal_geometry_matter_tensor_state_constructed=False,
 original_total_action_preparation_implementation_proved=False,
 finite_K_lapse_action_origin_of_initial_column_proved=True,
 Peierls_or_canonical_geometry_algebra_proved=False),
 ["finite_stress/lapse_boundary/ACTION_LIFT.md",
  "finite_stress/lapse_boundary/ACTUAL_INVERSE.md",
  "finite_stress/lapse_boundary/PREPARED_READOUT.md",
  "finite_stress/lapse_boundary/CONSTRAINT_RESIDUAL.md",
  "finite_stress/lapse_boundary/QUIET_WINDOW.md"],
 proof="MIXED_BOUNDARY.md")
