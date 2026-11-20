"""Independent rational endpoints, complex-sign negative control and scope checks."""
import json
import sympy as s
from common import *
entries=["static_bound","compensation","quantum_floor","zero_virial","relational","positive_clock","gravity_contract","dust_regularity"]
data={n:json.loads((HERE/(n+".json")).read_text()) for n in entries}
assert all(j["status"]=="PASS" and j["old_checkers_executed"]==0 for j in data.values())
# A distinct coarse rational proof of the new >10% bound.
margin=s.Rational(3,16)-s.Rational(1,500000)-s.Rational(9,100)*s.Rational(23,16)**2
assert margin==s.Rational(39,25600)-s.Rational(1,500000) and margin>0
# Wrong complex transpose has a large, exact residual.
Y=s.Matrix([[0,-s.I],[s.I,0]])
p=s.Matrix([s.sqrt(3)/2,0,0,s.Rational(1,2)])
C=s.kronecker_product(Y,s.eye(2))+s.kronecker_product(s.eye(2),-s.sqrt(3)*Y/2)
wrong=s.simplify((p.adjoint()*C*C*p)[0])
assert wrong==s.Rational(13,4)
assert data["quantum_floor"]["complex_transpose_orientation_verified"]
assert data["static_bound"]["strict_record_weighted_relative_RMS_lower"][0]>.1
clock=data["positive_clock"]
assert clock["full_constraint_RMS_lower"][0]>.49
assert clock["conditional_trace_distance_upper"][1]<1e-28
assert clock["mean_clock_energy_fraction_of_original_total"][0]>.13
assert clock["clock_window_probability_lower"][0]>.029
assert not clock["full_bare_source_marginal_unchanged"]
assert not clock["all_unbounded_RSET_derivatives_certified"]
assert data["zero_virial"]["proper_energy_constraint_RMS_lower"][0]>2.22
assert not data["gravity_contract"]["original_full_NOON_AE_model_preserved"]
assert data["relational"]["new_normal_Hadamard_source_family_preserves_complete_free_stress_records"]
assert not data["relational"]["original_bare_full_marginal_preserved"]
dust=data["dust_regularity"]
assert dust["original_subcritical_probability_upper"][1]<2.85e-12
assert dust["original_vs_any_admissible_source_trace_distance_lower"][0]>.9999999999971
assert not dust["original_momentum_law_and_stress_equivalent_family_embeddable"]
assert not dust["compact_spectral_support_required"]
assert dust["full_minisuperspace_LB_unitarily_equivalent_to_flat"]
assert dust["every_finite_constant_beta_exact_original_P_law_embedding_excluded"]
assert not dust["all_beta_near_one_numeric_distance_claimed"]
assert not data["gravity_contract"]["finite_positive_matter_stress_history_certified"]
finish("review.py",{
 "rational_ten_percent_margin":str(margin),"wrong_sigma_y_compensator_variance":str(wrong),
 "finite_clock_tail_not_mistaken_for_full_constraint_residual":True,
 "positive_clock_energy_cost_retained":True,
 "fixed_bare_marginal_bound_not_extended_to_stress_equivalence_class":True,
 "kinematic_vs_physical_normality_distinction_retained":True,
 "leading_GR_dust_not_spliced_into_original_AE_NOON_model":True,
 "self_adjoint_total_H_not_confused_with_finite_positive_matter_form":True,
 "original_source_dust_carrier_rejected_on_open_window":True,
 "LB_and_finite_constant_weight_ordering_escape_checked":True,
 "new_scientific_entries_reviewed":len(entries),
 "formal_machine_proof_or_external_human_review_claimed":False,
 "common_total_preparation_local_gravity_readout":"OPEN",
 "whole_physical_unification":"OPEN"},extra=[n+".json" for n in entries])
