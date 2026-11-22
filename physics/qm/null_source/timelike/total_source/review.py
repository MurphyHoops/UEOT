"""Cross-certificate scope and numerical frontier audit."""
import json
from pathlib import Path
from common import *
names=["rotation","fieldspace","autonomous","constraints","coherence","pressure_noise",
 "influence","history_witness","preparation","total_future","discrimination","response",
 "initial_correlations","carrier","preparation_causality"]
data={n:json.loads((HERE/(n+".json")).read_text()) for n in names}
for n,d in data.items():
 assert d["status"]=="PASS"
 assert d["old_checkers_executed"]==d["mode_ODE_integrations"]==d["geometry_ODE_integrations"]==0
 for rel,digest in d["source_sha256"].items():
  assert hashlib.sha256((REPO/rel).read_bytes()).hexdigest()==digest,(n,rel)
assert data["rotation"]["complete_total_stress_operator_preserved_by_constant_O4_rotation"]
assert not data["autonomous"]["same_original_CQ_initial_state_or_full_AE_QFT_claimed"]
assert not data["constraints"]["specified_independent_noise_linear_extension_has_absolute_constrained_baseline"]
assert not data["constraints"]["deterministic_semiclassical_mean_solution_invalidated"]
assert data["coherence"]["complete_W2_and_total_energy_spectral_law_preserved"]
assert data["pressure_noise"]["density_and_momentum_difference_slots_vanish"]
assert above(box(data["history_witness"]["full_field_contrast_strict_lower_c_equals_w"]),"2e-10")
assert data["preparation"]["explicit_unitary_positive_unpostselected_dilation"]
assert not data["total_future"]["individual_joint_states_assumed_product"]
assert data["discrimination"]["first_independent_shots_for_error_below_0_05"]==4229
assert data["response"]["both_positive_poles_retained"]
assert not data["response"]["absolute_constraint_compatible_baseline_supplied"]
assert not data["initial_correlations"]["complete_physical_joint_state_closed"]
assert data["carrier"]["individual_future_influences_factor_for_all_c"]
assert not data["carrier"]["numeric_carrier_epsilon0_or_bare_contrast_bound_inherited"]
assert above(box(data["preparation_causality"]["example_ratio_to_old_response_window"]),"6140000")
finish("review.py",{
 "proof":"REVIEW.md","new_scientific_checks_including_review":16,
 "frozen_results_reused_without_execution":121,"frozen_scientific_files":438,
 "native_read_only_research_agents":3,"external_human_peer_review":False,
 "new_source_pair_is_original_angular_preparation_success":False,
 "same_W2_energy_law_static_mean_but_distinct_full_field_influence":True,
 "explicit_gate_carrier_future_and_causal_preparation_bound":True,
 "bare_smooth_history_contrast_strict_lower":data["history_witness"]["full_field_contrast_strict_lower_c_equals_w"],
 "ideal_source_independent_shots_for_error_below_five_percent":4229,
 "open":["absolute constrained joint quantum/geometric baseline",
 "actual local autonomous preparation with full total source",
 "expanded common mean and causal fluctuation dynamics",
 "empirical gravitational readout and calibration","physical unification"],
 "whole_physics_unification_completed":False
},tuple(["REVIEW.md","README.md","INPUTS_AND_NEXT_TEST.md"]+[n+".json" for n in names]))
