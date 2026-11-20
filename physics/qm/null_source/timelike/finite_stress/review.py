"""Independent scope ledger and source-binding consistency."""
import ast,hashlib,json
from common import *
NAMES=["model","phase_diagram","critical_state","volume_moments","positive_source",
 "source_observables","dispersion_gap","finite_clock","robustness"]
science={n:json.loads((HERE/(n+".json")).read_text()) for n in NAMES}
for n,j in science.items():
    assert j["status"]=="PASS"
    assert j["old_checkers_executed"]==j["mode_ODE_integrations"]==j["geometry_ODE_integrations"]==0
    for rel,digest in j["source_sha256"].items():
        assert hashlib.sha256((REPO/rel).read_bytes()).hexdigest()==digest,(n,rel)
    assert str((HERE/(n.upper()+".md")).relative_to(REPO)) in j["source_sha256"]
assert science["model"]["full_original_AE_model_restored"] is False
assert science["phase_diagram"]["subcritical_H2_assumption_needed"] is False
assert science["critical_state"]["complete_original_P_law_preserved"] is True
assert science["critical_state"]["bare_source_state_preserved"] is False
assert science["volume_moments"]["weighted_energy_term_wrongly_assumed_nonpositive"] is False
assert science["positive_source"]["total_positive_energy_variance_finite_each_finite_time_window"] is True
assert science["source_observables"]["naive_classical_symmetric_work_law_exact"] is False
assert science["dispersion_gap"]["global_volume_weighted_ratio_claimed"] is False
assert science["dispersion_gap"]["ratio_diagnostics_are_linear_observable_means"] is False
assert science["dispersion_gap"]["same_state_reference_constraint_linear_mean_claimed"] is True
assert science["finite_clock"]["same_dust_counted_once"] is True
assert science["finite_clock"]["unconditional_source_equals_input_claimed"] is False
assert science["robustness"]["model_sequence_is_fixed_mu_limit"] is False
assert science["robustness"]["old_A_free_history_matched"] is False
allowed={"__future__","argparse","hashlib","json","math","pathlib","mpmath","sympy","common","ast"}
for n in NAMES+["common","review"]:
    tree=ast.parse((HERE/(n+".py")).read_text())
    for node in ast.walk(tree):
        if isinstance(node,ast.Import):
            assert all(a.name.split(".")[0] in allowed for a in node.names)
        if isinstance(node,ast.ImportFrom):
            assert node.level==0 and node.module.split(".")[0] in allowed
        if isinstance(node,ast.Call) and isinstance(node.func,ast.Name):
            assert node.func.id not in {"eval","exec","__import__"}
finish("review.py",{
 "scientific_entries_checked":NAMES,
 "current_science_source_hashes_match":True,
 "new_certificates_import_only_declared_libraries_and_new_common":True,
 "strong_dust_quantization_required_by_original_mean_SCE_goal":False,
 "finite_source_exists_in_declared_critical_model":True,
 "original_AE_QFT_mean_and_noise_and_device_unified":False,
 "empirical_gravity_record_calibrated":False,
 "external_human_peer_review":False,
 "native_actual_source_audit_is_separately_recorded":True,
 "Core_modified":False,"GI_in_scope":False,"whole_physical_unification":"OPEN"},
 extra=[n+".json" for n in NAMES]+["CONTRACT.md"])
