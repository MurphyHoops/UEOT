"""Actual local mid/out source instrument on one common static positive window."""
import json
from common import *
def result():
    old=json.loads((HERE/"actual_history.json").read_text())
    prior=json.loads((HERE/"static_preparation.json").read_text())
    E1=box(old["nonselective_high_displacement_E1_upper"])
    F=box(old["nonselective_high_displacement_F_upper"])
    K=1/(3*iv.pi**2*X)
    extra=K*iv.sqrt(4*F+16*E1**2)
    total=box(prior["single_ring_joint_projected_residual_RMS_upper"])+extra
    assert below(extra,"2.9e-14") and below(total,"1.4e-6")
    assert above(exact("1.5e-6")-total,"1.9e-7")
    return {
      "input":"new uniform single-ring or explicit original-A-matched two-center preparation",
      "instrument":"same actual short weak coupling and complete mid/out annulus reader",
      "same_static_geometry_and_window_for_every_record":True,
      "future_window_origin":"tau=lambda*(t_proper-t_star), after pulse, finite-probe h and stipulated reader completion",
      "all_records_share_outcome_independent_post_readout_origin":True,
      "original_pulse_center_used_as_future_window_origin":False,
      "free_waiting_phases_or_zero_shear_reset":False,
      "common_normalizer_for_both_stress_components":"3/(2*A^2)",
      "full_source_S0_spectral_law_preserved_at_free_out":True,
      "all_records_retained":True,
      "record_dependent_geometry_feedback":False,
      "high_reset_or_conditional_product_assumed":False,
      "static_quadratic_coefficient_K":outward(K),
      "actual_local_added_joint_RMS_upper":outward(extra),
      "actual_local_same_static_joint_RMS_upper":outward(total),
      "each_conditional_mean_solves_same_static_SCE":False,
      "finite_common_coupling_exists_for_source_record_TV_above":"0.999",
      "finite_common_coupling_exists_for_target_static_RMS_below":"1.5e-6",
      "calibrated_finite_coupling_or_total_device_energy_supplied":False,
      "global_D_clock_protocol_composed_without_recalculation":False,
      "full_local_tensor_or_total_gravity_history_closed":False,
      "proof":"STATIC_INSTRUMENT.md"}
if __name__=="__main__":finish("static_instrument.py",result(),["STATIC_INSTRUMENT.md","static_preparation.json","invariant_preparation.json","actual_history.json","implementation_bridge.json"])
