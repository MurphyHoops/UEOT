"""Independent separatrix, retained geometry spread and scope audit."""
import json,sympy as sp
from common import *
NAMES=["semantics","records","evolution","profile","ultraviolet","local_readout","locality","backaction","fluctuations","long_filter","transport","smooth_binary","actual_history","dynamic_filter","kinetic_probe","conditional","renormalization","controller","local_tensor","conditional_tensor","pulse_ward","implementation_bridge","conditional_noise","symmetry_exit","invariant_preparation","static_preparation","clock_resource","static_instrument"]
def result():
    d={n:json.loads((HERE/(n+".json")).read_text()) for n in NAMES}
    assert all(x["status"]=="PASS" for x in d.values())
    y,k,z=sp.symbols("y k z",positive=True)
    F=y-k+z/y**2
    assert sp.simplify(F.subs({y:2*k/3,z:4*k**3/27}))==0
    assert sp.simplify(sp.diff(F,y).subs({y:2*k/3,z:4*k**3/27}))==0
    qcrit=4/(27*BETA)
    mus=d["smooth_binary"]["conditional_source_mean_centers"]
    err=box(d["smooth_binary"]["conditional_source_mean_error_upper"])
    assert below((box(mus[0])+err)/MU,qcrit.a)
    assert above((box(mus[1])-err)/MU,qcrit.b)
    risk=box(d["smooth_binary"]["complete_two_flag_source_Bayes_risk_upper"])
    geometry_spread=iv.sqrt(box(CASE["variance_S0"])-risk)/(2*MU)
    assert above(geometry_spread,"0.15")
    actual=d["actual_history"]
    total=box(actual["actual_joint_two_projected_equation_RMS_upper"])
    assert below(total,"7.6e-6")
    assert actual["high_state_reset"] is False and actual["conditional_zero_high_product_assumed"] is False
    assert actual["instantaneous_local_full_tensor_SCE_closed"] is False
    assert d["local_tensor"]["at_least_one_flag_has_nonzero_local_anisotropic_mean"]
    assert d["controller"]["actual_short_conditional_high_NEC_sign_inferred_from_energy_alone"] is False
    assert d["renormalization"]["finite_controller_counterterm_coefficient_fixed_by_free_AE_scheme"] is False
    assert d["conditional_tensor"]["both_flags_require_nonhomogeneous_geometry_or_device_compensation"]
    assert d["implementation_bridge"]["physical_total_source_implementation_complete"] is False
    assert d["invariant_preparation"]["source_record_discrimination_is_gravity_discrimination"] is False
    assert d["invariant_preparation"]["noise_contrast_alone_changes_deterministic_mean_SCE_geometry"] is False
    assert d["clock_resource"]["Gamma_preparation_or_local_clock_instrument_built"] is False
    assert below(box(d["static_preparation"]["single_ring_joint_projected_residual_RMS_upper"]),"1.4e-6")
    assert below(box(d["static_instrument"]["actual_local_same_static_joint_RMS_upper"]),"1.4e-6")
    return {
      "separatrix_condition":"zeta=4*kappa^3/27; qcrit=4/(27*beta)",
      "critical_posterior_mean_ratio":outward(qcrit),
      "two_binary_branches_straddle_leading_separatrix":True,
      "leading_branches_claimed_same_original_static_past":False,
      "initial_a_to_six_relative_standard_deviation_lower":outward(geometry_spread),
      "conditional_source_precision_removes_classical_geometry_spread":False,
      "actual_same_state_projected_positive_time_RMS_upper":outward(total),
      "new_scientific_checks":29,"frozen_results_reused_without_execution":91,
      "native_read_only_review_agents":3,
      "new_radial_same_geometry_RMS_upper":d["static_preparation"]["single_ring_joint_projected_residual_RMS_upper"],
      "new_radial_source_comparison_is_original_angular_success":False,
      "external_human_peer_review":False,
      "closed":"actual local instrument and finite-probe stress-moment bridge; same-state projected histories; conditional local tensor/noise; old symmetry exit; distinct radial same-geometry source comparison and clock resource gate",
      "open":["controller and reader renormalized total source","causal local Einstein response","constrained common physical past and preparation","exact nearby SCE existence and stability","empirical calibration","physical unification"],
      "proof":"REVIEW.md"}
if __name__=="__main__":finish("review.py",result(),["REVIEW.md"]+[n+".json" for n in NAMES])
