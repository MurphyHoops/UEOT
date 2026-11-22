"""Actual short local poststate and both averaged future residual second moments."""
import json
from common import *
def result():
    binary=json.loads((HERE/"smooth_binary.json").read_text())
    mean=json.loads((HERE/"ultraviolet.json").read_text())
    transport=json.loads((HERE/"transport.json").read_text())
    risk=box(binary["complete_two_flag_source_Bayes_risk_upper"])
    w=C/2500;vm=BETA_FIELD2*w;s=1/(4*vm)
    D1=TIME_TV;D2=256/iv.pi**2
    assert below(D2,26)
    E1=s*D1**2/(2*X*VOLUME)
    F=s*(1+2*NTHERMAL)*D1*D2/(2*X*VOLUME)
    K=46*LAMBDA2/iv.pi**2
    extra=K*iv.sqrt(8*F+32*E1**2)
    assert below(extra,"5e-12")
    be=box(mean["density_mean_residual_normalized_by_3_lambda2_over_2"])
    bp=box(mean["pressure_mean_residual_normalized_by_3_lambda2_over_2"])
    trans=box(transport["all_modes_mean_stress_difference_over_lambda4_upper"])
    trans_normalized=exact(2)/3*trans*LAMBDA2
    source=iv.sqrt(2)*BETA/MU*iv.sqrt(risk)
    mean_norm=iv.sqrt((be+trans_normalized)**2+(bp+trans_normalized)**2)
    high=iv.sqrt(2)*LAMBDA2*iv.sqrt(exact(1600)**2+exact(8000)**2)
    total=source+mean_norm+high+extra
    assert below(total,"7.6e-6")
    return {
      "state":"actual smooth-binary short local poststate transported on the same CCR algebra",
      "spatial_projection":"full-S3 average of density and isotropic pressure only",
      "proper_future_window":"0 <= lambda*t <= 1/10 with smooth positive weight",
      "all_outcomes_retained":True,"high_state_reset":False,
      "conditional_zero_high_product_assumed":False,
      "conditional_zero_high_correlations_bounded_by_Minkowski":True,
      "two_flag_positive_operator_domination_used":True,
      "source_vector_RMS_upper":outward(source),
      "mean_residual_vector_upper":outward(mean_norm),
      "transported_reference_high_vector_RMS_upper":outward(high),
      "nonselective_high_displacement_E1_upper":outward(E1),
      "nonselective_high_displacement_F_upper":outward(F),
      "future_quadratic_coefficient_K_upper":outward(K),
      "actual_local_backaction_added_vector_RMS_upper":outward(extra),
      "actual_joint_two_projected_equation_RMS_upper":outward(total),
      "same_original_U0_and_M2":True,
      "mode_and_geometry_ODE_integrations":0,
      "instantaneous_local_full_tensor_SCE_closed":False,
      "local_nonhomogeneous_metric_response_constructed":False,
      "apparatus_and_controller_total_source_closed":False,
      "nearby_exact_SCE_solution_proved":False,
      "proof":"ACTUAL_HISTORY.md"}
if __name__=="__main__":finish("actual_history.py",result(),["ACTUAL_HISTORY.md","smooth_binary.json","transport.json","ultraviolet.json","fluctuations.json"])
