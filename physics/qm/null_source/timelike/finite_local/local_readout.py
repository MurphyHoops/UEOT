"""Finite-support shift-invariant source readout with all high modes retained."""
from common import *
def result():
    assert above(VOLUME) and below(VOLUME,"0.57")
    assert below(TIME_TV,"2.547")
    field_variance=(1+2*NTHERMAL)*TIME_TV/(2*X*VOLUME)
    energy=iv.pi**2*TIME_TV**2/(2*A*VOLUME)
    duration=3*iv.pi*A/8
    assert below(LOCAL_MSE_UPPER,"3e-9")
    return {
      "geometry":"original unfiltered exact static mean-SCE background",
      "fixed_test":"f=A^-4 t'(eta-eta_ref) b(Omega), integral t=integral b=1",
      "time_kernel":"uniform blocks of widths pi/4 and pi/16 convolved with an even C-infinity probability bump of radius pi/32",
      "spatial_kernel":"normalized S3 ball radius pi/6 convolved with smooth probability bump radius pi/24",
      "temporal_support_duration_conformal":"3*pi/8",
      "spatial_support_cap_radius":"5*pi/24",
      "proper_measurement_duration":outward(duration),
      "antipodal_equal_time_support_is_strict_causal_complement":True,
      "shift_invariant_without_Q_reference":True,
      "zero_Q_coefficient":0,
      "zero_P_coefficient":"-1/(sqrt(2*pi^2)*A^2)",
      "original_full_source_spectral_law_preserved_nonselectively":True,
      "space_ball_volume":outward(VOLUME),
      "spatial_L2_squared_upper":outward(1/VOLUME),
      "time_derivative_L1_upper":outward(TIME_TV),
      "all_mode_high_field_variance_upper":outward(field_variance),
      "input_referred_pointer_noise":outward(W_POINTER),
      "input_referred_high_noise_upper":outward(W_HIGH_UPPER),
      "total_input_referred_noise_upper":outward(W_UPPER),
      "source_estimator_MSE_upper":outward(LOCAL_MSE_UPPER),
      "two_fields_out_mean_injected_energy_upper":outward(energy),
      "pointer_resolution_in_field_units":outward(VM_FIELD),
      "known_time_ordering_Pi_squared_phase_compensation_required":True,
      "apparatus_total_gravitational_source_closed":False,
      "valid_in_old_fast_mode_short_window":False,
      "proof":"LOCAL_READOUT.md"}
if __name__=="__main__":finish("local_readout.py",result(),["LOCAL_READOUT.md"])
