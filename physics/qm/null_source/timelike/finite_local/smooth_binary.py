"""Two smooth radial flags, finite reader energy, no outcome deletion."""
from common import *
def result():
    root3=iv.sqrt(3);L=1+root3/4
    vscaled=VP/C;w=C/2500
    high=W_HIGH_UPPER
    delta=(VP+w+high)/C
    gap=(root3-1)/4;dr=exact("0.001")
    tail=iv.exp(-(gap-dr)**2/(2*delta))
    assert below(tail,"1.1e-18")
    intrinsic=4*vscaled*L+8*vscaled**2
    within=4*vscaled*L+4*vscaled**2
    risk=(iv.sqrt(intrinsic)+root3/2*iv.sqrt(tail))**2
    mu_error=(iv.sqrt(within*tail)+root3*tail/2)/(exact("0.5")-tail)
    assert below(risk,"1.56e-11") and below(mu_error,"9e-15")
    mu_lo=1+2*vscaled;mu_hi=1+root3/2+2*vscaled
    qlo=(mu_lo-mu_error)/MU;qhi=(mu_hi+mu_error)/MU
    assert above(qlo,exact(3)/5) and below(qhi,exact(7)/5)
    relative_reader_energy=2*(w/C)*(800*iv.pi)**2*tail
    assert below(relative_reader_energy,"6e-15")
    distance=iv.sqrt((VP+high)/(2*w+VP+high))
    assert below(distance,"8e-4")
    long_distance=iv.sqrt(VP/(2*w+VP))
    assert below(long_distance,"6e-5")
    weak_vm=BETA_FIELD2*w
    out_energy=TIME_TV**2/(4*weak_vm*A**3*VOLUME)
    assert below(out_energy,"1.88e-11")
    assert below(iv.sqrt(XC)/A,exact(5)/4)
    assert below((1+exact(7)/5)**(exact(1)/6),exact(6)/5)
    assert below(exact(6)/5*exact(5)/4*exact(13)/12,exact(13)/8+exact("1e-50"))
    return {
      "actual_instrument":"two smooth radial reader effects after the local Gaussian pointer unitary",
      "pointer_noise_per_P_coordinate":outward(w),
      "normalized_total_coordinate_noise_upper":outward(delta),
      "threshold_radius_over_sqrt_C":"(3+sqrt(3))/4",
      "radial_transition_halfwidth":outward(dr),
      "tail_and_transition_annulus_probability_upper":outward(tail),
      "complete_two_flag_source_Bayes_risk_upper":outward(risk),
      "conditional_source_mean_centers":[outward(mu_lo),outward(mu_hi)],
      "conditional_source_mean_error_upper":outward(mu_error),
      "conditional_source_means_enclosure":[[outward(mu_lo-mu_error)[0],outward(mu_lo+mu_error)[1]],[outward(mu_hi-mu_error)[0],outward(mu_hi+mu_error)[1]]],
      "conditional_mean_ratio_enclosure":[outward(qlo)[0],outward(qhi)[1]],
      "flag_probability_deviation_from_one_half_upper":outward(tail),
      "reader_pointer_kinetic_energy_relative_increment_upper":outward(relative_reader_energy),
      "short_protocol_complete_flag_and_field_distance_from_latent_label_benchmark_upper":outward(distance+tail),
      "long_protocol_analogous_distance_upper":outward(long_distance+tail),
      "short_two_target_fields_out_mean_injected_energy_upper":outward(out_energy),
      "readout_shift_invariant":True,"readout_internal_O2_invariant":True,
      "fine_angle_or_radius_record_created":False,"outcomes_deleted":False,
      "nonselective_source_spectral_law_unchanged":True,
      "high_poststate_reset":False,
      "two_branch_transport_plateau_required":False,
      "common_proper_preparation_wait_time":outward(325*A),
      "all_records_share_common_future_start":True,
      "causal_flag_distribution_proper_wait":outward(iv.pi*A),
      "causal_flag_distribution_extra_zero_shear":outward(iv.pi/X),
      "physical_localized_flag_collection_assumed":True,
      "apparatus_controller_Einstein_source_closed":False,
      "proof":"SMOOTH_BINARY.md"}
if __name__=="__main__":finish("smooth_binary.py",result(),["SMOOTH_BINARY.md","local_readout.json","transport.json"])
