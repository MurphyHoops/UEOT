"""Actual-prior lower bounds for short local source instruments, including high noise."""
from common import *
def result():
    alpha2=1/(2*iv.pi**2)
    vb=alpha2/X0+(1+2*NTHERMAL)/(2*X*iv.sqrt(3)*VOLUME)
    cloc=alpha2/(4*vb)
    floor=4*cloc*(C*MU-2*VP)/C**2
    scale2=exact("1e10");vm=exact("1e-12")
    q=scale2*alpha2/(C**2*vm)
    gap=iv.exp(-scale2*vb/2)*(1-1/iv.sqrt(1+q*(VP+C/2)))
    assert above(floor,"1.36e-12") and above(gap/2,"0.05")
    return {
      "short_local_region_and_antipodal_test":"LOCAL_READOUT.md strict supports",
      "complement_observable":"B=phi(A^-4 t(eta-eta_ref)b_south); beta_B=0",
      "alpha_B_squared":outward(alpha2),
      "actual_complement_variance_upper":outward(vb),
      "universal_local_QND_source_Bayes_MMSE_strict_lower":outward(floor),
      "universal_local_QND_source_standard_error_lower":outward(iv.sqrt(floor)),
      "for_non_QND_instruments_bound_is_noise_operator_error_only":True,
      "global_S0_Gaussian_resolution":outward(vm),
      "bounded_O2_averaged_Weyl_test_scale":100000,
      "actual_fixed_input_global_vs_any_short_local_channel_D_lower":outward(gap/2),
      "full_scalar_observable_contract_required_for_Weyl_witness":True,
      "shift_invariant_subalgebra_can_use_this_Q_Weyl_witness":False,
      "normal_state_energy_unbounded_minimax_channel_gap":"1 in TV for complete records; not the finite-prior result above",
      "pure_zero_linear_observable_in_region_with_causal_complement":"only the zero observable",
      "long_worldtube_with_empty_causal_complement_excluded":False,
      "proof":"LOCALITY.md"}
if __name__=="__main__":finish("locality.py",result(),["LOCALITY.md","LOCAL_READOUT.md"])
