"""A distinct radial preparation pair: equal two-point physics, different complete stress noise."""
import sympy as sp
from common import *
def result():
    root3=iv.sqrt(3);L=1+root3/4;r=VP/C
    variance_mid=4*r*L+4*r*r
    variance_two=exact(3)/16+variance_mid
    assert above(variance_mid) and below(variance_mid,"1.56e-11")
    assert sp.simplify((1+(1+sp.sqrt(3)/2)**2)/2-(1+sp.sqrt(3)/4)**2-sp.Rational(3,16))==0
    w=C/2500;delta=(VP+w+W_HIGH_UPPER)/C
    rc=iv.sqrt(L);r1=(1+root3)/2;dr=exact("0.001")
    h0=(rc-1)/2-dr;h1=(r1-rc)/2-dr
    e0=iv.exp(-h0*h0/(2*delta));e1=iv.exp(-h1*h1/(2*delta))
    two_error=(e0+e1)/2;mid_error=e1
    TVlower=1-two_error-mid_error
    equal_prior_error=(two_error+mid_error)/2
    reader=2*(w/C)*(800*iv.pi)**2*e1
    assert below(two_error,"8.79e-5") and below(mid_error,"1.688e-4")
    assert above(TVlower,"0.999743") and below(equal_prior_error,"1.3e-4")
    assert below(reader,"0.86")
    # Homogeneous leading-GR fold: there is no first-order radius response at the static point.
    x,z=sp.symbols("x z",real=True)
    F=sp.Rational(2,3)+(1+z)/(3*(1+x)**6)-1/(1+x)**2
    assert F.subs({x:0,z:0})==0
    assert sp.diff(F,x).subs({x:0,z:0})==0
    assert sp.diff(F,x,2).subs({x:0,z:0})/2==4
    assert sp.diff(F,z).subs({x:0,z:0})==sp.Rational(1,3)
    aa,hh,ds=sp.symbols("aa hh ds",real=True)
    assert sp.diff(sp.Rational(3,2)*(hh**2+aa**-2),aa)==-3/aa**3
    assert sp.diff(sp.Rational(3,2)*(hh**2+aa**-2),hh).subs(hh,0)==0
    # Exact two-center matcher for the original actual angular prior, without twirling A.
    d=sp.sqrt(3)/2;L_exact=1+d/2;aa=d/(3+d)
    zzp=-aa+sp.sqrt(1+aa**2);zzm=-aa-sp.sqrt(1+aa**2)
    wp=(1+aa/sp.sqrt(1+aa**2))/2;wm=1-wp
    assert sp.simplify(wp*zzp+wm*zzm)==0
    assert sp.simplify(wp*zzp**2+wm*zzm**2-1)==0
    for zz in [zzp,zzm]:
        assert sp.simplify((1+d)/4+zz*d/2+zz**2*(3+d)/4-L_exact)==0
    # The preceding identities match m and covariance for either sigma=+1 or -1.
    rr,tt=sp.symbols("rr tt",real=True)
    zz=tt/(1-2*rr*tt)
    cg=sp.log(sp.cosh(sp.sqrt(3)*zz/4))
    for order,expected in [(1,0),(2,sp.Rational(3,16)),(3,9*rr/4),(4,27*rr**2-sp.Rational(9,128))]:
        assert sp.simplify(sp.diff(cg,tt,order).subs(tt,0)-expected)==0
    return {
      "contract":"new radial source preparation; not the old angular preparation comparison",
      "two_ring_R":["1","1+sqrt(3)/2"],"single_ring_R":"1+sqrt(3)/4",
      "same_M2_U0_Gaussian_covariance_high_state_and_mean_source":True,
      "normal_trace_class_CQ_states_not_sharp_P_eigenstates":True,
      "complete_two_point_functions_equal":True,
      "same_free_mean_RSET_and_stress_response_inputs":True,
      "same_complete_relative_mean_response_on_common_prescribed_linear_background_family":True,
      "relative_response_equality_includes_shared_contact_seagull_and_finite_counterterms":True,
      "absolute_response_kernel_calculated":False,
      "source_CGF_difference":"log cosh((sqrt(3)/4)*t/(1-2*r*t))",
      "source_connected_cumulant_differences":["0","3/16","9*r/4","27*r^2-9/128"],
      "finite_kinetic_environment_block_noise_difference":"(3/16)*J_A tensor J_B",
      "block_identity_includes_nonlinear_reader_or_quantum_controller":False,
      "noise_contrast_alone_changes_deterministic_mean_SCE_geometry":False,
      "existing_exact_mean_SCE_solution_reused_only_when_its_prior_is_compatible":True,
      "complete_stress_noise_difference":"(3/16)*J_tensor_J",
      "J":"M2*(2*u_a*u_b+g_ab)/(2*a^6)",
      "single_ring_source_variance":outward(variance_mid),
      "two_ring_source_variance":outward(variance_two),
      "single_ring_noise_minimal_only_in_fixed_v_radial_Gaussian_CQ_family":True,
      "same_additive_nonselective_pointer_preserves_rank_one_noise_difference":True,
      "new_mid_out_reader_two_ring_error_upper":outward(two_error),
      "new_mid_out_reader_single_ring_error_upper":outward(mid_error),
      "new_reader_outcome_TV_strict_lower":outward(TVlower),
      "new_reader_equal_prior_error_upper":outward(equal_prior_error),
      "new_reader_pointer_kinetic_increment_relative_upper":outward(reader),
      "new_reader_inherits_old_low_high_posterior_risk_bound":False,
      "new_reader_whole_apparatus_mean_stress_same_for_both_preparations":False,
      "source_record_discrimination_is_gravity_discrimination":False,
      "leading_GR_static_constraint_C1_source_to_geometry_graph_exists":False,
      "full_AE_or_all_geometries_excluded_by_leading_fold":False,
      "constraint_compatible_metric_noise_response_constructed":False,
      "full_AE_static_linear_constraint":"delta_rho+3*delta_a/A^3=0",
      "frozen_all_initial_jets_and_high_state_accept_nonzero_source_realization":False,
      "linear_noise_realization_gate_invalidates_common_ensemble_mean_history":False,
      "original_actual_A_preserved_by_explicit_new_two_center_preparation":True,
      "new_two_center_preparation_matches_full_first_and_second_field_moments":True,
      "new_two_center_preparation_preserves_old_full_Y_marginal":False,
      "new_two_center_preparation_is_historical_angular_B":False,
      "general_matched_moment_fixed_radius_centers_at_most":3,
      "stationary_closed_preparation_same_input_total_energy_law_is_conserved":True,
      "target_quieting_proves_complete_apparatus_energy_noise_reduction":False,
      "proof":"INVARIANT_PREPARATION.md"}
if __name__=="__main__":finish("invariant_preparation.py",result(),["INVARIANT_PREPARATION.md","symmetry_exit.json","local_tensor.json","implementation_bridge.json","../physical_source/RECORDS.md"])
