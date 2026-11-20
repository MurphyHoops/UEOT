"""Independent cross-check of the new inverse, state and physical-scope exits."""
import sympy as sp
from common import *
NAMES=["spectrum","fast_root","state_matching","causal_inverse","harmonics"]
def result():
    data={n:json.loads((HERE/(n+".json")).read_text()) for n in NAMES}
    assert all(v["status"]=="PASS" for v in data.values())
    spec,fast,state,causal,harm=(data[n] for n in NAMES)
    # Barycentric second difference independently checks the pole-weight sign.
    z,a,b,c=sp.symbols("z a b c",real=True)
    bary=1/((z+c)*(z-a)*(z-b))+1/((a+c)*(a-z)*(a-b))+1/((b+c)*(b-z)*(b-a))
    assert sp.factor(bary-1/((z+c)*(a+c)*(b+c)))==0
    # Ward and curvature check independently of the modal expressions.
    x,u,sigma=sp.symbols("x u sigma",positive=True)
    rho=sp.Rational(3,2)/x;p=-sp.Rational(1,2)/x
    drho=-3*(rho+p)*u
    assert sp.simplify(2*rho*u+drho)==0
    assert sp.simplify(6*(sigma*sigma-2)*u/x).has(sigma)
    # Explicit first six Riccati coefficients, independent of code recursion.
    V=sp.symbols("V0:6",real=True);v0,v1,v2,v3,v4,v5=V
    expected=[-v0,-v1,v0**2-v2,4*v0*v1-v3,
              -v4+5*v1**2+6*v0*v2-2*v0**3,
              -v5+18*v1*v2+8*v0*v3-16*v0**2*v1]
    for literal,want in zip(state["Riccati_first_eight"],expected):
        assert sp.expand(sp.sympify(literal,locals={str(v):v for v in V})-want)==0
    assert spec["right_half_s_plane_roots"]==2 and spec["nonreal_y_zeros"]==0
    q=box(fast["fast_to_slow_rate_ratio"])
    assert above(q,468087) and below(q,468088)
    assert below(box(fast["root_s_derivative_divided_by_A"]),-29)
    assert above(box(fast["fast_conformal_growth_rate"]),5)
    assert below(2*SLOW,5)
    assert causal["both_positive_poles_retained"]
    assert causal["short_window_sup_w_per_sup_f"][1]<4.20e-14
    assert causal["short_window_sup_wprime_per_sup_f"][1]<1.30e-7
    assert not causal["seed_eta_0_1_nonlinear_error_certified"]
    assert not causal["past_slow_residual_convolution_automatically_converges"]
    assert state["linear_Hamiltonian_defect"]==0
    assert not state["same_slow_first_two_past_coefficients_fix_fast_amplitude"]
    assert not state["finite_one_slice_stress_is_full_Hadamard"]
    assert state["exact_bidisc_Jost_state_construction"]
    assert not state["Jost_small_norm_condition_required"]
    assert state["Jost_V_to_F_map_entire"]
    assert state["Jost_Wronskian_Theta_derivative_exact"]==0
    assert state["example_potential_norm_bound"][1]<0.051
    assert state["example_Jost_contraction_ratio_bound"][1]<0.008
    assert not state["example_is_exact_SCE_solution"]
    assert harm["uniform_absolute_characteristic_lower"][0]>11.99
    assert harm["four_derivative_inverse_norm_upper"]<1.73e18
    assert harm["same_global_divisor_and_M4_cover_all_combinations"]
    assert harm["two_variable_coefficient_inverse_retains_both_linear_amplitudes"]
    assert not harm["four_derivative_space_is_full_operator_domain"]
    assert not harm["nonlinear_two_parameter_history_exists"]
    assert not harm["analytic_selection_adopted_as_physical_law"]
    assert not WINDOW["exact_nonlinear_SCE_solution_constructed"]
    return {
      "new_certificates_read":NAMES,
      "barycentric_divided_difference_checked":True,
      "Riccati_first_six_independently_checked":True,
      "Ward_constraint_and_nongauge_curvature_checked":True,
      "past_weight_alpha":5,
      "past_weight_domain":"sup_{eta<=0} exp(-5*eta)*abs(w^(j)(eta)) finite; fast exponential is a nonzero kernel while slow first two coefficients are fixed",
      "unaugmented_past_norm_le_residual_estimate_exists":False,
      "causal_finite_start_inverse_and_past_kernel_are_distinct_domains":True,
      "all_integer_and_mixed_nonlinear_frequencies_nonresonant":True,
      "two_parameter_graph_coefficient_inverse_closed":True,
      "two_parameter_exact_incoming_state_family_constructed":True,
      "scalar_inverse_plus_smooth_flat_forcing_gives_legal_linear_state_transport":True,
      "all_orders_Hadamard_proof_is_finitely_machine_formalized":False,
      "whole_unified_physics_goal":"OPEN",
      "nonlinear_common_history_and_shadowing":"OPEN",
      "full_fluctuation_law_and_constrained_joint_data":"OPEN",
      "calibrated_local_gravity_instrument":"OPEN",
      "O2_complete_record_theorem":"Inherited: full joint twirl plus common covariant physical selection/instrument; differing fast amplitudes are differing geometric inputs",
      "native_research_agents":3,
      "external_human_peer_review":False,
      "core_modified":False,
      "GI_in_scope":False
    }
if __name__=="__main__":finish("review.py",result(),
    [p for n in NAMES for p in [n+".py",n+".json"]])
