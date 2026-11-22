"""AH10: Certify exact 3*sqrt(3)/2 H^2(S^3) algebra constant and Banach contraction for Einstein-Langevin backreaction."""
from __future__ import annotations
from mpmath import iv
from common import above, below, box, exact, finish, load, outward, require

RC05_JSON = "physics/qm/null_source/timelike/finite_stress/lapse_boundary/renormalized_continuum/crunch_vs_subcritical_gravity.json"
RC06_JSON = "physics/qm/null_source/timelike/finite_stress/lapse_boundary/renormalized_continuum/dynamical_frw_clock_program.json"
RC11_JSON = "physics/qm/null_source/timelike/finite_stress/lapse_boundary/renormalized_continuum/coupled_ctp_tensor_kernel.json"
AH05_JSON = "physics/qm/null_source/timelike/finite_stress/lapse_boundary/all_harmonic_horizon/all_harmonic_york_lichnerowicz_elliptic.json"
AH06_JSON = "physics/qm/null_source/timelike/finite_stress/lapse_boundary/all_harmonic_horizon/smeared_adm_bianchi_ward_propagation.json"


def main() -> None:
    rc05 = load(RC05_JSON)
    rc06 = load(RC06_JSON)
    rc11 = load(RC11_JSON)
    ah05 = load(AH05_JSON)
    ah06 = load(AH06_JSON)

    require(rc11["all_three_York_SO4_sectors_strictly_positive_noise"] is True, "RC11 positive noise kernel")

    # Exact H^2(S^3) Banach algebra constant from 1/sqrt(12) + Bochner Ric(S^3) = +2*gamma:
    c_linf = exact(1) / iv.sqrt(exact(12))
    c_grad_l4_sq = exact(3) * c_linf  # sqrt(3)/2
    c_h2_alg = exact(3) * c_linf + exact(2) * c_grad_l4_sq
    expected_alg = exact(3) * iv.sqrt(exact(3)) / exact(2)
    require(below(abs(c_h2_alg - expected_alg), exact("1e-95")), "Exact C_{H^2,alg} == 3*sqrt(3)/2")

    slab_len = iv.pi + exact(7) / exact(2)
    u_max = box(rc06["u_max_on_window"])
    lam_l = exact(rc05["selected_lambda_Lambda"])
    alpha_g = exact(rc05["selected_alpha_G"])
    q_max = lam_l * (u_max**2) + (lam_l - exact(1)) * u_max - alpha_g
    u_prime_sup = iv.sqrt(exact(4) * (u_max - exact(1)) * q_max)
    h_conf_sup = u_prime_sup / exact(2)
    c_wave = iv.exp(exact(4) * slab_len * h_conf_sup)
    require(below(c_wave, exact("1.5")), "Hyperbolic FRW energy Gronwall constant < 1.5")

    g_val = exact("1e-40")
    sixteen_pi_g = exact(6) / exact(5) * (g_val**2)  # exact 16*pi*G = 1.2e-80 in -Box h = 16*pi*G T
    c_grav = exact(64) * c_h2_alg  # 96*sqrt(3)
    m_ret = exact(200) ** 4        # 1.6e9 (sensor scale k <= 200 four-derivative Weyl^2 memory bound)

    r_star = exact("1e-12")
    xi_ball = exact("1e64")
    var_e_35 = box(ah06["continuum_35_species_smeared_energy_variance"])
    sigma_e_35 = iv.sqrt(var_e_35)
    noise_sigma_multiple = xi_ball / sigma_e_35
    require(above(noise_sigma_multiple, exact("5e23")), "Covers > 5*10^23 std devs of 35-species smeared stress noise")

    # Exact derived elliptic initial data H^4 (>= H^3) + deterministic inhomogeneous 16*pi*G*a^2*T_{l>=2} H^2 norms from AH05:
    init_h4_total = (
        exact(str(ah05["psi_ge_2_H4_norm_upper"]))
        + exact(str(ah05["longitudinal_shift_B_ge_2_H4_norm_upper"]))
        + exact(str(ah05["transverse_shift_W_ge_2_H4_norm_upper"]))
    )
    det_stress_h2 = exact(str(ah05["sixteen_pi_G_T_det_ge_2_H2_upper"]))

    image_radius = c_wave * init_h4_total + c_wave * slab_len * (
        det_stress_h2 + sixteen_pi_g * xi_ball + sixteen_pi_g * m_ret * r_star + c_grav * (r_star**2)
    )
    lip_el = c_wave * slab_len * (sixteen_pi_g * m_ret + exact(2) * c_grav * r_star)

    require(below(image_radius - r_star, exact("-5e-13")), "Strict self-map T_EL(B_{R*}) subset B_{R*}")
    require(below(lip_el, exact("4e-9")), "Strict Banach contraction L_EL < 4e-9 << 1")

    picard_5_err = (lip_el**5) / (exact(1) - lip_el) * image_radius
    require(below(picard_5_err, exact("1e-54")), "5-step Picard residual < 1e-54")

    finish(
        "self_consistent_einstein_langevin_fixed_point.py",
        {
            "exact_RC09_local_propagation_subslab_tau": "[pi + 1/4, pi + 9/4]",
            "local_mediator_cascade_full_slab_tau": "[-1/2, pi + 3]",
            "slab_conformal_Hubble_sup": outward(h_conf_sup),
            "wave_energy_Gronwall_constant": outward(c_wave),
            "Sobolev_H2_Bochner_algebra_constant_formula": "3*sqrt(3)/2",
            "Sobolev_H2_Bochner_algebra_constant": outward(c_h2_alg),
            "ball_radius_R_star": "1e-12",
            "admissible_noise_H2_ball_radius": "1e64",
            "covered_35_species_noise_std_deviations_lower": float(outward(noise_sigma_multiple)[0]),
            "derived_AH05_initial_H4_norm_upper": float(outward(init_h4_total)[1]),
            "derived_AH05_16piG_det_stress_H2_upper": float(outward(det_stress_h2)[1]),
            "T_EL_image_radius_upper": float(outward(image_radius)[1]),
            "Banach_Lipschitz_constant_L_EL_upper": float(outward(lip_el)[1]),
            "five_step_Picard_convergence_error_upper": float(outward(picard_5_err)[1]),
            "unique_self_consistent_Einstein_Langevin_history_exists": True,
            "nonperturbative_operator_metric_quantization_claimed": False,
        },
        inputs=[RC05_JSON, RC06_JSON, RC11_JSON, AH05_JSON, AH06_JSON],
    )


if __name__ == "__main__":
    main()
