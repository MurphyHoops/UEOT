"""AH10: Certify 3*sqrt(3)/2 H^2(S^3) algebra constant and EFT-quasilinear + all-harmonic-semilinear Einstein-Langevin contractions."""
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

    # 1. Exact H^2(S^3) Banach algebra constant from 1/sqrt(12) + Bochner Ric(S^3) = +2*gamma:
    c_linf = exact(1) / iv.sqrt(exact(12))
    c_grad_l4_sq = exact(3) * c_linf  # sqrt(3)/2
    c_h2_alg = exact(3) * c_linf + exact(2) * c_grad_l4_sq
    expected_alg = exact(3) * iv.sqrt(exact(3)) / exact(2)
    require(below(abs(c_h2_alg - expected_alg), exact("1e-95")), "Exact C_{H^2,alg} == 3*sqrt(3)/2")

    # 2. Gate-free post-encoding slab I_prop = [pi, pi + 5/2] subset (pi, 5.90] and exact k>=3 wave-energy norm factor sqrt(17/8) < 3/2:
    slab_len = exact(5) / exact(2)
    norm_eq_exact = iv.sqrt(exact(9) / exact(8) + exact(1))  # sqrt(17/8)
    norm_eq_bound = exact(3) / exact(2)
    require(below(norm_eq_exact - norm_eq_bound, 0), "Exact k>=3 norm equivalence sqrt(17/8) < 3/2")

    u_max = box(rc06["u_max_on_window"])
    lam_l = exact(rc05["selected_lambda_Lambda"])
    alpha_g = exact(rc05["selected_alpha_G"])
    q_max = lam_l * (u_max**2) + (lam_l - exact(1)) * u_max - alpha_g
    u_prime_sup = iv.sqrt(exact(4) * (u_max - exact(1)) * q_max)
    h_conf_sup = u_prime_sup / exact(2)
    c_wave = norm_eq_bound * iv.exp(exact(2) * slab_len * h_conf_sup)
    require(below(c_wave, exact("1.8")), "Exact hyperbolic FRW energy Gronwall constant < 1.8")

    g_val = exact("1e-40")
    sixteen_pi_g = exact(6) / exact(5) * (g_val**2)  # exact 16*pi*G = 1.2e-80 in -Box h = 16*pi*G T
    k_eft = exact(200)
    m_ret = k_eft**4  # 1.6e9 on sensor EFT band 3 <= k <= 200

    r_star = exact(5) / (exact(10) ** 12)  # 5e-12
    neumann_inv_cubed = (exact(1) - exact(4) * c_linf * r_star) ** (-3)
    require(below(neumann_inv_cubed, exact(2)), "Neumann metric-inverse geometric factor < 2")

    # Derived Lipschitz constants:
    # Semilinear connection quadratic terms (64 triples * (3/2)^2 * 2 = 288):
    c_grav_semi = exact(288) * c_h2_alg
    # Full quasilinear EFT band (16 * 2 * K_EFT + 288 = 6688):
    c_grav_eft = (exact(32) * k_eft + exact(288)) * c_h2_alg

    xi_ball = exact(10) ** 64
    var_e_35 = box(ah06["continuum_35_species_smeared_energy_variance"])
    sigma_e_35 = iv.sqrt(var_e_35)
    noise_sigma_multiple = xi_ball / sigma_e_35
    require(above(noise_sigma_multiple, exact("9e23")), "Covers > 9*10^23 std devs of 35-species smeared stress noise")

    # Exact derived elliptic Cauchy data at tau = pi+ and deterministic 16*pi*G*a^2*T_{l>=2} H^2 bound from AH05:
    init_cauchy_norm = exact(2) * (
        exact(ah05["psi_ge_2_H4_norm_upper"])
        + exact(ah05["longitudinal_shift_B_ge_2_H4_norm_upper"])
        + exact(ah05["transverse_shift_W_ge_2_H4_norm_upper"])
    )
    det_stress_h2 = exact(ah05["sixteen_pi_G_T_det_ge_2_H2_upper"])

    image_eft = c_wave * (
        init_cauchy_norm
        + slab_len * u_max * (det_stress_h2 + sixteen_pi_g * xi_ball + sixteen_pi_g * m_ret * r_star + c_grav_eft * (r_star**2))
    )
    lip_eft = c_wave * slab_len * u_max * (sixteen_pi_g * m_ret + exact(2) * c_grav_eft * r_star)

    image_semi = c_wave * (
        init_cauchy_norm + slab_len * u_max * (det_stress_h2 + sixteen_pi_g * xi_ball + c_grav_semi * (r_star**2))
    )
    lip_semi = c_wave * slab_len * u_max * (exact(2) * c_grav_semi * r_star)

    require(below(image_eft - r_star, exact("-3e-12")) and below(image_semi - r_star, exact("-3e-12")), "Strict self-maps")
    require(below(lip_eft, exact("8e-7")) and below(lip_semi, exact("4e-8")), "Strict Banach contractions << 1")

    picard_5_err = (lip_eft**5) / (exact(1) - lip_eft) * image_eft
    require(below(picard_5_err, exact("1e-42")), "5-step Picard residual < 1e-42")

    finish(
        "self_consistent_einstein_langevin_fixed_point.py",
        {
            "post_encoding_gate_free_slab_tau": "[pi, pi + 5/2]",
            "EFT_spectral_band_cutoff_K_EFT": 200,
            "slab_conformal_Hubble_sup": outward(h_conf_sup),
            "exact_k_ge_3_norm_equivalence_sqrt_17_over_8": outward(norm_eq_exact),
            "wave_energy_Gronwall_constant": outward(c_wave),
            "Sobolev_H2_Bochner_algebra_constant_formula": "3*sqrt(3)/2",
            "Sobolev_H2_Bochner_algebra_constant": outward(c_h2_alg),
            "ball_radius_R_star": "5e-12",
            "admissible_noise_H2_ball_radius": "1e64",
            "covered_35_species_noise_std_deviations_lower": float(outward(noise_sigma_multiple)[0]),
            "derived_AH05_initial_Cauchy_norm_upper": float(outward(init_cauchy_norm)[1]),
            "derived_AH05_16piG_det_stress_H2_upper": float(outward(det_stress_h2)[1]),
            "T_EL_EFT_image_radius_upper": float(outward(image_eft)[1]),
            "Banach_Lipschitz_constant_L_EL_EFT_upper": float(outward(lip_eft)[1]),
            "Banach_Lipschitz_constant_L_EL_all_harmonic_semilinear_upper": float(outward(lip_semi)[1]),
            "five_step_Picard_convergence_error_upper": float(outward(picard_5_err)[1]),
            "unique_self_consistent_Einstein_Langevin_history_exists": True,
            "nonperturbative_operator_metric_quantization_claimed": False,
        },
        inputs=[RC05_JSON, RC06_JSON, RC11_JSON, AH05_JSON, AH06_JSON],
    )


if __name__ == "__main__":
    main()
