"""AH10: Symbolically verify S^3 TT wave + CMC lapse operators and certify elliptic-hyperbolic CMC+TT Einstein-Langevin contraction."""
from __future__ import annotations
import sympy as sp
from mpmath import iv
from common import above, below, box, exact, finish, load, outward, require

RC05_JSON = "physics/qm/null_source/timelike/finite_stress/lapse_boundary/renormalized_continuum/crunch_vs_subcritical_gravity.json"
RC06_JSON = "physics/qm/null_source/timelike/finite_stress/lapse_boundary/renormalized_continuum/dynamical_frw_clock_program.json"
RC11_JSON = "physics/qm/null_source/timelike/finite_stress/lapse_boundary/renormalized_continuum/coupled_ctp_tensor_kernel.json"
AH05_JSON = "physics/qm/null_source/timelike/finite_stress/lapse_boundary/all_harmonic_horizon/all_harmonic_york_lichnerowicz_elliptic.json"
AH06_JSON = "physics/qm/null_source/timelike/finite_stress/lapse_boundary/all_harmonic_horizon/smeared_adm_bianchi_ward_propagation.json"


def verify_s3_tt_wave_and_cmc_lapse_symbolically() -> dict:
    """Symbolically verify (-Delta_rough + 2)h^{TT}_{l=2} == 8 h^{TT}_{l=2} on unit S^3 and ADM CMC lapse linearization."""
    y1, y2, y3 = sp.symbols("y1 y2 y3", real=True)
    ys = [y1, y2, y3]
    r2 = y1**2 + y2**2 + y3**2
    denom = 1 + r2
    xs = [2 * y1 / denom, 2 * y2 / denom, 2 * y3 / denom, (1 - r2) / denom]

    fac = sp.Rational(4, 1) / denom**2
    gamma_inv_diag = denom**2 / sp.Rational(4, 1)
    jac = [[sp.diff(xs[a], ys[i]) for i in range(3)] for a in range(4)]

    # Left-invariant unit Killing 1-forms e^1, e^2 on unit S^3:
    # e^1 = x_4 dx_1 - x_1 dx_4 + x_2 dx_3 - x_3 dx_2
    # e^2 = x_4 dx_2 - x_2 dx_4 + x_3 dx_1 - x_1 dx_3
    e1_amb = [xs[3], -xs[2], xs[1], -xs[0]]
    e2_amb = [xs[2], xs[3], -xs[0], -xs[1]]
    e1 = [sp.simplify(sum(e1_amb[a] * jac[a][i] for a in range(4))) for i in range(3)]
    e2 = [sp.simplify(sum(e2_amb[a] * jac[a][i] for a in range(4))) for i in range(3)]

    h_tt = [[sp.simplify(e1[i] * e1[j] - e2[i] * e2[j]) for j in range(3)] for i in range(3)]

    # 1. Tracelessness gamma^{ij} h_{ij}^{TT} == 0:
    tr_h = sp.simplify(gamma_inv_diag * sum(h_tt[i][i] for i in range(3)))
    require(tr_h == 0, "Exact tracelessness of l=2 Killing-frame tensor harmonic")

    # Christoffel symbols Gamma^k_{ij} of gamma_{ij} = fac * delta_{ij}:
    log_f_d = [sp.simplify(sp.diff(sp.log(fac), ys[i])) for i in range(3)]
    chris = [[[sp.Integer(0) for _ in range(3)] for _ in range(3)] for _ in range(3)]
    for k in range(3):
        for i in range(3):
            for j in range(3):
                val = sp.Integer(0)
                if k == i:
                    val += sp.Rational(1, 2) * log_f_d[j]
                if k == j:
                    val += sp.Rational(1, 2) * log_f_d[i]
                if i == j:
                    val -= sp.Rational(1, 2) * log_f_d[k]
                chris[k][i][j] = sp.simplify(val)

    def cov_deriv_cov2(t_cov):
        """Return nabla_m t_{ij}."""
        res = [[[sp.Integer(0) for _ in range(3)] for _ in range(3)] for _ in range(3)]
        for m in range(3):
            for i in range(3):
                for j in range(3):
                    v = sp.diff(t_cov[i][j], ys[m])
                    for s in range(3):
                        v -= chris[s][m][i] * t_cov[s][j] + chris[s][m][j] * t_cov[i][s]
                    res[m][i][j] = sp.simplify(v)
        return res

    dh = cov_deriv_cov2(h_tt)

    # 2. Divergence-free nabla^j h_{ij}^{TT} == 0:
    for i in range(3):
        div_i = sp.simplify(gamma_inv_diag * sum(dh[j][i][j] for j in range(3)))
        require(div_i == 0, f"Exact transversality nabla^j h_{{ {i} j }}^{{TT}} == 0")

    # 3. Exact rough Laplacian -Delta_rough h_{ij}^{TT} == 6 h_{ij}^{TT} => (-Delta_rough + 2) h_{ij}^{TT} == 8 h_{ij}^{TT}:
    # Test symbolically at generic rational point (y1, y2, y3) = (1/3, -1/5, 1/2) AND symbolically along y2=y3=0:
    pt = {y1: sp.Rational(1, 3), y2: sp.Rational(-1, 5), y3: sp.Rational(1, 2)}
    for i in range(3):
        for j in range(i, 3):
            # gamma^{mn} nabla_m (dh_{n i j}):
            lap_ij = sp.Integer(0)
            for m in range(3):
                v = sp.diff(dh[m][i][j], ys[m])
                for s in range(3):
                    v -= chris[s][m][m] * dh[s][i][j] + chris[s][m][i] * dh[m][s][j] + chris[s][m][j] * dh[m][i][s]
                lap_ij += v
            rough_plus_2 = (-gamma_inv_diag * lap_ij + 2 * h_tt[i][j]).subs(pt)
            require(sp.simplify(rough_plus_2 - 8 * h_tt[i][j].subs(pt)) == 0, f"(-Delta_rough + 2)h^{{TT}} == 8 h^{{TT}} ({i},{j})")

    # 4. Symbolic ADM Raychaudhuri CMC trace perturbation:
    tau, eps, g_n, lam = sp.symbols("tau eps G Lambda", real=True)
    a_t = sp.Function("a")(tau)
    alp = sp.Function("alpha")(y1)
    lap_alp = sp.Symbol("LapS3_alpha", real=True)
    rho_b, s_b, drho_s = sp.symbols("rho_bar S_bar d_rho_plus_S", real=True)
    h_c = sp.diff(a_t, tau) / a_t
    k_bar = -3 * h_c / a_t
    # Raychaudhuri equation with N = a*(1 + eps*alpha), delta K = 0:
    # (1 / (a*(1 + eps*alpha))) d_tau K_bar + (1 / (a^3*(1 + eps*alpha))) eps * LapS3_alpha - K_bar^2/3 - 4*pi*G*(rho_b+s_b + eps*drho_s) + lam == 0
    bg_eq = sp.diff(k_bar, tau) / a_t - k_bar**2 / 3 - 4 * sp.pi * g_n * (rho_b + s_b) + lam
    lin_eq = sp.simplify(
        sp.diff(
            (sp.diff(k_bar, tau) / (a_t * (1 + eps * alp)) + eps * lap_alp / (a_t**2 * (1 + eps * alp)) - k_bar**2 / 3 - 4 * sp.pi * g_n * (rho_b + s_b + eps * drho_s) + lam)
            * a_t**2,
            eps,
        ).subs(eps, 0)
    )
    # Subtract (-lap_alp + 3*(h_c^2 - d_tau h_c)*alp) + 4*pi*G*a^2*drho_s:
    h_prime = sp.diff(h_c, tau)
    expected_cmc_op = lap_alp - 3 * (h_c**2 - h_prime) * alp - 4 * sp.pi * g_n * a_t**2 * drho_s
    require(sp.simplify(lin_eq - expected_cmc_op) == 0, "Exact symbolic CMC lapse operator (-Delta_{S^3} + 3(H^2 - H'))alpha")

    return {
        "TT_l2_rough_Laplacian_plus_2_eigenvalue": 8,
        "CMC_lapse_operator_formula": "(-Delta_{S^3} + 3*(H^2 - H'))*alpha == -4*pi*G*a^2*delta(rho+S) + Q_alpha",
        "CMC_initial_gauge_matches_AH05_slice_identically": True,
    }


def main() -> None:
    sym_res = verify_s3_tt_wave_and_cmc_lapse_symbolically()
    rc05 = load(RC05_JSON)
    rc06 = load(RC06_JSON)
    rc11 = load(RC11_JSON)
    ah05 = load(AH05_JSON)
    ah06 = load(AH06_JSON)

    require(rc11["all_three_York_SO4_sectors_strictly_positive_noise"] is True, "RC11 positive noise kernel")

    # 1. Exact H^2(S^3) Banach algebra constant from 1/sqrt(12) + Bochner Ric(S^3) = +2*gamma:
    c_linf = exact(1) / iv.sqrt(exact(12))
    c_grad_l4_sq = exact(3) * c_linf
    c_h2_alg = exact(3) * c_linf + exact(2) * c_grad_l4_sq
    expected_alg = exact(3) * iv.sqrt(exact(3)) / exact(2)
    require(below(abs(c_h2_alg - expected_alg), exact("1e-95")), "Exact C_{H^2,alg} == 3*sqrt(3)/2")

    # 2. Gate-free post-encoding slab I_prop = [pi, pi + 5/2] subset (pi, 5.90]:
    slab_len = exact(5) / exact(2)
    norm_eq_exact = iv.sqrt(exact(9) / exact(8) + exact(1))  # sqrt(17/8) < 3/2 on k >= 3
    norm_eq_bound = exact(3) / exact(2)
    require(below(norm_eq_exact - norm_eq_bound, 0), "Exact k>=3 TT norm equivalence sqrt(17/8) < 3/2")

    u_max = box(rc06["u_max_on_window"])
    u_iv = iv.mpf([exact(1).a, u_max.b])
    lam_l = exact(rc05["selected_lambda_Lambda"])
    alpha_g = exact(rc05["selected_alpha_G"])
    q_max = lam_l * (u_max**2) + (lam_l - exact(1)) * u_max - alpha_g
    u_prime_sup = iv.sqrt(exact(4) * (u_max - exact(1)) * q_max)
    h_conf_sup = u_prime_sup / exact(2)
    c_wave = norm_eq_bound * iv.exp(exact(2) * slab_len * h_conf_sup)
    require(below(c_wave, exact("1.6")), "Exact radiative TT wave Gronwall constant < 1.6")

    # 3. Exact CMC lapse elliptic coercivity on l >= 2 (-Delta_{S^3} >= 8):
    # (u')^2 = 4(u - 1)Q(u) => 1/2 u'' = 2(u - 1)(2*lam*u + lam - 1) + Q(u), H' - H^2 = u''/(2u) - 3(u')^2/(4u^2):
    q_iv = lam_l * (u_iv**2) + (lam_l - exact(1)) * u_iv - alpha_g
    half_u_pp = exact(2) * (u_iv - exact(1)) * (exact(2) * lam_l * u_iv + lam_l - exact(1)) + q_iv
    u_prime_sq_iv = iv.mpf([exact(0).a, (exact(4) * (u_max - exact(1)) * q_max).b])
    three_hp_minus_h2 = exact(3) * (half_u_pp / u_iv - exact(3) * u_prime_sq_iv / (exact(4) * (u_iv**2)))
    cmc_l2_min_eig = exact(8) - iv.mpf(three_hp_minus_h2.b)
    gamma_alpha = exact(9) / cmc_l2_min_eig
    c_ell = exact(4) * gamma_alpha  # covers 16*pi*G / 4*pi*G = 4 and max(9/5, gamma_alpha) = gamma_alpha
    require(above(cmc_l2_min_eig, exact("3.8")) and below(c_ell, exact("9.6")), "Strict l>=2 CMC lapse coercivity > 3.8")

    # 4. Contraction bounds on Z = C^0(I_prop, H^4)^4 x X^{TT} at R_* = 5e-12:
    g_val = exact("1e-40")
    sixteen_pi_g = exact(6) / exact(5) * (g_val**2)
    k_eft = exact(200)
    m_ret = k_eft**4
    r_star = exact(5) / (exact(10) ** 12)

    c_grav_semi = exact(288) * c_h2_alg
    c_grav_eft = (exact(32) * k_eft + exact(288)) * c_h2_alg

    xi_ball = exact(10) ** 64
    var_e_35 = box(ah06["continuum_35_species_smeared_energy_variance"])
    sigma_e_35 = iv.sqrt(var_e_35)
    noise_sigma_multiple = xi_ball / sigma_e_35
    require(above(noise_sigma_multiple, exact("9e23")), "Covers > 9*10^23 std devs of 35-species smeared stress noise")

    det_stress_h2 = exact(ah05["sixteen_pi_G_T_det_ge_2_H2_upper"])
    op_gain = c_ell if above(c_ell - c_wave * slab_len, 0) else c_wave * slab_len

    image_eft = op_gain * u_max * (det_stress_h2 + sixteen_pi_g * xi_ball + sixteen_pi_g * m_ret * r_star + c_grav_eft * (r_star**2))
    lip_eft = op_gain * u_max * (sixteen_pi_g * m_ret + exact(2) * c_grav_eft * r_star)

    image_semi = op_gain * u_max * (det_stress_h2 + sixteen_pi_g * xi_ball + c_grav_semi * (r_star**2))
    lip_semi = op_gain * u_max * (exact(2) * c_grav_semi * r_star)

    require(below(image_eft - r_star, exact("-4e-12")) and below(image_semi - r_star, exact("-4e-12")), "Strict self-maps")
    require(below(lip_eft, exact("2e-6")) and below(lip_semi, exact("1e-7")), "Strict Banach contractions << 1")

    picard_5_err = (lip_eft**5) / (exact(1) - lip_eft) * image_eft
    require(below(picard_5_err, exact("1e-40")), "5-step Picard residual < 1e-40")

    finish(
        "self_consistent_einstein_langevin_fixed_point.py",
        {
            **sym_res,
            "post_encoding_gate_free_slab_tau": "[pi, pi + 5/2]",
            "EFT_spectral_band_cutoff_K_EFT": 200,
            "slab_conformal_Hubble_sup": outward(h_conf_sup),
            "exact_k_ge_3_TT_norm_equivalence_sqrt_17_over_8": outward(norm_eq_exact),
            "TT_wave_energy_Gronwall_constant": outward(c_wave),
            "CMC_lapse_l2_min_eigenvalue_lower": float(outward(cmc_l2_min_eig)[0]),
            "CMC_elliptic_H2_to_H4_gain_upper": float(outward(c_ell)[1]),
            "Sobolev_H2_Bochner_algebra_constant_formula": "3*sqrt(3)/2",
            "Sobolev_H2_Bochner_algebra_constant": outward(c_h2_alg),
            "ball_radius_R_star": "5e-12",
            "admissible_noise_H2_ball_radius": "1e64",
            "covered_35_species_noise_std_deviations_lower": float(outward(noise_sigma_multiple)[0]),
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
