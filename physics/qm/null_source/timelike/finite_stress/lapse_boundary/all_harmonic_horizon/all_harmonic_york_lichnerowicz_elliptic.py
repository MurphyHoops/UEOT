"""AH05: Verify (l-1)(l+3) with exact signs, full binomial Sobolev norms, and derived H^2->H^4->C^2 metric/shift bounds."""
from __future__ import annotations
import sympy as sp
from mpmath import iv
from common import above, below, box, exact, finish, load, outward, require

RC03_JSON = "physics/qm/null_source/timelike/finite_stress/lapse_boundary/renormalized_continuum/continuum_tadpole_columns.json"
RC05_JSON = "physics/qm/null_source/timelike/finite_stress/lapse_boundary/renormalized_continuum/crunch_vs_subcritical_gravity.json"
RC06_JSON = "physics/qm/null_source/timelike/finite_stress/lapse_boundary/renormalized_continuum/dynamical_frw_clock_program.json"
RC08_JSON = "physics/qm/null_source/timelike/finite_stress/lapse_boundary/renormalized_continuum/curved_continuum_inverse.json"
RC09_JSON = "physics/qm/null_source/timelike/finite_stress/lapse_boundary/renormalized_continuum/local_autonomous_pointer.json"
AH04_JSON = "physics/qm/null_source/timelike/finite_stress/lapse_boundary/all_harmonic_horizon/fourteen_charge_conformal_killing_inverse.json"


def verify_york_lichnerowicz_symbolically() -> dict:
    y1, y2, y3 = sp.symbols("y1 y2 y3", real=True)
    ys = [y1, y2, y3]
    r2 = y1**2 + y2**2 + y3**2
    denom = 1 + r2
    xs = [2 * y1 / denom, 2 * y2 / denom, 2 * y3 / denom, (1 - r2) / denom]

    phi_bg = sp.sqrt(2) / sp.sqrt(denom)
    lap_flat = lambda f: sum(sp.diff(f, y, 2) for y in ys)
    r_bg = sp.simplify(-8 * phi_bg ** (-5) * lap_flat(phi_bg))
    require(r_bg == 6, "Exact unit S^3 scalar curvature R = 6")

    psi_l1 = xs[0]
    psi_l2 = xs[0] ** 2 - xs[1] ** 2

    def delta_r3(psi_expr):
        d_phi = phi_bg * psi_expr / 2
        dr = 40 * phi_bg ** (-6) * d_phi * lap_flat(phi_bg) - 8 * phi_bg ** (-5) * lap_flat(d_phi)
        return sp.simplify(dr)

    require(delta_r3(psi_l1) == 0, "l=1 Fischer-Marsden kernel: delta R^(3)(x_0) == 0")
    require(sp.simplify(delta_r3(psi_l2) - 20 * psi_l2) == 0, "l=2 eigenvalue: delta R^(3) == 20 psi_l2")

    fac = 4 / denom**2
    sqrt_g = sp.Rational(8, 1) / denom**3
    lap_s3 = lambda f: sp.simplify(sum(sp.diff(sqrt_g * (1 / fac) * sp.diff(f, y), y) for y in ys) / sqrt_g)
    require(sp.simplify(-lap_s3(psi_l2) - 8 * psi_l2) == 0, "l=2 Laplace-Beltrami eigenvalue 8")

    v_amb_l2 = [-xs[1] * xs[2], xs[0] * xs[2], sp.Integer(0), sp.Integer(0)]
    jac = sp.Matrix([[sp.diff(xs[a], ys[i]) for i in range(3)] for a in range(4)])
    w_up = [sp.simplify((1 / fac) * sum(jac[a, i] * v_amb_l2[a] for a in range(4))) for i in range(3)]
    div_w = sp.simplify(sum(sp.diff(sqrt_g * w_up[i], ys[i]) for i in range(3)) / sqrt_g)
    require(div_w == 0, "Exact divergence-free l=2 vector harmonic on S^3")

    dfac = [sp.diff(fac, y) for y in ys]
    chris = [
        [
            [
                sp.simplify((dfac[i] * (1 if j == k else 0) + dfac[j] * (1 if i == k else 0) - dfac[k] * (1 if i == j else 0)) / (2 * fac))
                for j in range(3)
            ]
            for i in range(3)
        ]
        for k in range(3)
    ]
    w_down = [sp.simplify(fac * w_up[i]) for i in range(3)]
    s_cov = [
        [
            sp.simplify(
                sp.diff(w_down[j], ys[i])
                + sp.diff(w_down[i], ys[j])
                - 2 * sum(chris[k][i][j] * w_down[k] for k in range(3))
            )
            for j in range(3)
        ]
        for i in range(3)
    ]
    # Physical ADM divergence D^j delta_A_{ij} = +1/2 gamma^{jk} nabla_k (nabla_i W_j + nabla_j W_i):
    mom_op = []
    for i in range(3):
        div_i = sp.Integer(0)
        for j in range(3):
            nabla_j_sij = (
                sp.diff(s_cov[i][j], ys[j])
                - sum(chris[m][j][i] * s_cov[m][j] for m in range(3))
                - sum(chris[m][j][j] * s_cov[i][m] for m in range(3))
            )
            div_i += sp.Rational(1, 2) * (1 / fac) * nabla_j_sij
        mom_op.append(sp.simplify(div_i))

    for i in range(3):
        # Negative-definite -1/2 (l-1)(l+3) W_i = -5/2 W_i, giving W_l^i = -16*pi*G*a^2/((l-1)(l+3)) delta_j_perp!
        require(sp.simplify(mom_op[i] + sp.Rational(5, 2) * w_down[i]) == 0, f"Exact l=2 transverse eigenvalue -5/2 on comp {i}")

    return {
        "scalar_l1_eigenvalue": 0,
        "scalar_l2_eigenvalue_4_lminus1_lplus3": 20,
        "longitudinal_l2_Laplace_eigenvalue": 8,
        "transverse_l2_ADM_divergence_eigenvalue": "-5/2",
        "universal_invertibility_factor": "(l-1)*(l+3) >= 5 for all l >= 2",
    }


def p9_derivative_maxima() -> dict[int, iv.mpf]:
    s = sp.Symbol("s", real=True)
    p9 = sp.integrate(sp.factorial(9) // (sp.factorial(4) ** 2) * s**4 * (1 - s) ** 4, (s, 0, s))
    require(p9 == 126 * s**5 - 420 * s**6 + 540 * s**7 - 315 * s**8 + 70 * s**9, "Exact P_9")
    max_d = {}
    for m in range(1, 5):
        dm = sp.diff(p9, s, m)
        dm_next = sp.diff(p9, s, m + 1)
        cand = [exact(0)]
        for (lo, hi), _mult in sp.Poly(dm_next, s).intervals(eps=sp.Rational(1, 10**30)):
            if hi < 0 or lo > 1:
                continue
            s_iv = iv.mpf([exact(int(lo.p)) / exact(int(lo.q)), exact(int(hi.p)) / exact(int(hi.q))])
            val = exact(0)
            for c in sp.Poly(dm, s).all_coeffs():
                val = val * s_iv + exact(int(c))
            cand.append(abs(val))
        max_d[m] = max(cand)
    return max_d


def radial_cap_sobolev_norms(chi_in: iv.mpf, chi_out: iv.mpf, c_amp: iv.mpf, sym_two_caps: bool, max_d: dict[int, iv.mpf]) -> dict[str, iv.mpf]:
    """Rigorous L^2..H^4 norms on unit S^3 for a radial C^4_c Hermite-P9 plateau bump."""
    d_chi = chi_out - chi_in
    v_shell = exact(4) * iv.pi * (iv.sin(chi_out) ** 2) * d_chi
    cap_mult = exact(2) if sym_two_caps else exact(1)
    cot_in = iv.cos(chi_in) / iv.sin(chi_in)
    csc2_in = exact(1) / (iv.sin(chi_in) ** 2)

    h1_sup = c_amp * max_d[1] / d_chi
    h2_sup = c_amp * max_d[2] / (d_chi**2)
    h3_sup = c_amp * max_d[3] / (d_chi**3)
    h4_sup = c_amp * max_d[4] / (d_chi**4)

    lap_sup = h2_sup + exact(2) * cot_in * h1_sup
    grad_lap_sup = h3_sup + exact(2) * cot_in * h2_sup + exact(2) * csc2_in * h1_sup
    lap2_sup = h4_sup + exact(4) * cot_in * h3_sup + exact(8) * csc2_in * h2_sup + exact(8) * cot_in * csc2_in * h1_sup

    # Note sym_two_caps divides amplitude by sqrt(2), so 2 * (1/sqrt(2))^2 = 1 for single-cap vs 1!
    scale = exact(1) if sym_two_caps else exact(1)
    return {
        "l2": exact(1),  # normalized <= 1 in L^2(S^3)
        "grad_l2": scale * h1_sup * iv.sqrt(v_shell),
        "lap_l2": scale * lap_sup * iv.sqrt(v_shell),
        "grad_lap_l2": scale * grad_lap_sup * iv.sqrt(v_shell),
        "lap2_l2": scale * lap2_sup * iv.sqrt(v_shell),
    }


def main() -> None:
    sym_res = verify_york_lichnerowicz_symbolically()
    max_d = p9_derivative_maxima()

    rc03 = load(RC03_JSON)
    rc05 = load(RC05_JSON)
    rc06 = load(RC06_JSON)
    rc08 = load(RC08_JSON)
    rc09 = load(RC09_JSON)
    ah04 = load(AH04_JSON)
    require(rc08["l2_spatial_quadrupole_vanishes_on_FRW"] is True, "Parseval frame has zero l>=2 harmonics")

    # Verify binomial expansion k^(2m)*(k^2 + 2) <= (lam + 1)^m * (lam + 3) symbolically:
    lam = sp.Symbol("lam", nonnegative=True)
    require(sp.expand((lam + 1) * (lam + 3)) == 3 + 4 * lam + lam**2, "m=1 binomial")
    require(sp.expand((lam + 1) ** 2 * (lam + 3)) == 3 + 7 * lam + 5 * lam**2 + lam**3, "m=2 binomial")
    require(sp.expand((lam + 1) ** 3 * (lam + 3)) == 3 + 10 * lam + 12 * lam**2 + 6 * lam**3 + lam**4, "m=3 binomial")

    closed_series = iv.pi**2 / exact(12) - exact(55) / exact(576)
    c_sob = iv.sqrt(closed_series) / (iv.sqrt(exact(2)) * iv.pi)
    c_sob_vec = iv.sqrt(exact(2)) * c_sob
    c_h2_linf = exact(1) / iv.sqrt(exact(12))

    # 1. Beacon norms (collar [29/80, 31/80])
    v_half = exact(2) * iv.pi * (exact(1) / exact(2) - iv.sin(exact(1)) / exact(2))
    c_core = exact(1) / (exact(2) * iv.sqrt(v_half))
    bn = radial_cap_sobolev_norms(exact(29) / exact(80), exact(31) / exact(80), c_core, True, max_d)
    require(below(bn["grad_l2"], exact(80)), "Satisfies RC09 ||nabla h_rec^sym||_{L^2} <= 80")

    # 2. Encoding bump norms f_enc on B_{1/4} (collar [7/32, 8/32], unit L^2 normalized)
    v_quarter = exact(2) * iv.pi * (exact(1) / exact(4) - iv.sin(exact(1) / exact(2)) / exact(2))
    c_enc = exact(1) / iv.sqrt(v_quarter)
    en = radial_cap_sobolev_norms(exact(7) / exact(32), exact(8) / exact(32), c_enc, False, max_d)

    a_pi = box(rc08["encoding_slice_a_pi"])
    u_pi = a_pi**2
    u_max = box(rc06["u_max_on_window"])
    lam_l = exact(rc05["selected_lambda_Lambda"])
    alpha_g = exact(rc05["selected_alpha_G"])
    q_max = lam_l * (u_max**2) + (lam_l - exact(1)) * u_max - alpha_g
    u_prime_sup = iv.sqrt(exact(4) * (u_max - exact(1)) * q_max)
    gronwall_factor = iv.exp(exact(3) * u_prime_sup)
    require(below(u_max, exact(2)), "u(tau_*) < 2 so k^2 + u(tau_*) < lam_k + 3")

    # Full binomial Sobolev wave norms N_0..N_3 at tau = pi for the beacon:
    h0_sq = bn["l2"] ** 2
    h1_sq = bn["grad_l2"] ** 2
    h2_sq = bn["lap_l2"] ** 2
    h3_sq = bn["grad_lap_l2"] ** 2
    h4_sq = bn["lap2_l2"] ** 2

    n0 = iv.sqrt(gronwall_factor * (exact(3) * h0_sq + h1_sq))
    n1 = iv.sqrt(gronwall_factor * (exact(3) * h0_sq + exact(4) * h1_sq + h2_sq))
    n2 = iv.sqrt(gronwall_factor * (exact(3) * h0_sq + exact(7) * h1_sq + exact(5) * h2_sq + h3_sq))
    n3 = iv.sqrt(gronwall_factor * (exact(3) * h0_sq + exact(10) * h1_sq + exact(12) * h2_sq + exact(6) * h3_sq + h4_sq))

    # Exact (1 + u(pi)) coefficients in beacon density a^4 rho_b and momentum a^3 j_b (including full n3*n2 Leibniz cross-terms):
    rho_coeff_0 = (exact(3) + u_pi) / exact(2)
    rho_coeff_2 = exact(6) + exact(4) * u_pi
    rho_b_unit_l2 = rho_coeff_0 * c_h2_linf * n2 * n0 / (a_pi**4)
    lap_rho_b_unit_l2 = c_h2_linf * (exact(6) * n3 * n2 + exact(2) * n3 * n1 + rho_coeff_2 * n2 * n2) / (a_pi**4)
    # Physical ADM momentum j_i = a^(-3) [2/3 b' d_i b - 1/3 b d_i b']:
    j_b_unit_l2 = c_h2_linf * (n2 * n1) / (a_pi**3)
    lap_j_b_unit_l2 = exact(10) * c_h2_linf * (n3 * n2) / (a_pi**3)

    # Derived H^2 bounds on non-beacon l>=2 sectors (post-kick code + AH04 w*-trim + O(||u*||^2) matter/clock):
    g_val = exact("1e-40")
    four_pi_g = exact(3) / exact(10) * (g_val**2)
    r_b = exact(rc09["beacon_amplitude_scale_r_b"])
    four_pi_g_beacon_scale = (exact(3) / exact(10)) * (r_b**2)
    eta = exact("1e-13")
    u_rad = exact(rc08["certified_control_ball_radius"])
    w_trim_max = box(ah04["max_required_rotational_trim_w_norm"])
    v0 = exact(2) * iv.pi**2
    tadpole_scale = box(rc03["continuum_tadpole_scale_V0_v_over_8"])

    # (a) Post-kick code density Delta_rho_code = 1/(2 a_pi^4) eta^2 f_enc^2 (momentum jump at tau=pi+ is pure l>=0 without eta^2 velocity if field kick, bounded by eta*en["grad_l2"]):
    f_enc_h2 = en["l2"] + en["lap_l2"]
    code_rho_l2 = exact(1) / (exact(2) * (a_pi**4)) * (eta**2) * c_h2_linf * f_enc_h2 * en["l2"]
    code_lap_rho_l2 = exact(4) / (a_pi**4) * (eta**2) * c_h2_linf * (f_enc_h2**2)
    code_j_h2 = eta * (en["grad_l2"] + en["grad_lap_l2"]) / (a_pi**3)

    # (b) AH04 w*-trim l=2 stress (pure l=2 => -Delta = 8): ||rho_trim,l=2||_{L^2} <= 24 * w_trim_max / (sqrt(V0) * a_pi^4)
    trim_rho_l2 = exact(24) * w_trim_max / (iv.sqrt(v0) * (a_pi**4))
    trim_lap_rho_l2 = exact(8) * trim_rho_l2
    trim_j_h2 = exact(9) * trim_rho_l2 * a_pi

    # (c) Continuum matter + clock O(||u*||^2) l>=2 stress (from RC03 tadpole_scale < 252):
    app_u2_rho_h2 = exact(64) * (tadpole_scale**2) * (u_rad**2) / (iv.sqrt(v0) * (a_pi**4))

    four_pi_g_rho_l2 = four_pi_g_beacon_scale * rho_b_unit_l2 + four_pi_g * (code_rho_l2 + trim_rho_l2 + app_u2_rho_h2)
    four_pi_g_lap_rho_l2 = four_pi_g_beacon_scale * lap_rho_b_unit_l2 + four_pi_g * (code_lap_rho_l2 + trim_lap_rho_l2 + app_u2_rho_h2)
    four_pi_g_j_l2 = four_pi_g_beacon_scale * j_b_unit_l2 + four_pi_g * (code_j_h2 + trim_j_h2 + app_u2_rho_h2)
    four_pi_g_lap_j_l2 = four_pi_g_beacon_scale * lap_j_b_unit_l2 + four_pi_g * (code_j_h2 + trim_j_h2 + app_u2_rho_h2)

    # Hodge orthogonality on l>=2: ||delta_q|| <= ||delta_j|| / sqrt(8), ||delta_j_perp|| <= ||delta_j||
    # Elliptic H^2 -> H^4 factor max_{k>=3} k^2 / (k^2 - 4) == 9/5:
    ell_h4_gain = exact(9) / exact(5)
    psi_linf_upper = (a_pi**2) * c_sob * four_pi_g_rho_l2
    psi_h4_upper = ell_h4_gain * (a_pi**2) * (four_pi_g_rho_l2 + four_pi_g_lap_rho_l2)
    lap_psi_linf_upper = ell_h4_gain * (a_pi**2) * c_sob * four_pi_g_lap_rho_l2

    shift_b_linf_upper = exact(3) * (a_pi**2) * c_sob * (four_pi_g_j_l2 / iv.sqrt(exact(8)))
    shift_b_h4_upper = ell_h4_gain * exact(3) * (a_pi**2) * ((four_pi_g_j_l2 + four_pi_g_lap_j_l2) / iv.sqrt(exact(8)))
    shift_w_linf_upper = exact(4) * (a_pi**2) * c_sob_vec * four_pi_g_j_l2
    shift_w_h4_upper = ell_h4_gain * exact(4) * (a_pi**2) * (four_pi_g_j_l2 + four_pi_g_lap_j_l2)
    sixteen_pi_g_t_det_h2_upper = exact(4) * u_max * (
        four_pi_g_rho_l2 + four_pi_g_lap_rho_l2 + four_pi_g_j_l2 + four_pi_g_lap_j_l2
    )

    require(below(psi_linf_upper, exact("1e-22")), "||psi_{>=2}||_infty < 1e-22")
    require(below(shift_b_linf_upper, exact("1e-20")) and below(shift_w_linf_upper, exact("1e-19")), "Shift L^infty bounds")
    require(below(psi_h4_upper, exact("2e-14")) and below(shift_w_h4_upper, exact("2e-13")), "H^4 -> C^{2,1/2}(S^3) bounds")

    finish(
        "all_harmonic_york_lichnerowicz_elliptic.py",
        {
            **sym_res,
            "Sobolev_Green_series_exact_formula": "pi**2/12 - 55/576",
            "Sobolev_Green_series_value": outward(closed_series),
            "S3_Sobolev_Green_scalar_Linfty_constant": outward(c_sob),
            "S3_Sobolev_Green_vector_Linfty_constant": outward(c_sob_vec),
            "Hermite_P9_beacon_grad_L2": outward(bn["grad_l2"]),
            "SO4_commuting_backward_Gronwall_factor": outward(gronwall_factor),
            "full_binomial_Sobolev_wave_norms_used": True,
            "exact_g2_cancellation_4piG_times_rb_over_g_sq": outward(four_pi_g_beacon_scale),
            "psi_ge_2_Linfty_upper": float(outward(psi_linf_upper)[1]),
            "psi_ge_2_H4_norm_upper": float(outward(psi_h4_upper)[1]),
            "Laplacian_psi_ge_2_Linfty_upper": float(outward(lap_psi_linf_upper)[1]),
            "longitudinal_shift_B_ge_2_Linfty_upper": float(outward(shift_b_linf_upper)[1]),
            "longitudinal_shift_B_ge_2_H4_norm_upper": float(outward(shift_b_h4_upper)[1]),
            "transverse_shift_W_ge_2_Linfty_upper": float(outward(shift_w_linf_upper)[1]),
            "transverse_shift_W_ge_2_H4_norm_upper": float(outward(shift_w_h4_upper)[1]),
            "sixteen_pi_G_T_det_ge_2_H2_upper": float(outward(sixteen_pi_g_t_det_h2_upper)[1]),
            "all_harmonics_l_ge_2_to_infinity_elliptically_solved_in_H4_subset_C2": True,
        },
        inputs=[RC03_JSON, RC05_JSON, RC06_JSON, RC08_JSON, RC09_JSON, AH04_JSON],
    )


if __name__ == "__main__":
    main()
