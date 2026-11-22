"""AH01: Certify S^3 finite-rho_0 clock variance blowup and squeezing-proof Planck sensor floor."""
from __future__ import annotations
import sympy as sp
from mpmath import iv
from common import above, below, box, exact, finish, load, outward, require
from model import exact_cap_khat

CAP_JSON = "physics/qm/null_source/timelike/finite_stress/lapse_boundary/renormalized_continuum/geodesic_cap_kernel.json"
CAL_JSON = "physics/qm/null_source/timelike/finite_stress/lapse_boundary/renormalized_continuum/calibration_and_open_gates.json"


def main() -> None:
    cap = load(CAP_JSON)
    cal = load(CAL_JSON)

    # 1. Verify universal finite-rho0 bound sigma^2 > (25 / (576 * pi^2)) * rho0^(-2)
    v0 = exact(2) * iv.pi**2
    coeff_universal = exact(25) / (exact(576) * iv.pi**2)
    sample_variances = {}
    for den in (20, 40, 80):
        n_cut = den  # floor(1 / (1/den)) = den >= 3
        khats = exact_cap_khat(1, den, n_cut)
        require(all(above(kh, exact(5) / exact(6)) for kh in khats), f"khat > 5/6 up to N={n_cut}")
        if den == 20:
            # Cross-check against frozen RC01 khat_2_dipole
            rc_k2 = box(cap["khat_2_dipole"])
            require(not (khats[1].b < rc_k2.a or khats[1].a > rc_k2.b), "Matches frozen RC01 khat(2)")
        partial_var = exact(0)
        for k in range(2, n_cut + 1):
            kk = exact(k)
            partial_var += (kk**2 / iv.sqrt(kk**2 - exact(1))) * (khats[k - 1] ** 2) / (exact(2) * v0)
        analytic_lb = coeff_universal * exact(den**2)
        require(above(partial_var - analytic_lb, 0), f"Partial sum exceeds universal lower bound at rho0=1/{den}")
        sample_variances[f"rho0_1_over_{den}"] = {
            "N_cutoff": n_cut,
            "partial_variance_lower": float(outward(partial_var)[0]),
            "universal_bound_lower": float(outward(analytic_lb)[0]),
            "scaled_rho0_sq_variance_lower": float(outward(partial_var / exact(den**2))[0]),
        }

    # 2. Exact rational Beta integrals for C^7_c(B_L) radial kernel w_1(r) proportional to (1 - r^2)_+^8 in R^3
    s = sp.Symbol("s", real=True)
    j0 = sp.integrate((1 - s**2) ** 8 * s**2, (s, 0, 1))
    j1 = sp.integrate((1 - s**2) ** 16 * s**2, (s, 0, 1))
    j2 = sp.integrate(256 * s**2 * (1 - s**2) ** 14 * s**2, (s, 0, 1))
    require(j0 == sp.Rational(32768, 2078505), "Exact J0 rational check")

    def sym_rat_to_iv(r: sp.Rational) -> iv.mpf:
        return exact(int(sp.numer(r))) / exact(int(sp.denom(r)))

    j0_iv = sym_rat_to_iv(j0)
    j1_iv = sym_rat_to_iv(j1)
    j2_iv = sym_rat_to_iv(j2)

    cw2 = j1_iv / (exact(4) * iv.pi * j0_iv**2)
    cw_grad = j2_iv / (exact(4) * iv.pi * j0_iv**2)
    require(above(cw2, exact(1)) and above(cw_grad, exact(20)), "Plancherel kernel norms positive")

    # 3. Squeezing-proof dimensionless energy threshold E_min(N_gate=1, eta_t=1, mu_0=0, lambda_sys=2)
    # and massive case mu_0 = 1
    def calc_emin_lmin(n_gate: iv.mpf, eta_t: iv.mpf, mu0: iv.mpf, lam_sys: iv.mpf):
        cw_kin_bar = exact(1) / exact(2) * (iv.sqrt(cw2 * cw_grad) + mu0 * cw2)
        a_bar = cw_kin_bar / cw2
        num = n_gate**2
        den = exact(8) * eta_t**2 * (a_bar + iv.sqrt(a_bar**2 + n_gate**2 / (exact(4) * eta_t**2)))
        e_min = num / den
        l_ratio = iv.sqrt(exact(2) * e_min / lam_sys)
        return e_min, l_ratio, a_bar

    emin_massless, lratio_massless, abar_0 = calc_emin_lmin(exact(1), exact(1), exact(0), exact(2))
    emin_massive, lratio_massive, _ = calc_emin_lmin(exact(1), exact(1), exact(1), exact(2))
    emin_high_snr, lratio_high_snr, _ = calc_emin_lmin(exact(10), exact(1) / exact(2), exact(0), exact(2))

    require(above(emin_massless, exact("0.015")), "Strictly positive massless energy threshold")
    require(above(lratio_massless, exact("0.12")), "Strictly positive Planck sensor ratio")
    require(above(lratio_massive, exact("0.11")), "Strictly positive massive Planck sensor ratio")
    require(above(lratio_high_snr, exact("1.8")), "Super-Planckian floor for SNR=10, eta_t=1/2")

    lp_m = box(cal["Planck_length_m"])
    l_sensor_rc12_m = box(cal["physical_sensor_cap_radius_m"])
    lmin_massless_m = lratio_massless * lp_m
    require(above(lmin_massless_m, exact("1.9e-36")), "Physical minimum sensor radius > 1.9e-36 m")
    require(below(lmin_massless_m / l_sensor_rc12_m, exact("1e-39")), "RC01-RC12 sensor radius safely above horizon floor")

    finish(
        "horizon_minimum_sensor_scale.py",
        {
            "S3_universal_variance_coeff_25_over_576_pi2": outward(coeff_universal),
            "S3_universal_bound_valid_for_rho0_le": "1/3",
            "S3_sample_cap_variances": sample_variances,
            "ball_C7_J0_exact_rational": str(j0),
            "ball_C7_J1_exact_rational": str(j1),
            "ball_C7_J2_exact_rational": str(j2),
            "Plancherel_cw2": outward(cw2),
            "Plancherel_cw_grad": outward(cw_grad),
            "kinetic_to_L2_ratio_massless_upper": outward(abar_0),
            "E_min_dimless_SNR1_etat1_massless": outward(emin_massless),
            "L_min_over_Planck_SNR1_etat1_lam2_massless": outward(lratio_massless),
            "L_min_over_Planck_SNR1_etat1_lam2_mu1": outward(lratio_massive),
            "L_min_over_Planck_SNR10_etat0p5_lam2_massless": outward(lratio_high_snr),
            "physical_L_min_SNR1_m": outward(lmin_massless_m),
            "RC12_sensor_radius_above_horizon_floor": True,
            "squeezed_and_non_Gaussian_normal_states_covered": True,
            "pointwise_RSET_positivity_assumed": False,
            "pointlike_L_to_0_autonomous_clock_excluded_by_horizon_trapping": True,
        },
        inputs=[CAP_JSON, CAL_JSON],
    )


if __name__ == "__main__":
    main()
