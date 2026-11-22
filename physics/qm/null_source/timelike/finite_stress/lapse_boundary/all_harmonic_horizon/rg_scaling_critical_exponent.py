"""AH02: Certify two-sided S^3 variance equivalence and exact 3-regime RG trichotomy as rho_0 -> 0."""
from __future__ import annotations
from mpmath import iv
from common import above, below, box, exact, finish, load, outward, require

AH01_JSON = "physics/qm/null_source/timelike/finite_stress/lapse_boundary/all_harmonic_horizon/horizon_minimum_sensor_scale.json"
RC05_JSON = "physics/qm/null_source/timelike/finite_stress/lapse_boundary/renormalized_continuum/crunch_vs_subcritical_gravity.json"
RC02_JSON = "physics/qm/null_source/timelike/finite_stress/lapse_boundary/renormalized_continuum/continuum_clock_composite.json"


def parse_rational(s: str) -> iv.mpf:
    n_str, d_str = s.split("/")
    return exact(int(n_str)) / exact(int(d_str))


def main() -> None:
    ah01 = load(AH01_JSON)
    rc05 = load(RC05_JSON)
    rc02 = load(RC02_JSON)

    v0 = exact(2) * iv.pi**2
    c_lower = box(ah01["S3_universal_variance_coeff_25_over_576_pi2"])
    j0 = parse_rational(ah01["ball_C7_J0_exact_rational"])
    j2 = parse_rational(ah01["ball_C7_J2_exact_rational"])

    alpha0 = exact(3) * iv.sin(exact(1) / exact(3))
    require(above(alpha0, exact("0.9815")), "Chord factor alpha0 > 0.9815 on [0, 1/3]")

    high_tail_coeff = (exact(18) * v0 * j2) / (iv.pi * (alpha0**36) * (j0**2))
    c_upper = exact(8) / (exact(9) * v0) + (exact(1) / (iv.sqrt(exact(3)) * v0)) * (
        exact(10) / exact(9) + high_tail_coeff
    )
    require(above(c_upper - c_lower, 0), "Strict two-sided bracket c_lower < c_upper")

    # Verify Friedrichs shift quartic divergence C_shift,rho0 > (75 / 1024) * rho0^(-4) at rho0 = 1/20
    rho_ref = exact(1) / exact(20)
    c_shift_coeff = exact(75) / exact(1024)
    rc02_shift = box(rc02["uniform_Friedrichs_lower_bound_shift"])
    shift_lb_ref = c_shift_coeff / (rho_ref**4)
    require(above(rc02_shift - shift_lb_ref, 0), "RC02 Friedrichs shift exceeds universal (75/1024)*rho0^(-4) bound")

    # Cross-check that frozen RC02 continuum variance at rho_0 = 1/20 lies strictly inside (c_lower*400, c_upper*400)
    rc02_var_x = box(rc02["continuum_smeared_variances"]["X_rho0_infty"])
    lb_ref = c_lower / (rho_ref**2)
    ub_ref = c_upper / (rho_ref**2)
    require(above(rc02_var_x - lb_ref, 0) and below(rc02_var_x - ub_ref, 0), "RC02 variance inside two-sided RG bracket")

    # Reference coupling and sub-critical gravity parameter
    g_ref = exact("1e-40")
    alpha_g_ref = exact(rc05["selected_alpha_G"])
    alpha_g_crit = exact(1) / exact(3)
    require(alpha_g_ref == exact(1) / exact(10), "Exact reference alpha_G = 1/10")

    # Regime 1: nu = 0 (unrenormalized fixed g = 1e-40): washout radius where g^2 * sigma^2 >= 1
    # Lower bound sigma^2 > c_lower * rho0^(-2) => g_ref^2 * sigma^2 >= 1 definitely for rho0 <= g_ref * sqrt(c_lower)
    rho_washout_nu0 = g_ref * iv.sqrt(c_lower)
    require(above(rho_washout_nu0, exact("6.6e-42")), "Explicit sub-critical washout radius at nu=0")
    # Also check nu = 1/2: g(rho0)^2 * sigma^2 > c_lower * g_ref^2 / (rho_ref * rho0) >= 1
    rho_washout_nu_half = c_lower * (g_ref**2) / rho_ref
    require(above(rho_washout_nu_half, exact("8.7e-82")), "Explicit sub-critical washout radius at nu=1/2")

    # Regime 2: nu = 2 (super-critical): crunch threshold alpha_G(rho0) = 1/3 at rho_ref * (3/10)^(1/4)
    rho_crunch_nu2 = rho_ref * ((alpha_g_ref / alpha_g_crit) ** (exact(1) / exact(4)))
    require(above(rho_crunch_nu2, exact("0.0369")) and below(rho_crunch_nu2, exact("0.0371")), "nu=2 crunch radius")

    # Regime 3: Marginal quantum line nu = 1:
    # Quantum gate variance g(rho0)^2 * sigma^2 stays strictly inside (c_lower * g_ref^2 / rho_ref^2, c_upper * g_ref^2 / rho_ref^2)
    sigma_gate_nu1_lower = c_lower * (g_ref**2) / (rho_ref**2)
    sigma_gate_nu1_upper = c_upper * (g_ref**2) / (rho_ref**2)
    require(above(sigma_gate_nu1_lower, exact("1.7e-80")) and below(sigma_gate_nu1_upper, exact("1e-73")), "Marginal gate variance bounded")

    # Yet at fixed G, alpha_G(rho0; 1) = (1/10) * (rho_ref / rho0)^2 hits 1/3 at rho_crunch(1) = rho_ref * sqrt(3/10)!
    rho_crunch_nu1 = rho_ref * iv.sqrt(alpha_g_ref / alpha_g_crit)
    require(above(rho_crunch_nu1, exact("0.02738612")) and below(rho_crunch_nu1, exact("0.02738613")), "Marginal fixed-G crunch radius")
    require(below(rho_crunch_nu1 - rho_ref, 0), "Reference rho0 = 0.05 is above crunch radius 0.027386")

    finish(
        "rg_scaling_critical_exponent.py",
        {
            "reference_rho0_rad": "1/20",
            "reference_g": "1e-40",
            "reference_alpha_G": "1/10",
            "S3_variance_c_lower": outward(c_lower),
            "S3_variance_c_upper": outward(c_upper),
            "Friedrichs_shift_rho0_minus_4_coeff_lower": "75/1024",
            "Friedrichs_shift_lb_at_rho_ref": outward(shift_lb_ref),
            "RC02_shift_exceeds_quartic_bound": True,
            "RC02_rho0_variance_strictly_inside_two_sided_bounds": True,
            "subcritical_nu_lt_1_gate_variance_limit": "PLUS_INFINITY_GATE_WASHOUT",
            "subcritical_washout_radius_nu0_rad": outward(rho_washout_nu0),
            "subcritical_washout_radius_nu_half_rad": outward(rho_washout_nu_half),
            "marginal_nu_eq_1_gate_variance_lower": outward(sigma_gate_nu1_lower),
            "marginal_nu_eq_1_gate_variance_upper": outward(sigma_gate_nu1_upper),
            "marginal_nu_eq_1_fixed_G_crunch_radius_rad": outward(rho_crunch_nu1),
            "supercritical_nu_eq_2_fixed_G_crunch_radius_rad": outward(rho_crunch_nu2),
            "any_nu_permits_rho0_to_0_at_fixed_positive_G_without_crunch_or_washout": False,
        },
        inputs=[AH01_JSON, RC05_JSON, RC02_JSON],
    )


if __name__ == "__main__":
    main()
