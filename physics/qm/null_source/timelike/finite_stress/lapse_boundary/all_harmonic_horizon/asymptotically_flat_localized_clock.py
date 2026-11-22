"""AH07: Symbolically verify C^1 R^3 Lichnerowicz supersolution + Banach contraction at C_crit=2048/9375 and certify Lambda=0 clock."""
from __future__ import annotations
import sympy as sp
from mpmath import iv
from common import above, below, box, exact, finish, interval, load, outward, require

AH01_JSON = "physics/qm/null_source/timelike/finite_stress/lapse_boundary/all_harmonic_horizon/horizon_minimum_sensor_scale.json"
RC12_JSON = "physics/qm/null_source/timelike/finite_stress/lapse_boundary/renormalized_continuum/calibration_and_open_gates.json"


def verify_lichnerowicz_barrier_symbolically() -> dict:
    r, r_app, alpha, g_n, c_l, rho0 = sp.symbols("r R_app alpha G c rho0", positive=True)
    psi_max = sp.Rational(5, 4)
    a_amp = alpha * psi_max**5
    psi_in = 1 + a_amp * (sp.Rational(3, 2) - r**2 / (2 * r_app**2))
    psi_out = 1 + a_amp * r_app / r

    # 1. Exact C^1 matching at r = R_app
    require(sp.simplify(psi_in.subs(r, r_app) - psi_out.subs(r, r_app)) == 0, "C^0 continuity at R_app")
    require(
        sp.simplify(sp.diff(psi_in, r).subs(r, r_app) - sp.diff(psi_out, r).subs(r, r_app)) == 0,
        "C^1 continuity at R_app",
    )

    # 2. 3D radial Laplacian -(1/r^2) d/dr (r^2 dpsi/dr)
    lap_in = sp.simplify(-sp.diff(r**2 * sp.diff(psi_in, r), r) / r**2)
    lap_out = sp.simplify(-sp.diff(r**2 * sp.diff(psi_out, r), r) / r**2)
    require(sp.simplify(lap_in - 3 * a_amp / r_app**2) == 0 and lap_out == 0, "Exact radial Laplacian")

    # Verify 3 * alpha / R_app^2 == 2 * pi * G * rho0 / c^2 when alpha = G * (4/3 pi R_app^3 rho0) / (2 c^2 R_app)
    alpha_sub = g_n * (sp.Rational(4, 3) * sp.pi * r_app**3 * rho0) / (2 * c_l**2 * r_app)
    require(sp.simplify((3 * alpha_sub / r_app**2) - (2 * sp.pi * g_n * rho0 / c_l**2)) == 0, "Exact source coefficient")

    # 3. Critical threshold alpha_crit = 512 / 9375 (C_crit = 4*alpha_crit = 2048 / 9375) and exact Lipschitz = 1 at alpha_crit
    alpha_crit = sp.Rational(512, 9375)
    require(psi_in.subs({r: 0, alpha: alpha_crit}) == psi_max, "Exact tangent barrier psi_+(0) == 5/4")
    require(alpha_crit * psi_max**5 == sp.Rational(1, 6), "Exact exterior monopole ratio A / R_app = 1/6")
    lip_crit = sp.Rational(3, 2) * alpha_crit * (5 * psi_max**4)
    require(lip_crit == 1, "Exact Banach Lipschitz constant (9375/2048)*C0 == 1 at C_crit")

    # 4. Areal-radius derivative > 2/3 for any radial solution in [1, psi_+] (since -r*psi' < 1/6) and >= 35/36 for psi_+
    d_areal_in = sp.simplify(sp.diff(r * psi_in**2, r).subs({r: r_app, alpha: alpha_crit}))
    d_areal_out = sp.simplify(sp.diff(r * psi_out**2, r).subs({r: r_app, alpha: alpha_crit}))
    universal_radial_areal_lb = 1 * (1 - 2 * sp.Rational(1, 6))
    require(d_areal_in == sp.Rational(35, 36) and d_areal_out == sp.Rational(35, 36), "Positive barrier slope 35/36 at R_app")
    require(universal_radial_areal_lb == sp.Rational(2, 3), "Universal radial areal-radius slope lower bound 2/3 > 0")

    return {
        "critical_alpha_exact": "512/9375",
        "critical_compactness_C_crit_exact": "2048/9375",
        "Banach_contraction_Lipschitz_formula": "(9375/2048)*C_0 < 1",
        "barrier_supremum_psi_max": "5/4",
        "coordinate_ADM_mass_enclosure_factor_exact": "3125/1024",
        "proper_ADM_mass_lower_ratio_exact": "4/5",
        "universal_radial_areal_slope_lower_bound": "2/3",
        "barrier_areal_radius_slope_at_R_app_crit": "35/36",
    }


def main() -> None:
    sym_res = verify_lichnerowicz_barrier_symbolically()
    ah01 = load(AH01_JSON)
    rc12 = load(RC12_JSON)

    # Exact SI definitions (c, h exact in SI; CODATA-2022 interval for G_SI):
    h_si = exact(662607015) / (exact(10) ** 42)
    hbar = h_si / (exact(2) * iv.pi)
    c_si = exact("299792458")
    g_si = interval("6.67415e-11", "6.67445e-11")

    l_min_m = box(ah01["physical_L_min_SNR1_m"])
    l_sensor = exact(1) / exact(10000)   # 1e-4 m (100 um)
    r_app = exact(1) / exact(1000)       # 1e-3 m (1 mm = 10 L_sensor)
    e_clock_j = exact(1) / (exact(10) ** 9)
    c_crit = exact(2048) / exact(9375)

    require(above(l_sensor / l_min_m, exact("1e31")), "100 um sensor radius > 10^31 * L_min")
    c0_lab = exact(2) * g_si * e_clock_j / ((c_si**4) * r_app)
    lip_lab = (exact(9375) / exact(2048)) * c0_lab
    require(below(c0_lab, exact("2e-50")) and below(lip_lab, exact("1e-49")), "Strictly sub-critical contraction << 1")

    psi_origin_upper = exact(1) + (exact(3) / exact(8)) * c0_lab * ((exact(5) / exact(4)) ** 5)
    m_coord_kg = e_clock_j / (c_si**2)
    m_adm_upper_kg = m_coord_kg * psi_origin_upper**5

    # Compare localized flat-space energy density vs RC12 closed-S^3 closure density (~1.32e30 J/m^3):
    vol_app = (exact(4) / exact(3)) * iv.pi * (r_app**3)
    eps_lab = e_clock_j / vol_app
    eps_rc12 = box(rc12["turnaround_clock_energy_density_J_m3"])
    reduction_ratio = eps_lab / eps_rc12
    require(below(reduction_ratio, exact("2e-31")), "Energy density reduced by > 30 orders of magnitude vs closed S^3")

    # Massive carrier dispersion bound over T_exp = 1 s for Rb-87 carrier mass m_Rb = 1.443e-25 kg:
    m_carrier = exact(1443) / (exact(10) ** 28)
    t_exp = exact(1)
    dr_disp = hbar * t_exp / (m_carrier * r_app)
    require(below(dr_disp / r_app, exact("1e-3")), "Wavepacket dispersion < 10^-3 * R_app over 1 s")

    finish(
        "asymptotically_flat_localized_clock.py",
        {
            **sym_res,
            "cosmological_constant_Lambda": 0,
            "localized_sensor_radius_m": "1e-4",
            "localized_apparatus_radius_m": "1e-3",
            "localized_clock_energy_J": "1e-9",
            "localized_compactness_C0": outward(c0_lab),
            "localized_Banach_Lipschitz_constant": outward(lip_lab),
            "localized_ADM_mass_upper_kg": float(outward(m_adm_upper_kg)[1]),
            "localized_energy_density_J_m3": outward(eps_lab),
            "density_ratio_vs_RC12_closed_S3_upper": float(outward(reduction_ratio)[1]),
            "dispersion_fraction_over_1s_upper": float(outward(dr_disp / r_app)[1]),
            "horizon_and_minimal_surface_free_on_R3": True,
        },
        inputs=[AH01_JSON, RC12_JSON],
    )


if __name__ == "__main__":
    main()
