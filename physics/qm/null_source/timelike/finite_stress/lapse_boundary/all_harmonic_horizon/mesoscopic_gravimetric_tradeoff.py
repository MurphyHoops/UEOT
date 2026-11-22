"""AH08: Certify universal E/E_P gravimetric phase scaling and mesoscopic flat-space 62/242-trial window vs RC12 >1e35."""
from __future__ import annotations
import math
import sympy as sp
from mpmath import iv
from common import above, below, box, exact, finish, interval, load, outward, require

AH07_JSON = "physics/qm/null_source/timelike/finite_stress/lapse_boundary/all_harmonic_horizon/asymptotically_flat_localized_clock.json"
RC12_JSON = "physics/qm/null_source/timelike/finite_stress/lapse_boundary/renormalized_continuum/calibration_and_open_gates.json"


def main() -> None:
    load(AH07_JSON)
    rc12 = load(RC12_JSON)

    h_si = exact(662607015) / (exact(10) ** 42)
    hbar = h_si / (exact(2) * iv.pi)
    c_si = exact("299792458")
    g_si = interval("6.67415e-11", "6.67445e-11")
    e_planck = iv.sqrt(hbar * (c_si**5) / g_si)
    m_planck = e_planck / (c_si**2)
    require(above(e_planck, exact("1.956e9")) and below(e_planck, exact("1.957e9")), "Planck energy ~ 1.956e9 J")

    # Single-quantum fundamental mode on R_S3 ~ 1046.1 km: E_1 = hbar * c / R_S3
    r_s3 = box(rc12["physical_turnaround_radius_R_S3_m"])
    e_single_q = hbar * c_si / r_s3
    single_q_phase_1s = ((e_single_q / e_planck) ** 2) * (c_si * exact(1) / r_s3)
    require(below(single_q_phase_1s, exact("1e-76")), "Single-quantum unamplified phase < 1e-76 rad")

    # Mesoscopic flat-space (Lambda = 0) BEC/nanocrystal center-of-mass window:
    m_meso = exact(1) / (exact(10) ** 14)   # 1e-14 kg
    r_app = exact(5) / (exact(10) ** 5)     # 5e-5 m
    d_sep = exact(2) / (exact(10) ** 4)     # 2e-4 m
    t_int = exact(1)
    require(above(d_sep - exact(2) * r_app, 0), "Non-overlapping localized packets d_sep = 4 R_app > 2 R_app")

    c_crit = exact(2048) / exact(9375)
    c0_meso = exact(2) * g_si * m_meso / ((c_si**2) * r_app)
    require(below(c0_meso, exact("3e-37")) and below(c0_meso - c_crit, 0), "Deep sub-critical Lichnerowicz regime")

    # Verify exact algebraic identity G m^2 T / (hbar d) == (E/E_P)^2 * (c T / d) symbolically and on interval endpoints:
    g_s, m_s, t_s, hb_s, d_s, c_s = sp.symbols("G m T hbar d c", positive=True)
    ep_s = sp.sqrt(hb_s * c_s**5 / g_s)
    require(
        sp.simplify(g_s * m_s**2 * t_s / (hb_s * d_s) - ((m_s * c_s**2 / ep_s) ** 2) * (c_s * t_s / d_s)) == 0,
        "Symbolic Planck-ratio gravimetric phase identity",
    )
    dphi_direct = g_si * (m_meso**2) * t_int / (hbar * d_sep)
    e_meso = m_meso * (c_si**2)
    dphi_planck_form = ((e_meso / e_planck) ** 2) * (c_si * t_int / d_sep)
    require(below(abs(iv.mpf(dphi_direct.a) - iv.mpf(dphi_planck_form.a)), exact("1e-90")), "Lower endpoint match")
    require(below(abs(iv.mpf(dphi_direct.b) - iv.mpf(dphi_planck_form.b)), exact("1e-90")), "Upper endpoint match")
    require(above(dphi_direct, exact("0.316")) and below(dphi_direct, exact("0.317")), "Phase in (0.316, 0.317) rad")

    contrast_diff = iv.sin(dphi_direct)
    contrast_on_off = iv.sin(dphi_direct / exact(2))
    n_trials_diff = exact(2) * iv.log(exact(20)) / (contrast_diff**2)
    n_trials_on_off = exact(2) * iv.log(exact(20)) / (contrast_on_off**2)
    n_int_diff = math.ceil(float(outward(n_trials_diff)[1]))
    n_int_on_off = math.ceil(float(outward(n_trials_on_off)[1]))

    rc12_trials_lb = box(rc12["minimum_independent_trials_for_95pct_ID_lower"])
    improvement_diff = rc12_trials_lb / n_trials_diff
    improvement_on_off = rc12_trials_lb / n_trials_on_off

    require(n_int_diff == 62 and n_int_on_off == 242, "Exact Hoeffding integer trial counts 62 (diff) and 242 (on/off)")
    require(above(improvement_diff, exact("1e33")) and above(improvement_on_off, exact("4e32")), "> 10^32-10^33 trial reduction")

    finish(
        "mesoscopic_gravimetric_tradeoff.py",
        {
            "Planck_energy_J": outward(e_planck),
            "Planck_mass_kg": outward(m_planck),
            "single_quantum_R_S3_phase_1s_rad_upper": float(outward(single_q_phase_1s)[1]),
            "mesoscopic_packet_mass_kg": "1e-14",
            "mesoscopic_packet_radius_m": "5e-5",
            "mesoscopic_center_separation_m": "2e-4",
            "mesoscopic_Lichnerowicz_compactness_C0": outward(c0_meso),
            "mesoscopic_gravimetric_phase_1s_rad": outward(dphi_direct),
            "mesoscopic_differential_contrast": outward(contrast_diff),
            "mesoscopic_on_off_midpoint_contrast": outward(contrast_on_off),
            "mesoscopic_95pct_trials_differential_continuous": outward(n_trials_diff),
            "mesoscopic_95pct_integer_trials": n_int_diff,
            "mesoscopic_95pct_integer_trials_on_off": n_int_on_off,
            "trial_reduction_factor_vs_RC12_lower": float(outward(improvement_diff)[0]),
            "tabletop_experimental_execution_claimed": False,
        },
        inputs=[AH07_JSON, RC12_JSON],
    )


if __name__ == "__main__":
    main()
