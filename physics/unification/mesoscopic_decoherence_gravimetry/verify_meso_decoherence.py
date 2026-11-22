"""P-MESO-BMV-06 Certificate: Open-System Lindblad Decoherence Budget, LOCC Non-Classicality Witness
& Pre-Registered Blind-Holdout Pipeline for the Flat-Space Mesoscopic Gravimetric Protocol.

Verifies in 40-digit outward interval arithmetic (mpmath.iv / physics.unification.common):
1. Exact 4x4 complex interval verification of the Bose-Marletto-Vedral (BMV) stabilizer witness
   W_BMV = I x I - X x X + Y x Z + Z x Y: Hermiticity, commuting stabilizer algebra, two-value
   spectrum {-2, +2}, non-negativity >= 0 across separable / Kafri-Taylor-Milburn LOCC channels,
   and exact trace match against both spatial-path Lindblad pure dephasing and local depolarizing
   open-system channels at AH08 parameters (m = 10^-14 kg, R_app = 50 um, d = 200 um, T = 1 s).
2. Maximum tolerable per-packet decoherence rate Gamma_max > 0.1258 s^-1 (depolarizing) and
   > 0.1443 s^-1 (pure spatial dephasing) vs physical cryogenic UHV environmental rate
   Gamma_env < 0.02 s^-1 at T_env = 0.5 K, P_gas = 10^-15 Pa He-4 + blackbody scattering/emission.
3. Noisy SPAM-and-leakage-calibrated 95%-confidence Hoeffding trial bounds at Gamma_env = 0.02 s^-1
   (69 differential phase runs; 435 < 450 total commuting-stabilizer witness shots; 365 < 450 shots
   per local Pauli setting) plus pre-registered HARDWARE_CERTIFICATION_CONTRACT.md blind-holdout
   pipeline validation (device_certified = False, physical_unification = "OPEN").
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
import sys
from mpmath import iv

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
sys.path.insert(0, str(HERE.parent))
from common import outward_str, require, sha256_file, strictly_above, strictly_below, write_json


def _mat_zeros(n: int) -> list[list]:
    z = iv.mpc(0, 0)
    return [[z for _ in range(n)] for _ in range(n)]


def _mat_add(a: list[list], b: list[list], sign: int = 1) -> list[list]:
    n = len(a)
    s = iv.mpc(sign, 0)
    return [[a[i][j] + s * b[i][j] for j in range(n)] for i in range(n)]


def _mat_scale(c, a: list[list]) -> list[list]:
    n = len(a)
    cc = iv.mpc(c)
    return [[cc * a[i][j] for j in range(n)] for i in range(n)]


def _mat_mul(a: list[list], b: list[list]) -> list[list]:
    n = len(a)
    out = _mat_zeros(n)
    for i in range(n):
        for j in range(n):
            acc = iv.mpc(0, 0)
            for k in range(n):
                acc += a[i][k] * b[k][j]
            out[i][j] = acc
    return out


def _conj(z):
    return iv.mpc(z.real, -z.imag)


def _mat_dag(a: list[list]) -> list[list]:
    n = len(a)
    return [[_conj(a[j][i]) for j in range(n)] for i in range(n)]


def _mat_kron2(a: list[list], b: list[list]) -> list[list]:
    out = _mat_zeros(4)
    for i1 in range(2):
        for i2 in range(2):
            for j1 in range(2):
                for j2 in range(2):
                    out[2 * i1 + i2][2 * j1 + j2] = a[i1][j1] * b[i2][j2]
    return out


def _mat_trace(a: list[list]):
    acc = iv.mpc(0, 0)
    for i in range(len(a)):
        acc += a[i][i]
    return acc


def _mat_max_abs(a: list[list]):
    mx = iv.mpf(0)
    for row in a:
        for entry in row:
            val = abs(entry)
            if val.b > mx.b:
                mx = val
    return mx


def _enclose_zeta_int(s_pow: int, n_cut: int = 200):
    """Rigorous Euler-Maclaurin integral enclosure of zeta(s_pow) for integer s_pow >= 2."""
    partial = iv.mpf(0)
    for n in range(1, n_cut + 1):
        partial += iv.mpf(1) / (iv.mpf(n) ** s_pow)
    p_minus_1 = s_pow - 1
    tail_lo = iv.mpf(1) / (iv.mpf(p_minus_1) * (iv.mpf(n_cut + 1) ** p_minus_1))
    tail_hi = iv.mpf(1) / (iv.mpf(p_minus_1) * (iv.mpf(n_cut) ** p_minus_1))
    return partial + iv.mpf([tail_lo.a, tail_hi.b])


def _bloch_state_2x2(rx, ry, rz) -> list[list]:
    half = iv.mpc("0.5", 0)
    one = iv.mpf(1)
    return [
        [half * iv.mpc(one + rz, 0), half * iv.mpc(rx, -ry)],
        [half * iv.mpc(rx, ry), half * iv.mpc(one - rz, 0)],
    ]


def verify_bmv_4x4_and_gravimetric_thresholds() -> tuple[dict, dict]:
    zero = iv.mpc(0, 0)
    one = iv.mpc(1, 0)
    iu = iv.mpc(0, 1)

    i2 = [[one, zero], [zero, one]]
    px = [[zero, one], [one, zero]]
    py = [[zero, -iu], [iu, zero]]
    pz = [[one, zero], [zero, -one]]

    i4 = _mat_kron2(i2, i2)
    a1 = _mat_kron2(px, px)
    a2 = _mat_scale(-1, _mat_kron2(py, pz))
    a3 = _mat_scale(-1, _mat_kron2(pz, py))
    # W_BMV = I x I - X x X + Y x Z + Z x Y = I_4 - A_1 - A_2 - A_3
    w_bmv = _mat_add(_mat_add(_mat_add(i4, a1, -1), a2, -1), a3, -1)

    # Verify exact 4x4 operator identities in 40-digit complex interval arithmetic:
    require(strictly_below(_mat_max_abs(_mat_add(_mat_dag(w_bmv), w_bmv, -1)), "1e-39"), "W_BMV Hermiticity")
    for op in (a1, a2, a3):
        require(strictly_below(_mat_max_abs(_mat_add(_mat_mul(op, op), i4, -1)), "1e-39"), "Stabilizer involution")
    require(strictly_below(_mat_max_abs(_mat_add(_mat_mul(a1, a2), a3, -1)), "1e-39"), "A1 * A2 == A3")
    require(strictly_below(_mat_max_abs(_mat_add(_mat_mul(a2, a1), a3, -1)), "1e-39"), "A2 * A1 == A3")
    require(strictly_below(_mat_max_abs(_mat_add(_mat_mul(a2, a3), _mat_mul(a3, a2), -1)), "1e-39"), "[A2, A3] == 0")
    # Spectral identity (W_BMV - 2 I_4)(W_BMV + 2 I_4) == 0 (exact eigenvalues {-2, +2, +2, +2}):
    spec_res = _mat_mul(_mat_add(w_bmv, _mat_scale(2, i4), -1), _mat_add(w_bmv, _mat_scale(2, i4), 1))
    require(strictly_below(_mat_max_abs(spec_res), "1e-39"), "(W - 2I)(W + 2I) == 0")

    # Verify separable LOCC boundary & Kafri-Taylor-Milburn classical dephasing-gravity channel >= 0:
    # 1) Extremal aligned Cauchy-Schwarz product state r = (3/5, 12/25, 16/25), s = (3/5, -16/25, -12/25):
    r_ext = _bloch_state_2x2(iv.mpf("3") / 5, iv.mpf("12") / 25, iv.mpf("16") / 25)
    s_ext = _bloch_state_2x2(iv.mpf("3") / 5, -iv.mpf("16") / 25, -iv.mpf("12") / 25)
    tr_ext = _mat_trace(_mat_mul(w_bmv, _mat_kron2(r_ext, s_ext)))
    require(strictly_below(abs(tr_ext), "1e-38"), "Aligned Cauchy-Schwarz separable boundary achieves W == 0")

    # 2) Kafri-Taylor-Milburn (KTM) classical-mediator channel: classical mediator measures Z_1, Z_2
    #    (collapsing off-diagonal path coherences -> separable mixture of |00>, |01>, |10>, |11>):
    rho_ktm = _mat_scale(iv.mpf("0.25"), i4)
    tr_ktm = _mat_trace(_mat_mul(w_bmv, rho_ktm)).real
    require(strictly_above(tr_ktm, "0.999999999999999999"), "KTM classical mediator satisfies Tr(W rho_KTM) == 1 >= 0")

    # AH08 flat-space mesoscopic protocol parameters (CODATA-2022 exact h, c; measured G interval):
    h_si = iv.mpf("6.62607015e-34")
    hbar = h_si / (2 * iv.pi)
    c_si = iv.mpf("299792458")
    g_si = iv.mpf(["6.67415e-11", "6.67445e-11"])

    m_meso = iv.mpf("1e-14")   # 10 pg packet mass
    r_app = iv.mpf("5e-5")     # 50 um interferometric arm half-width (Delta x = 2 R_app = 100 um)
    d_sep = iv.mpf("2e-4")     # 200 um center-to-center separation
    t_int = iv.mpf("1")        # 1 s coherent interaction window

    dphi_grav = g_si * (m_meso ** 2) * t_int / (hbar * d_sep)
    require(
        strictly_above(dphi_grav, "0.31643") and strictly_below(dphi_grav, "0.31646"),
        "AH08 gravimetric phase must lie strictly inside (0.31643, 0.31646) rad",
    )

    cos_half_sq = iv.cos(dphi_grav / 2) ** 2
    sin_phi = iv.sin(dphi_grav)
    s_bmv = cos_half_sq + sin_phi
    require(
        strictly_above(s_bmv, "1.2863") and strictly_below(s_bmv, "1.2864"),
        "BMV coherent correlator sum cos^2(dphi/2) + sin(dphi) must lie in (1.2863, 1.2864) > 1",
    )

    # Maximum tolerable per-packet decoherence rates for strict non-LOCC violation W < 0:
    gamma_max_depol = iv.log(s_bmv) / (2 * t_int)
    nu_crit_deph = (-sin_phi + iv.sqrt((sin_phi ** 2) + 4 * cos_half_sq)) / (2 * cos_half_sq)
    gamma_max_deph = -iv.log(nu_crit_deph) / t_int
    require(strictly_above(gamma_max_depol, "0.1258"), "Gamma_max (depolarizing) must exceed 0.1258 s^-1")
    require(strictly_above(gamma_max_deph, gamma_max_depol), "Pure spatial dephasing threshold strictly exceeds depolarizing")

    # Direct 4x4 Kraus-channel matrix verification at conservative environmental cap Gamma_cap = 0.02 s^-1
    # evaluated at BOTH CODATA G-interval endpoints of dphi_grav (avoiding interval-dependency wrapping on G)
    # plus full G-interval outward enclosure on dphi_grav:
    gamma_cap = iv.mpf("0.02")
    nu_cap = iv.exp(-gamma_cap * t_int)
    w_z = [(1 + nu_cap) / 2, (1 - nu_cap) / 2]
    ops_z = [i2, pz]
    w_d = [(1 + 3 * nu_cap) / 4, (1 - nu_cap) / 4, (1 - nu_cap) / 4, (1 - nu_cap) / 4]
    ops_d = [i2, px, py, pz]

    for phi_pt in (iv.mpf(dphi_grav.a), iv.mpf(dphi_grav.b)):
        exp_iphi = iv.mpc(iv.cos(phi_pt), iv.sin(phi_pt))
        psi_vec = [iv.mpc("0.5", 0), iv.mpc("0.5", 0), iv.mpc("0.5", 0), iv.mpc("0.5", 0) * exp_iphi]
        rho_pure = [[psi_vec[i] * _conj(psi_vec[j]) for j in range(4)] for i in range(4)]

        rho_deph = _mat_zeros(4)
        for a_idx in range(2):
            for b_idx in range(2):
                kab = _mat_kron2(ops_z[a_idx], ops_z[b_idx])
                term = _mat_mul(_mat_mul(kab, rho_pure), kab)
                rho_deph = _mat_add(rho_deph, _mat_scale(w_z[a_idx] * w_z[b_idx], term), 1)

        rho_depol = _mat_zeros(4)
        for a_idx in range(4):
            for b_idx in range(4):
                kab = _mat_kron2(ops_d[a_idx], ops_d[b_idx])
                term = _mat_mul(_mat_mul(kab, rho_pure), kab)
                rho_depol = _mat_add(rho_depol, _mat_scale(w_d[a_idx] * w_d[b_idx], term), 1)

        tr_w_deph = _mat_trace(_mat_mul(w_bmv, rho_deph))
        tr_w_depol = _mat_trace(_mat_mul(w_bmv, rho_depol))
        cf_deph = 1 - (nu_cap ** 2) * (iv.cos(phi_pt / 2) ** 2) - nu_cap * iv.sin(phi_pt)
        cf_depol = 1 - (nu_cap ** 2) * ((iv.cos(phi_pt / 2) ** 2) + iv.sin(phi_pt))

        require(strictly_below(abs(tr_w_deph.imag), "1e-38"), "Im Tr(W rho_deph) == 0")
        require(strictly_below(abs(tr_w_depol.imag), "1e-38"), "Im Tr(W rho_depol) == 0")
        require(strictly_below(abs(tr_w_deph.real - cf_deph), "1e-37"), "4x4 dephased trace matches closed form")
        require(strictly_below(abs(tr_w_depol.real - cf_depol), "1e-37"), "4x4 depolarized trace matches closed form")

    closed_w_deph = 1 - (nu_cap ** 2) * cos_half_sq - nu_cap * sin_phi
    closed_w_depol = 1 - (nu_cap ** 2) * s_bmv
    require(strictly_below(closed_w_deph, closed_w_depol) and strictly_below(closed_w_depol, "-0.235"), "Both W < -0.235 < 0")

    ctx = {
        "h_si": h_si,
        "hbar": hbar,
        "c_si": c_si,
        "g_si": g_si,
        "m_meso": m_meso,
        "r_app": r_app,
        "d_sep": d_sep,
        "t_int": t_int,
        "dphi_grav": dphi_grav,
        "gamma_max_depol": gamma_max_depol,
        "gamma_max_deph": gamma_max_deph,
        "nu_cap": nu_cap,
        "w_depol_cap": closed_w_depol,
        "w_deph_cap": closed_w_deph,
    }
    summary = {
        "gravimetric_phase_rad": outward_str(dphi_grav),
        "coherent_correlator_sum_cos2_plus_sin": outward_str(s_bmv),
        "max_tolerable_decoherence_rate_depolarizing_s_inv": outward_str(gamma_max_depol),
        "max_tolerable_decoherence_rate_spatial_dephasing_s_inv": outward_str(gamma_max_deph),
        "ktm_classical_locc_witness_value": "1",
        "witness_at_gamma_0p02_depolarizing": outward_str(closed_w_depol),
        "witness_at_gamma_0p02_spatial_dephasing": outward_str(closed_w_deph),
        "matrix_4x4_closed_form_max_abs_residual_upper": "1e-37",
    }
    return summary, ctx


def verify_cryo_uhv_decoherence_budget(ctx: dict) -> dict:
    h_si = ctx["h_si"]
    hbar = ctx["hbar"]
    c_si = ctx["c_si"]
    g_si = ctx["g_si"]
    m_meso = ctx["m_meso"]
    r_app = ctx["r_app"]
    gamma_max_depol = ctx["gamma_max_depol"]

    k_boltz = iv.mpf("1.380649e-23")  # Exact SI definition
    # CODATA-2022 atomic mass unit u = 1.66053906892(52)e-27 kg and 4He relative atomic mass:
    u_si = iv.mpf(["1.66053906840e-27", "1.66053906944e-27"])
    m_he4 = iv.mpf(["4.0026032541", "4.0026032542"]) * u_si

    # 10 pg crystalline diamond microsphere (rho = 3515 kg/m^3), spatial splitting Delta x = 2 R_app = 100 um:
    rho_diam = iv.mpf("3515")
    r_sphere = (3 * m_meso / (4 * iv.pi * rho_diam)) ** (iv.mpf(1) / 3)
    delta_x = 2 * r_app

    # Lichnerowicz sub-horizon check for BOTH physical microsphere radius and arm envelope R_app:
    c_crit = iv.mpf("2048") / 9375
    c0_sphere = 2 * g_si * m_meso / ((c_si ** 2) * r_sphere)
    c0_app = 2 * g_si * m_meso / ((c_si ** 2) * r_app)
    require(strictly_below(c0_sphere, "2e-35") and strictly_below(c0_sphere, c_crit), "Sub-horizon sphere compactness")
    require(strictly_below(c0_app, "3e-37") and strictly_below(c0_app, c_crit), "Sub-horizon arm compactness")

    # Cryogenic UHV operating envelope: T_env = 0.5 K, P_gas = 10^-15 Pa residual 4He
    t_env = iv.mpf("0.5")
    p_gas = iv.mpf("1e-15")
    n_gas = p_gas / (k_boltz * t_env)
    v_th = iv.sqrt(8 * k_boltz * t_env / (iv.pi * m_he4))
    lambda_th_he4 = h_si / iv.sqrt(2 * iv.pi * m_he4 * k_boltz * t_env)
    require(strictly_below(lambda_th_he4, "2e-9") and strictly_below(lambda_th_he4, delta_x), "Short-wavelength gas regime")

    # Collisional localization rate Gamma_gas = n_gas * (pi R_sphere^2) * v_th:
    gamma_gas = n_gas * (iv.pi * (r_sphere ** 2)) * v_th

    # Blackbody Rayleigh scattering + thermal emission/absorption (Joos-Zeh / Romero-Isart dipole regime, lambda_bb ~ 2.88 cm >> Delta x):
    lambda_bb = h_si * c_si / (k_boltz * t_env)
    require(strictly_above(lambda_bb, "0.028") and strictly_above(lambda_bb, 100 * delta_x), "Dipole long-wavelength BB regime")

    eps_r = iv.mpf("5.7")  # Cryogenic diamond static/IR permittivity
    cm_real_sq = ((eps_r - 1) / (eps_r + 2)) ** 2
    zeta9 = _enclose_zeta_int(9, n_cut=200)
    pref_sc = iv.mpf(math.factorial(8) * 8) * zeta9 / (9 * iv.pi)
    gamma_bb_scatter = (
        pref_sc
        * c_si
        * (r_sphere ** 6)
        * ((k_boltz * t_env / (hbar * c_si)) ** 9)
        * cm_real_sq
        * (delta_x ** 2)
    )

    # Conservative cryogenic dielectric loss Im((eps-1)/(eps+2)) <= 10^-3 at T_int = T_env = 0.5 K (emission + absorption):
    im_cm_upper = iv.mpf("1e-3")
    gamma_bb_em_abs = (
        2
        * (16 * (iv.pi ** 5) / 189)
        * c_si
        * (r_sphere ** 3)
        * ((k_boltz * t_env / (hbar * c_si)) ** 6)
        * im_cm_upper
        * (delta_x ** 2)
    )

    gamma_env_total = gamma_gas + gamma_bb_scatter + gamma_bb_em_abs
    safety_ratio = gamma_max_depol / gamma_env_total
    require(
        strictly_below(gamma_env_total, "0.02") and strictly_above(safety_ratio, "6.9"),
        "Total cryo-UHV decoherence rate must satisfy Gamma_env < 0.02 s^-1 << Gamma_max (> 6.9x margin)",
    )

    return {
        "temperature_K": "0.5",
        "he4_pressure_Pa": "1e-15",
        "diamond_microsphere_radius_m": outward_str(r_sphere),
        "microsphere_Lichnerowicz_compactness": outward_str(c0_sphere),
        "he4_thermal_wavelength_m": outward_str(lambda_th_he4),
        "gas_collision_rate_s_inv": outward_str(gamma_gas),
        "blackbody_scattering_rate_s_inv": outward_str(gamma_bb_scatter),
        "blackbody_emission_absorption_rate_s_inv": outward_str(gamma_bb_em_abs),
        "total_environmental_decoherence_rate_s_inv": outward_str(gamma_env_total),
        "conservative_budget_cap_s_inv": "0.02",
        "decoherence_safety_margin_vs_depolarizing_threshold": outward_str(safety_ratio),
    }


def _validate_hardware_submission(record: dict, required_columns: tuple[str, ...]) -> tuple[bool, str]:
    """Deterministic pre-registered validator implementing HARDWARE_CERTIFICATION_CONTRACT.md §§2-3."""
    cols = set(record.get("columns", ()))
    if not set(required_columns).issubset(cols):
        return False, "MISSING_MANDATORY_HDF5_COLUMNS"
    shot_ids = record.get("shot_id", [])
    n_trig = record.get("n_triggered", -1)
    if n_trig <= 0 or shot_ids != list(range(n_trig)):
        return False, "POSTSELECTED_SHOT_DROP_REJECTED"
    if not record.get("calibration_polytope_nonempty", False):
        return False, "MODEL_SPECIFICATION_REJECTED"
    if not record.get("single_event_power_passed", False):
        return False, "INSUFFICIENT_DISCRIMINATION_POWER"
    if not record.get("holdout_blinded_and_passed", False):
        return False, "HOLDOUT_ENVELOPE_REJECTED"
    if not (record.get("witness_upper_95", 0.0) < 0.0):
        return False, "LOCC_BASELINE_NOT_VIOLATED"
    return True, "DEVICE_CERTIFIED"


def verify_spam_hoeffding_and_hardware_contract(ctx: dict) -> dict:
    dphi_grav = ctx["dphi_grav"]
    nu_cap = ctx["nu_cap"]
    w_depol_cap = ctx["w_depol_cap"]
    w_deph_cap = ctx["w_deph_cap"]

    # Asymmetric SPAM + non-computational leakage contract (P-SPAM-05):
    leak = iv.mpf("0.01")
    e0 = iv.mpf("0.008")
    e1 = iv.mpf("0.012")
    eta_spam = (1 - leak) * (1 - e0 - e1)  # 0.99 * 0.98 = 0.9702

    # 1. Noisy SPAM-corrected differential gravimetric phase readout (+/- dphi_grav) at Gamma_env = 0.02 s^-1:
    #    Additive SPAM offset (1 - leak)*e0 cancels identically in y_+ - y_- = eta_spam * nu_cap * sin(dphi_grav).
    for phi_pt in (iv.mpf(dphi_grav.a), iv.mpf(dphi_grav.b)):
        p_plus_pt = (1 + nu_cap * iv.sin(phi_pt)) / 2
        p_minus_pt = (1 - nu_cap * iv.sin(phi_pt)) / 2
        y_plus_pt = (1 - leak) * (e0 + (1 - e0 - e1) * p_plus_pt)
        y_minus_pt = (1 - leak) * (e0 + (1 - e0 - e1) * p_minus_pt)
        require(
            strictly_below(abs((y_plus_pt - y_minus_pt) - eta_spam * nu_cap * iv.sin(phi_pt)), "1e-38"),
            "Exact cancellation of asymmetric SPAM offset in differential gravimetric contrast",
        )
    contrast_noisy_spam = eta_spam * nu_cap * iv.sin(dphi_grav)

    n_diff_noisy_cont = 2 * iv.log(iv.mpf("20")) / (contrast_noisy_spam ** 2)
    n_diff_noisy_int = math.ceil(float(outward_str(n_diff_noisy_cont)[1]))
    require(
        n_diff_noisy_int == 69,
        f"Expected 69 noisy SPAM-corrected differential trials at Gamma=0.02 s^-1, got {n_diff_noisy_int}",
    )

    # 2. Non-LOCC BMV entanglement witness W < 0 certification at 95% confidence (alpha = 0.05):
    #    (a) Commuting joint stabilizer / Bell-basis readout (W_BMV = 2 I - 4 Pi_++ in [-2, +2], width 4 / eta_spam):
    n_bell_deph_spam = 8 * iv.log(iv.mpf("20")) / ((eta_spam * w_deph_cap) ** 2)
    n_bell_depol_ideal = 8 * iv.log(iv.mpf("20")) / (w_depol_cap ** 2)
    n_bell_deph_int = math.ceil(float(outward_str(n_bell_deph_spam)[1]))
    n_bell_depol_ideal_int = math.ceil(float(outward_str(n_bell_depol_ideal)[1]))
    require(
        n_bell_deph_int == 435 and n_bell_deph_int < 450 and n_bell_depol_ideal_int == 431,
        f"Joint stabilizer 95% witness shot count must be < 450, got {n_bell_deph_int}",
    )

    #    (b) Local 3-setting single-qubit Pauli readout (XX, YZ, ZY; per-arm calibrated range [-1/eta_spam^2, +1/eta_spam^2]):
    #        For N_set shots per setting (3*N_set independent bounded summands), Hoeffding 95% upper confidence bound
    #        W_hat + sqrt(6 ln(20) / (N_set * eta_spam^4)) < 0 holds at E[W_hat] = W iff N_set > 6 ln(20) / (eta_spam^4 * W^2).
    n_local_per_setting_depol = 6 * iv.log(iv.mpf("20")) / ((eta_spam ** 4) * (w_depol_cap ** 2))
    n_local_per_setting_deph = 6 * iv.log(iv.mpf("20")) / ((eta_spam ** 4) * (w_deph_cap ** 2))
    n_local_depol_int = math.ceil(float(outward_str(n_local_per_setting_depol)[1]))
    n_local_deph_int = math.ceil(float(outward_str(n_local_per_setting_deph)[1]))
    require(
        n_local_depol_int == 365 and n_local_deph_int == 347 and n_local_depol_int < 450,
        f"Per-setting local Pauli 95% witness shot count must be < 450, got {n_local_depol_int}",
    )

    # 3. Pre-registered HARDWARE_CERTIFICATION_CONTRACT.md compliance & negative controls:
    contract_md = REPO / "validation/physics_unification/HARDWARE_CERTIFICATION_CONTRACT.md"
    require(contract_md.is_file(), "Missing HARDWARE_CERTIFICATION_CONTRACT.md")
    contract_text = contract_md.read_text()
    mandatory_columns = (
        "shot_id",
        "timestamp_ns",
        "block_id",
        "setting_code",
        "initial_sign",
        "reset_telemetry",
        "leakage_flag",
        "outcome_code",
    )
    for col in mandatory_columns:
        require(f"`{col}`" in contract_text, f"Column `{col}` missing in HARDWARE_CERTIFICATION_CONTRACT.md")

    # Negative Control A: postselected / dropped trigger (shot_id gap) -> rejected
    ok_drop, code_drop = _validate_hardware_submission(
        {
            "columns": mandatory_columns,
            "n_triggered": 4,
            "shot_id": [0, 1, 3],
            "calibration_polytope_nonempty": True,
            "single_event_power_passed": True,
            "holdout_blinded_and_passed": True,
            "witness_upper_95": -0.12,
        },
        mandatory_columns,
    )
    require((not ok_drop) and code_drop == "POSTSELECTED_SHOT_DROP_REJECTED", "Postselection check failed")

    # Negative Control B: empty 99% calibration confidence region -> MODEL_SPECIFICATION_REJECTED (no vacuous pass)
    ok_empty, code_empty = _validate_hardware_submission(
        {
            "columns": mandatory_columns,
            "n_triggered": 4,
            "shot_id": [0, 1, 2, 3],
            "calibration_polytope_nonempty": False,
            "single_event_power_passed": True,
            "holdout_blinded_and_passed": True,
            "witness_upper_95": -0.12,
        },
        mandatory_columns,
    )
    require((not ok_empty) and code_empty == "MODEL_SPECIFICATION_REJECTED", "Empty calibration check failed")

    # Negative Control C: classical LOCC mediator baseline (witness_upper_95 >= 0) -> LOCC_BASELINE_NOT_VIOLATED
    ok_locc, code_locc = _validate_hardware_submission(
        {
            "columns": mandatory_columns,
            "n_triggered": 4,
            "shot_id": [0, 1, 2, 3],
            "calibration_polytope_nonempty": True,
            "single_event_power_passed": True,
            "holdout_blinded_and_passed": True,
            "witness_upper_95": 0.04,
        },
        mandatory_columns,
    )
    require((not ok_locc) and code_locc == "LOCC_BASELINE_NOT_VIOLATED", "LOCC baseline rejection failed")

    # Actual repository raw-data directory check: zero device HDF5 submissions -> device_certified = False
    raw_dir = REPO / "validation/physics_unification/raw"
    archived_h5 = sorted(raw_dir.glob("*.h5")) if raw_dir.is_dir() else []
    require(len(archived_h5) == 0, "Unexpected unverified raw hardware HDF5 archive present")

    return {
        "spam_leakage_parameters": {"leak": "0.01", "e0": "0.008", "e1": "0.012", "effective_visibility": "0.9702"},
        "noisy_differential_contrast_at_gamma_0p02": outward_str(contrast_noisy_spam),
        "noisy_differential_95pct_trials_continuous": outward_str(n_diff_noisy_cont),
        "noisy_differential_95pct_integer_trials": n_diff_noisy_int,
        "bmv_witness_95pct_shots_commuting_stabilizer_spam": n_bell_deph_int,
        "bmv_witness_95pct_shots_commuting_stabilizer_ideal_depol": n_bell_depol_ideal_int,
        "bmv_witness_95pct_shots_per_local_pauli_setting_depol": n_local_depol_int,
        "bmv_witness_95pct_shots_per_local_pauli_setting_deph": n_local_deph_int,
        "mandatory_hdf5_columns_verified": list(mandatory_columns),
        "negative_controls": [code_drop, code_empty, code_locc],
        "archived_raw_hdf5_files": 0,
        "hardware_status": "PREREGISTERED_NOT_EXECUTED",
    }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--write", action="store_true", help="Write deterministic certificate.json")
    ap.add_argument("--check", action="store_true", help="Verify against committed certificate.json without rewriting")
    ap.add_argument("--output", type=Path, default=HERE / "certificate.json")
    args = ap.parse_args()
    if args.write and args.check:
        ap.error("Specify at most one of --write and --check")

    bmv_summary, ctx = verify_bmv_4x4_and_gravimetric_thresholds()
    env_summary = verify_cryo_uhv_decoherence_budget(ctx)
    pipeline_summary = verify_spam_hoeffding_and_hardware_contract(ctx)

    payload = {
        "result_ids": ["P-MESO-BMV-06"],
        "lean_module": "formalization/ueot-physics-unification/UEOTPhysicsUnification/MesoscopicDecoherenceGravimetry.lean",
        "bmv_non_locc_witness_and_4x4_traces": bmv_summary,
        "cryogenic_uhv_decoherence_budget": env_summary,
        "spam_calibrated_hoeffding_and_blind_holdout": pipeline_summary,
        "device_certified": False,
        "physical_unification": "OPEN",
        "status": "PASS",
        "source_sha256": sha256_file(Path(__file__).resolve()),
    }
    if args.check:
        require(args.output.is_file(), f"Missing certificate file for --check: {args.output}")
        require(json.loads(args.output.read_text()) == payload, "mesoscopic_decoherence_gravimetry certificate drift")
    else:
        write_json(args.output, payload)
    print("PASS: mesoscopic_decoherence_gravimetry P-MESO-BMV-06")


if __name__ == "__main__":
    main()
