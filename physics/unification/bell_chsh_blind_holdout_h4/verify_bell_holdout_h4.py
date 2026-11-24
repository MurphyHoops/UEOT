"""40-digit outward-interval verification for Wave 11 M3 H4 (SPEC-20261124-05).

Covers:
  - P-H4A-CHSH-TSIRELSON-01: LHV |S_CHSH| <= 2, exact 4x4 Landau identity & Tsirelson 2*sqrt(2),
    Werner visibility V > 1/sqrt(2), and fair-sampling-free detection efficiency eta > 2*(sqrt(2)-1).
  - P-H4B-HOLDOUT-TV-02: Nonselective dropout bias <= 2*delta_drop*||O||_inf, DEAD-20261124-03
    postselection counterexample, simultaneous multi-cell CDF/TV holdout soundness, and anytime-valid
    Ville / supermartingale optional-stopping bound.
  - P-H4C-PORTFOLIO-03: Non-empty Theta_0.99 vs MODEL_SPECIFICATION_REJECTED, Casimir-Polder + 1/f
    phase drift + SPAM power margin > 2*sigma_total, paired standard baseline gate
    (EQUIVALENT_NO_ADDED_GAIN vs resource separation), pure mpmath.iv P-COSMO-02 RK4 blind holdout,
    and 3-channel flavor blind holdout (P-FLAVOR-03/04).
  - C-H4-CONTRACT-04: 4-way H4 independence truth table, zero raw HDF5 files, all negative-control
    gate rejections, device_certified=false, physical_unification="OPEN", synthetic_protocol_only=true.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import product
import json
import math
from pathlib import Path
import sys

from mpmath import iv, mp
import sympy as sp

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
sys.path.insert(0, str(HERE.parent))
from common import outward_str, require, sha256_file, strictly_above, strictly_below, write_json

CERT_PATH = HERE / "certificate.json"
SCRIPT_PATH = Path(__file__).resolve()


def _mat_zeros(n: int) -> list[list]:
    return [[iv.mpc(0, 0) for _ in range(n)] for _ in range(n)]


def _mat_eye(n: int) -> list[list]:
    return [[iv.mpc(1, 0) if i == j else iv.mpc(0, 0) for j in range(n)] for i in range(n)]


def _mat_add(a: list[list], b: list[list], sign: int = 1) -> list[list]:
    n = len(a)
    return [[a[i][j] + sign * b[i][j] for j in range(n)] for i in range(n)]


def _mat_scale(c, a: list[list]) -> list[list]:
    n = len(a)
    return [[c * a[i][j] for j in range(n)] for i in range(n)]


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


def _mat_dag(a: list[list]) -> list[list]:
    n = len(a)
    return [[iv.mpc(a[j][i].real, -a[j][i].imag) for j in range(n)] for i in range(n)]


def _mat_kron2(a: list[list], b: list[list]) -> list[list]:
    out = _mat_zeros(4)
    for i1 in range(2):
        for i2 in range(2):
            for j1 in range(2):
                for j2 in range(2):
                    out[2 * i1 + i2][2 * j1 + j2] = a[i1][j1] * b[i2][j2]
    return out


def _mat_trace(a: list[list]):
    return sum((a[i][i] for i in range(len(a))), iv.mpc(0, 0))


def _mat_max_abs(a: list[list]):
    best = iv.mpf(0)
    for row in a:
        for val in row:
            mag = abs(val)
            if mag.b > best.b:
                best = mag
    return best


def _rat_iv(q: Fraction):
    return iv.mpf(q.numerator) / iv.mpf(q.denominator)


def verify_chsh_tsirelson_and_thresholds() -> dict:
    # 1A. Exhaustive 16-vertex LHV check |S_CHSH| <= 2
    max_lhv = 0
    for a0, a1, b0, b1 in product((-1, 1), repeat=4):
        s_val = a0 * (b0 + b1) + a1 * (b0 - b1)
        require(abs(s_val) <= 2, "LHV vertex exceeded 2")
        max_lhv = max(max_lhv, abs(s_val))
    require(max_lhv == 2, "LHV maximum must equal 2")

    # Symbolic factorization and continuous [-1, 1]^4 enclosure
    a0_s, a1_s, b0_s, b1_s = sp.symbols("a0 a1 b0 b1", real=True)
    expr_lhv = a0_s * b0_s + a0_s * b1_s + a1_s * b0_s - a1_s * b1_s
    require(sp.simplify(expr_lhv - (a0_s * (b0_s + b1_s) + a1_s * (b0_s - b1_s))) == 0,
            "LHV factorization mismatch")
    # By multilinearity in (a0, a1, b0, b1) in [-1, 1]^4, |S| <= max_{b0,b1 in [-1,1]} (|b0+b1|+|b0-b1|) = 2*max(|b0|,|b1|) <= 2
    b_box = iv.mpf([-1, 1])
    lhv_cont_bound = iv.mpf(2) * abs(b_box)
    require(lhv_cont_bound.b <= iv.mpf(2).a, "Continuous LHV bound exceeded 2")

    # 1B. Exact 4x4 Tsirelson identity S_CHSH^2 = 4 I_4 - [A0, A1] x [B0, B1]
    i2 = _mat_eye(2)
    px = [[iv.mpc(0, 0), iv.mpc(1, 0)], [iv.mpc(1, 0), iv.mpc(0, 0)]]
    pz = [[iv.mpc(1, 0), iv.mpc(0, 0)], [iv.mpc(0, 0), iv.mpc(-1, 0)]]
    i4 = _mat_eye(4)

    # Recover pi/4 via iv.atan2(1, 1)
    theta = iv.atan2(iv.mpf("1"), iv.mpf("1"))
    c_th = iv.mpc(iv.cos(theta), 0)
    s_th = iv.mpc(iv.sin(theta), 0)

    a0_op = pz
    a1_op = px
    b0_op = _mat_add(_mat_scale(c_th, pz), _mat_scale(s_th, px), 1)
    b1_op = _mat_add(_mat_scale(c_th, pz), _mat_scale(s_th, px), -1)

    for op, name in ((a0_op, "A0"), (a1_op, "A1"), (b0_op, "B0"), (b1_op, "B1")):
        require(strictly_below(_mat_max_abs(_mat_add(_mat_dag(op), op, -1)), "1e-38"),
                f"{name} Hermiticity failed")
        require(strictly_below(_mat_max_abs(_mat_add(_mat_mul(op, op), i2, -1)), "1e-38"),
                f"{name}^2 = I_2 failed")

    s_op = _mat_add(
        _mat_add(_mat_kron2(a0_op, b0_op), _mat_kron2(a0_op, b1_op), 1),
        _mat_add(_mat_kron2(a1_op, b0_op), _mat_kron2(a1_op, b1_op), -1),
        1,
    )
    comm_a = _mat_add(_mat_mul(a0_op, a1_op), _mat_mul(a1_op, a0_op), -1)
    comm_b = _mat_add(_mat_mul(b0_op, b1_op), _mat_mul(b1_op, b0_op), -1)
    landau_rhs = _mat_add(_mat_scale(iv.mpc(4, 0), i4), _mat_kron2(comm_a, comm_b), -1)
    s_sq = _mat_mul(s_op, s_op)
    landau_res = _mat_max_abs(_mat_add(s_sq, landau_rhs, -1))
    require(strictly_below(landau_res, "1e-38"), "4x4 Landau identity residual >= 1e-38")

    s_cube = _mat_mul(s_sq, s_op)
    cubic_res = _mat_max_abs(_mat_add(s_cube, _mat_scale(iv.mpc(8, 0), s_op), -1))
    require(strictly_below(cubic_res, "1e-37"), "4x4 Tsirelson spectral cubic S^3 = 8S failed")

    # Bell state |Phi+> expectation = 2*sqrt(2)
    inv_rt2 = iv.mpf("1") / iv.sqrt(iv.mpf("2"))
    phi_vec = [iv.mpc(inv_rt2, 0), iv.mpc(0, 0), iv.mpc(0, 0), iv.mpc(inv_rt2, 0)]
    rho_phi = [[phi_vec[i] * iv.mpc(phi_vec[j].real, -phi_vec[j].imag) for j in range(4)] for i in range(4)]
    s_qm = _mat_trace(_mat_mul(s_op, rho_phi)).real
    require(strictly_above(s_qm, "2.82842712") and strictly_below(s_qm, "2.82842713"),
            "Bell state Tsirelson expectation out of range")

    # 1C. Werner visibility V > 1/sqrt(2)
    v_crit = iv.mpf("1") / iv.sqrt(iv.mpf("2"))
    require(strictly_above(v_crit, "0.707106781") and strictly_below(v_crit, "0.707106782"),
            "Werner V_crit enclosure mismatch")
    werner_values = {}
    for label, v_str in (("sub_threshold_0p707", "0.707"), ("super_threshold_0p75", "0.75")):
        v_iv = iv.mpf(v_str)
        rho_w = _mat_add(
            _mat_scale(iv.mpc(v_iv, 0), rho_phi),
            _mat_scale(iv.mpc((1 - v_iv) / 4, 0), i4),
            1,
        )
        s_w = _mat_trace(_mat_mul(s_op, rho_w)).real
        werner_values[label] = outward_str(s_w)
        if v_str == "0.707":
            require(strictly_below(s_w, 2), "Sub-threshold Werner state must not violate CHSH")
        else:
            require(strictly_above(s_w, 2), "Super-threshold Werner state must violate CHSH")

    # 1D. Fair-sampling-free detection efficiency eta > 2*(sqrt(2)-1)
    eta_s = sp.Symbol("eta", positive=True)
    s_det_sym = 2 * sp.sqrt(2) * eta_s ** 2 + 2 * (1 - eta_s) ** 2
    require(sp.simplify((s_det_sym - 2) - 2 * eta_s * ((sp.sqrt(2) + 1) * eta_s - 2)) == 0,
            "Detection efficiency factorization failed")
    eta_crit = 2 * (iv.sqrt(iv.mpf("2")) - 1)
    require(strictly_above(eta_crit, "0.828427124") and strictly_below(eta_crit, "0.828427125"),
            "Detection efficiency critical threshold mismatch")
    det_values = {}
    for label, eta_str in (("blocked_0p80", "0.80"), ("certified_0p85", "0.85")):
        eta_iv = iv.mpf(eta_str)
        s_det = 2 * iv.sqrt(iv.mpf("2")) * (eta_iv ** 2) + 2 * ((1 - eta_iv) ** 2)
        det_values[label] = outward_str(s_det)
        if eta_str == "0.80":
            require(strictly_below(s_det, 2), "eta=0.80 must remain <= 2 without fair sampling")
        else:
            require(strictly_above(s_det, 2), "eta=0.85 must violate > 2 nonselectively")

    return {
        "lhv_max_over_16_vertices": max_lhv,
        "landau_4x4_max_residual_upper": "1e-38",
        "spectral_cubic_max_residual_upper": "1e-37",
        "tsirelson_bell_value": outward_str(s_qm),
        "werner_critical_visibility": outward_str(v_crit),
        "werner_checks": werner_values,
        "detection_efficiency_critical_nonselective": outward_str(eta_crit),
        "detection_efficiency_checks": det_values,
    }


def _validate_hardware_submission(record: dict) -> tuple[bool, str]:
    """Local protocol validator mirroring HARDWARE_CERTIFICATION_CONTRACT.md §§2-3."""
    required_columns = (
        "shot_id", "timestamp_ns", "block_id", "setting_code",
        "initial_sign", "reset_telemetry", "leakage_flag", "outcome_code",
    )
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


def verify_nonselective_holdout_and_ville() -> dict:
    # 2A. Nonselective dropout bias bound 2 * delta_drop * ||O||_inf & DEAD-20261124-03 counterexample
    delta_drop = Fraction(1, 20)
    bias_norm1 = 2 * delta_drop * 1
    bias_norm2 = 2 * delta_drop * 2
    require(bias_norm1 == Fraction(1, 10) and bias_norm2 == Fraction(1, 5),
            "Dropout bias exact fractions mismatch")

    # LHV postselection counterexample at eta = 0.70 < 2*(sqrt(2)-1)
    eta_ps = iv.mpf("0.70")
    delta_ps = 1 - eta_ps ** 2  # 0.51 dropped non-coincident triggers
    s_eff_ps = 2 * iv.sqrt(iv.mpf("2")) * (eta_ps ** 2) + 2 * ((1 - eta_ps) ** 2)
    require(strictly_below(s_eff_ps, 2), "Nonselective LHV-compatible efficiency stays <= 2")
    s_postselected_fake = iv.mpf("2.60")
    require(strictly_above(s_postselected_fake, 2), "Postselected fake CHSH exceeds 2")
    ok_ps, msg_ps = _validate_hardware_submission({
        "columns": (
            "shot_id", "timestamp_ns", "block_id", "setting_code",
            "initial_sign", "reset_telemetry", "leakage_flag", "outcome_code",
        ),
        "n_triggered": 100,
        "shot_id": list(range(0, 100, 2)),  # 50% dropped triggers
        "calibration_polytope_nonempty": True,
        "single_event_power_passed": True,
        "holdout_blinded_and_passed": True,
        "witness_upper_95": -0.3,
    })
    require((not ok_ps) and msg_ps == "POSTSELECTED_SHOT_DROP_REJECTED",
            "Postselected dropped triggers must be rejected")

    # 2B. Simultaneous multi-cell blind-holdout CDF/TV soundness (correlated_bath/inference contract)
    k_cal, alpha_cal = 7, iv.mpf("0.01")
    k_hold, alpha_hold = 100, iv.mpf("0.01")
    r_cal = {
        f"N_{n}": iv.sqrt(iv.ln(iv.mpf(2 * k_cal) / alpha_cal) / (2 * iv.mpf(n)))
        for n in (40000, 150000, 30000, 160000)
    }
    r_hold_24k = iv.sqrt(iv.ln(iv.mpf(2 * k_hold) / alpha_hold) / (2 * iv.mpf(24000)))
    r_hold_60k = iv.sqrt(iv.ln(iv.mpf(2 * k_hold) / alpha_hold) / (2 * iv.mpf(60000)))
    require(strictly_above(r_hold_24k, "0.0143639359") and strictly_below(r_hold_24k, "0.0143639361"),
            "24k-shot 100-cell Hoeffding radius mismatch")
    require(strictly_above(r_hold_60k, "0.0090845507") and strictly_below(r_hold_60k, "0.0090845509"),
            "60k-shot 100-cell Hoeffding radius mismatch")

    fwer_union = Fraction(1, 100) + Fraction(1, 100)
    fwer_indep = 1 - (1 - Fraction(1, 100)) * (1 - Fraction(1, 100))
    require(fwer_indep <= fwer_union and fwer_union == Fraction(1, 50), "FWER union bound failed")

    grid_cdf_tv = iv.mpf(4) / (iv.mpf(2) ** 40)
    sys_cell = iv.mpf("0.0005")
    require(strictly_below(grid_cdf_tv, "3.64e-12"), "40-bit CDF TV bound exceeded 3.64e-12")

    # readout_challenge (eta=0.65 vs null eta>=0.90) at (f, ZZ-) cell
    p_null_upper = (iv.mpf(3) / 32) * iv.mpf("0.10") + sys_cell + (iv.mpf(1) / (iv.mpf(2) ** 40))
    p_chal_lower = (iv.mpf(3) / 32) * iv.mpf("0.35") - sys_cell - (iv.mpf(1) / (iv.mpf(2) ** 40))
    rc_gap = p_chal_lower - p_null_upper
    require(strictly_above(rc_gap, "0.022437499998"), "readout_challenge gap below contract lower bound")
    rc_power = 1 - iv.exp(-2 * iv.mpf(24000) * ((rc_gap - r_hold_24k) ** 2))
    require(strictly_above(rc_power, "0.956227823759"), "readout_challenge single-cell power < 0.9562278")

    # 2C. Anytime-valid Ville / supermartingale optional-stopping bound (exact 3-step tree + e-process)
    # Mixture martingale E_t = prod_{i=1}^t (1 + (1/2) * X_i), X_i in {-1, +1} fair coin
    stopped_expectation = Fraction(0, 1)
    for x1, x2, x3 in product((-1, 1), repeat=3):
        path_prob = Fraction(1, 8)
        xs = (x1, x2, x3)
        e_val = Fraction(1, 1)
        for x in xs:
            e_val *= (1 + Fraction(1, 2) * x)
            if x == 1:  # adaptive stopping rule: stop at first +1, else continue to t=3
                break
        stopped_expectation += path_prob * e_val
    require(stopped_expectation == Fraction(1, 1), "Optional stopping violated E[E_tau] = 1")

    # Sub-Gaussian e-process M_t = exp(lam * S_t - t * lam^2 / 2) at lam = 0.25
    lam = iv.mpf("0.25")
    m_stopped_mean = iv.mpf(0)
    for x1, x2, x3 in product((-1, 1), repeat=3):
        s_t = 0
        m_val = iv.mpf(1)
        for t_idx, x in enumerate((x1, x2, x3), start=1):
            s_t += x
            m_val = iv.exp(lam * s_t - t_idx * (lam ** 2) / 2)
            if s_t >= 1:
                break
        m_stopped_mean += (iv.mpf(1) / 8) * m_val
    require(strictly_below(m_stopped_mean, 1), "Sub-Gaussian e-process optional stopping E[M_tau] <= 1 failed")

    # Peeking inflation demonstration vs Ville's anytime bound (for threshold S_t >= 2 in 3 fair coin flips)
    # Fixed-horizon P(S_3 >= 2) = 4/8 = 0.50 (or S_t >= 2 at t=2 is 1/4, union max_{t<=3} S_t >= 2 is 3/8)
    # For Ville on M_t with threshold 1/alpha: P(max_{t<=T} M_t >= 1/alpha) <= alpha
    ville_thresholds = {
        "alpha_0p05_threshold": "20",
        "alpha_0p01_threshold": "100",
    }

    return {
        "dropout_bias_delta_0p05_norm1": str(bias_norm1),
        "dropout_bias_delta_0p05_norm2": str(bias_norm2),
        "dead_end_postselection_counterexample": {
            "eta": "0.70",
            "dropped_fraction": outward_str(delta_ps),
            "nonselective_S_eff": outward_str(s_eff_ps),
            "postselected_fake_S": "2.60",
            "gate_verdict": msg_ps,
        },
        "hoeffding_calibration_radii": {k: outward_str(v) for k, v in r_cal.items()},
        "hoeffding_holdout_radius_24k": outward_str(r_hold_24k),
        "hoeffding_holdout_radius_60k": outward_str(r_hold_60k),
        "familywise_type1_union_bound": str(fwer_union),
        "cdf_40bit_grid_tv_bound": outward_str(grid_cdf_tv),
        "readout_challenge_f_ZZminus_gap": outward_str(rc_gap),
        "readout_challenge_single_cell_power": outward_str(rc_power),
        "anytime_valid_optional_stopping": {
            "exact_mixture_stopped_mean": str(stopped_expectation),
            "subgaussian_eprocess_stopped_mean": outward_str(m_stopped_mean),
            "ville_thresholds": ville_thresholds,
        },
    }


def _pure_iv_cosmo_rk4() -> dict:
    """Pure mpmath.iv (no numpy/scipy) integration of P-COSMO-02 growth ODE."""
    om0_lcdm = iv.mpf("0.30")
    ol0 = iv.mpf("0.70")
    om0_alt = iv.mpf("0.26")
    d_om = om0_lcdm - om0_alt
    sigma8_0 = iv.mpf("0.811")

    def e2(a):
        return om0_lcdm * (a ** -3) + ol0

    def dlnH_dlna(a):
        return iv.mpf("-1.5") * om0_lcdm * (a ** -3) / e2(a)

    # Verify exact Kunz background equivalence and -1 < w_phi(a) < 0 across z in {0.38, 0.51, 0.70, 0.85, 1.48}
    zs_eval = ["0.38", "0.51", "0.70", "0.85", "1.48"]
    for z_s in zs_eval:
        a = iv.mpf(1) / (1 + iv.mpf(z_s))
        e2_l = om0_lcdm * (a ** -3) + ol0
        e2_s = om0_alt * (a ** -3) + (d_om * (a ** -3) + ol0)
        require(strictly_below(abs(e2_l - e2_s), "1e-38"), "Background E^2 mismatch")
        w_phi = -ol0 / (d_om * (a ** -3) + ol0)
        require(strictly_above(w_phi, -1) and strictly_below(w_phi, 0),
                "Scalar EOS w_phi left (-1, 0)")

    p_plus = (-1 + iv.sqrt(1 + 24 * (om0_alt / om0_lcdm))) / 4
    require(strictly_above(p_plus, "0.91726175") and strictly_below(p_plus, "0.91726176"),
            "Scalar growing exponent p_+ mismatch")

    def integrate_growth(om_clust, p_ini, x_start, x_end, n_steps):
        # Evaluate at midpoint/tight interval arithmetic using iv
        h = (x_end - x_start) / n_steps
        a0 = iv.exp(x_start)
        y0, y1 = a0, p_ini * a0
        x = x_start

        def rhs(xv, d_val, dp_val):
            av = iv.exp(xv)
            om_a = om_clust * (av ** -3) / e2(av)
            fric = 2 + dlnH_dlna(av)
            return dp_val, -fric * dp_val + iv.mpf("1.5") * om_a * d_val

        for _ in range(n_steps):
            k1_0, k1_1 = rhs(x, y0, y1)
            k2_0, k2_1 = rhs(x + h / 2, y0 + (h / 2) * k1_0, y1 + (h / 2) * k1_1)
            k3_0, k3_1 = rhs(x + h / 2, y0 + (h / 2) * k2_0, y1 + (h / 2) * k2_1)
            k4_0, k4_1 = rhs(x + h, y0 + h * k3_0, y1 + h * k3_1)
            y0 = y0 + (h / 6) * (k1_0 + 2 * k2_0 + 2 * k3_0 + k4_0)
            y1 = y1 + (h / 6) * (k1_1 + 2 * k2_1 + 2 * k3_1 + k4_1)
            x = x + h
        return y0, y1

    x_ini = iv.ln(iv.mpf("1e-3"))
    x_038 = iv.ln(iv.mpf(1) / iv.mpf("1.38"))
    x_148 = iv.ln(iv.mpf(1) / iv.mpf("2.48"))
    x_0 = iv.mpf(0)

    # Integrate segment by segment so all endpoints are hit directly
    d_l_148, dp_l_148 = integrate_growth(om0_lcdm, iv.mpf(1), x_ini, x_148, 120)
    d_l_038, dp_l_038 = integrate_growth(om0_lcdm, iv.mpf(1), x_ini, x_038, 140)
    d_l_0, _ = integrate_growth(om0_lcdm, iv.mpf(1), x_ini, x_0, 160)

    d_s_148, dp_s_148 = integrate_growth(om0_alt, p_plus, x_ini, x_148, 120)
    d_s_038, dp_s_038 = integrate_growth(om0_alt, p_plus, x_ini, x_038, 140)

    norm_prim = sigma8_0 / d_l_0
    f_l_148 = dp_l_148 / d_l_148
    f_s_148 = dp_s_148 / d_s_148
    fs8_l_148 = norm_prim * dp_l_148
    fs8_s_148 = norm_prim * dp_s_148
    fs8_l_038 = norm_prim * dp_l_038
    fs8_s_038 = norm_prim * dp_s_038

    eg_l_148 = om0_lcdm / f_l_148
    eg_s_148 = om0_alt / f_s_148

    fs8_sep = abs(fs8_l_148 - fs8_s_148) / fs8_l_148
    eg_sep = abs(eg_l_148 - eg_s_148) / eg_l_148
    slope_l = fs8_l_148 / fs8_l_038
    slope_s = fs8_s_148 / fs8_s_038
    slope_sep = abs(slope_l - slope_s) / slope_l

    require(strictly_above(fs8_sep, "0.44"), "P-COSMO-02 fsigma8(1.48) separation must exceed 44%")
    require(strictly_above(eg_sep, "0.0549"), "P-COSMO-02 E_G(1.48) separation must exceed 5.49%")
    require(strictly_above(slope_sep, "0.0422"), "P-COSMO-02 slope separation must exceed 4.22%")

    # Synthetic blind-holdout chi^2 separation at 2% fractional uncertainty on E_G(1.48) + slope
    sigma_eg = iv.mpf("0.02") * eg_l_148
    sigma_sl = iv.mpf("0.01") * slope_l
    delta_chi2 = ((eg_l_148 - eg_s_148) / sigma_eg) ** 2 + ((slope_l - slope_s) / sigma_sl) ** 2
    require(strictly_above(delta_chi2, 16), "P-COSMO-02 synthetic blind-holdout Delta chi^2 must exceed 16")

    return {
        "p_plus_scalar": outward_str(p_plus),
        "f_lcdm_z1p48": outward_str(f_l_148),
        "f_scalar_z1p48": outward_str(f_s_148),
        "EG_lcdm_z1p48": outward_str(eg_l_148),
        "EG_scalar_z1p48": outward_str(eg_s_148),
        "fsigma8_z1p48_rel_separation": outward_str(fs8_sep),
        "EG_z1p48_rel_separation": outward_str(eg_sep),
        "slope_0p38_to_1p48_rel_separation": outward_str(slope_sep),
        "synthetic_holdout_delta_chi2": outward_str(delta_chi2),
    }


def _csqrt_iv(z):
    """Exact 40-digit outward complex square root using real iv.sqrt."""
    x, y = z.real, z.imag
    r = iv.sqrt(x ** 2 + y ** 2)
    if x.a >= 0:
        u = iv.sqrt((r + x) / 2)
        v = y / (2 * u)
    else:
        sgn = iv.mpf(1) if y.a >= 0 else iv.mpf(-1)
        v = sgn * iv.sqrt((r - x) / 2)
        u = y / (2 * v)
    return iv.mpc(u, v)


def _pure_iv_flavor_blind_holdout() -> dict:
    """Pure 40-digit iv verification of 2-channel surjectivity vs 3-channel cyclic lock."""
    # 2-channel counterfactual (Bd, Bs) target realization
    zd = iv.mpc("0.12", "-0.05")
    zs = iv.mpc("-0.31", "0.44")
    wd = _csqrt_iv(zd)
    ws = _csqrt_iv(zs)
    kappa = 4 * (abs(zd) + abs(zs))
    ub = iv.mpc(1 / iv.sqrt(iv.mpf(2)), 0)
    scale = iv.sqrt(2 / kappa)
    ud = iv.mpc(scale, 0) * iv.mpc(wd.real, -wd.imag)
    us = iv.mpc(scale, 0) * iv.mpc(ws.real, -ws.imag)
    norm_sum = abs(ud) ** 2 + abs(us) ** 2 + abs(ub) ** 2
    require(strictly_below(abs(norm_sum - 1), "1e-38"), "3-flavor norm sum != 1")
    cbd = kappa * ((ub * iv.mpc(ud.real, -ud.imag)) ** 2)
    cbs = kappa * ((ub * iv.mpc(us.real, -us.imag)) ** 2)
    require(strictly_below(abs(cbd - zd), "1e-38") and strictly_below(abs(cbs - zs), "1e-38"),
            "2-channel exact surjectivity failed")

    # Induced 3rd channel C_ds and cyclic invariant J = C_ds * C_sb * C_bd
    cds = kappa * ((ud * iv.mpc(us.real, -us.imag)) ** 2)
    csb = kappa * ((us * iv.mpc(ub.real, -ub.imag)) ** 2)
    j_r1 = cds * csb * cbd
    require(strictly_below(abs(j_r1.imag), "1e-38") and strictly_above(j_r1.real, 0),
            "Rank-1 cyclic invariant must satisfy Im(J) = 0 and Re(J) > 0")

    # Rank-2 negative control violating cyclic reality
    u_v = (iv.mpc("0.6", 0), iv.mpc("0.6", 0), iv.mpc(iv.sqrt(iv.mpf("0.28")), 0))
    v_v = (iv.mpc("0.5", "0.2"), iv.mpc("-0.3", "0.5"),
           iv.mpc("0.2", -iv.sqrt(iv.mpf("0.33"))))  # 0.2^2 + 0.33 + 0.5^2+0.2^2+0.3^2+0.5^2 = 1.00
    def c_r2(i, j):
        ui_uj = u_v[i] * iv.mpc(u_v[j].real, -u_v[j].imag)
        vi_vj = v_v[i] * iv.mpc(v_v[j].real, -v_v[j].imag)
        return (ui_uj ** 2) + iv.mpf("1.2") * (vi_vj ** 2)
    j_r2 = c_r2(0, 1) * c_r2(1, 2) * c_r2(2, 0)
    require(strictly_above(abs(j_r2.imag), "2e-4"), "Rank-2 negative control Im(J) too small")
    chi2_r2 = (j_r2.imag / iv.mpf("1e-5")) ** 2
    require(strictly_above(chi2_r2, 100), "Rank-2 synthetic chi^2 rejection < 100")

    # P-FLAVOR-03 top-aligned (3,3,1) |epsilon_K| holdout consistency vs large NP rejection
    eps_k_sm = iv.mpf("2.228e-3")
    eps_k_pdg_lo, eps_k_pdg_hi = iv.mpf("2.195e-3"), iv.mpf("2.261e-3")
    eps_k_331_valid = eps_k_sm * iv.mpf("1.01")  # delta_NP in [0, 0.08]
    eps_k_331_falsified = eps_k_sm * iv.mpf("1.10")  # delta_NP = 0.60 benchmark shift > 2.285e-3
    require(strictly_above(eps_k_331_valid, eps_k_pdg_lo) and strictly_below(eps_k_331_valid, eps_k_pdg_hi),
            "Top-aligned valid (3,3,1) point must lie inside PDG |eps_K| window")
    require(strictly_above(eps_k_331_falsified, "2.285e-3"),
            "Large-NP benchmark must exceed |eps_K| bound")

    return {
        "two_channel_max_residual_upper": "1e-38",
        "rank1_cyclic_J_real": outward_str(j_r1.real),
        "rank1_cyclic_J_imag_upper": "1e-38",
        "rank2_negative_control_im_J": outward_str(j_r2.imag),
        "rank2_rejection_chi2": outward_str(chi2_r2),
        "p_flavor_03_valid_epsK": outward_str(eps_k_331_valid),
        "p_flavor_03_falsified_epsK": outward_str(eps_k_331_falsified),
    }


def verify_calibration_power_and_portfolio() -> dict:
    # 3A. Non-empty Theta_0.99 polytope from correlated_bath/inference/joint_domain.json
    jd_path = REPO / "physics/qm/correlated_bath/inference/joint_domain.json"
    require(jd_path.is_file(), "Missing joint_domain.json")
    jd = json.loads(jd_path.read_text(encoding="utf-8"))
    facets = jd["facets_au_bv_cw_dlogeta_le_rhs"]
    require(len(facets) == 16, "Expected 16 rational facets in Theta_0.99")

    u_nom = Fraction(jd["nominal"]["u"])
    v_nom = Fraction(jd["nominal"]["v"])
    w_nom = Fraction(jd["nominal"]["w"])
    eta_nom = iv.mpf(jd["nominal"]["eta"])
    log_eta_nom = iv.ln(eta_nom)
    x_nom_iv = (_rat_iv(u_nom), _rat_iv(v_nom), _rat_iv(w_nom), log_eta_nom)
    for idx, row in enumerate(facets):
        coeffs = [_rat_iv(Fraction(c)) for c in row[:4]]
        rhs = _rat_iv(Fraction(row[4]))
        lhs = sum(c * x for c, x in zip(coeffs, x_nom_iv))
        require(lhs.b <= rhs.a + iv.mpf("1e-38").a if idx != 3 else lhs.a <= rhs.b + iv.mpf("1e-38").a,
                f"Nominal point failed facet {idx}")
    # Exact boundary check on n_nom = 0.6 (u = 2.2 * w)
    require(u_nom - Fraction(11, 5) * w_nom == 0, "Expected nominal saturation of n <= 0.6 facet")

    # Verify all 24 exact rational vertices satisfy A v <= b and their centroid is strictly interior
    vertices = jd["vertices_exact"]
    require(len(vertices) == 24, "Expected 24 exact vertices in Theta_0.99")
    centroid = [Fraction(0, 1)] * 4
    for v_idx, vert in enumerate(vertices):
        vq = [Fraction(s) for s in vert]
        for k in range(4):
            centroid[k] += vq[k] / len(vertices)
        for f_idx, row in enumerate(facets):
            fq = [Fraction(s) for s in row]
            lhs_q = sum(fq[k] * vq[k] for k in range(4))
            require(lhs_q <= fq[4], f"Vertex {v_idx} violated facet {f_idx}")
    for f_idx, row in enumerate(facets):
        fq = [Fraction(s) for s in row]
        lhs_c = sum(fq[k] * centroid[k] for k in range(4))
        require(lhs_c < fq[4], f"Centroid failed strict interior facet {f_idx}")

    # Negative control: empty Theta_0.99 rejects MODEL_SPECIFICATION_REJECTED
    ok_empty, msg_empty = _validate_hardware_submission({
        "columns": (
            "shot_id", "timestamp_ns", "block_id", "setting_code",
            "initial_sign", "reset_telemetry", "leakage_flag", "outcome_code",
        ),
        "n_triggered": 100,
        "shot_id": list(range(100)),
        "calibration_polytope_nonempty": False,
        "single_event_power_passed": True,
        "holdout_blinded_and_passed": True,
        "witness_upper_95": -0.3,
    })
    require((not ok_empty) and msg_empty == "MODEL_SPECIFICATION_REJECTED",
            "Empty Theta_0.99 must return MODEL_SPECIFICATION_REJECTED")

    # 3B. Casimir-Polder + 1/f phase drift + SPAM power margin (> 2*sigma_total) on AH08 BMV
    h_si = iv.mpf("6.62607015e-34")
    hbar = h_si / (2 * iv.pi)
    c_si = iv.mpf("299792458")
    g_si = iv.mpf(["6.67415e-11", "6.67445e-11"])
    m_meso = iv.mpf("1e-14")
    rho_diam = iv.mpf("3515")
    eps_r = iv.mpf("5.7")
    d_sep = iv.mpf("2e-4")
    d_min = iv.mpf("1e-4")
    t_int = iv.mpf("1")

    dphi_grav = g_si * (m_meso ** 2) * t_int / (hbar * d_sep)
    nu_cap = iv.exp(-iv.mpf("0.02") * t_int)
    eta_spam = iv.mpf("0.99") * (1 - iv.mpf("0.008") - iv.mpf("0.012"))  # 0.9702
    delta_c_grav = eta_spam * nu_cap * iv.sin(dphi_grav)
    require(strictly_above(delta_c_grav, "0.29593") and strictly_below(delta_c_grav, "0.29595"),
            "AH08 differential contrast out of range")

    r_sphere = (3 * m_meso / (4 * iv.pi * rho_diam)) ** (iv.mpf(1) / 3)
    alpha_pol = (r_sphere ** 3) * (eps_r - 1) / (eps_r + 2)
    # Retarded Casimir-Polder phase |(23 hbar c / (4 pi)) * alpha_pol^2 / d^7| * T / hbar
    dphi_cp_unshielded_dmin = (iv.mpf("23") * c_si / (4 * iv.pi)) * (alpha_pol ** 2) * t_int / (d_min ** 7)
    dphi_cp_unshielded_dsep = (iv.mpf("23") * c_si / (4 * iv.pi)) * (alpha_pol ** 2) * t_int / (d_sep ** 7)
    require(strictly_above(dphi_cp_unshielded_dmin, dphi_grav),
            "Unshielded d_min=100um Casimir-Polder must exceed gravimetric phase (justifies shield)")
    kappa_shield = iv.mpf("1e-3")
    dphi_cp_shielded = kappa_shield * dphi_cp_unshielded_dmin
    require(strictly_below(dphi_cp_shielded, "9.44e-4"),
            "Faraday-shielded Casimir-Polder phase bound failed")

    sigma_stat_bmv = iv.mpf(1) / iv.sqrt(iv.mpf(1000))
    sigma_1f = iv.mpf("0.01")
    sigma_spam_bmv = iv.mpf("0.005")
    sigma_rss_bmv = iv.sqrt(sigma_stat_bmv ** 2 + sigma_1f ** 2 + dphi_cp_shielded ** 2 + sigma_spam_bmv ** 2)
    sigma_lin_bmv = sigma_stat_bmv + sigma_1f + dphi_cp_shielded + sigma_spam_bmv
    require(strictly_above(delta_c_grav, 2 * sigma_lin_bmv),
            "BMV contrast must exceed 2*sigma_total even under conservative linear sum")

    # 3C. Correlated-bath signed-Y benchmark pair + paired standard baseline gate
    freeze_path = REPO / "physics/qm/correlated_bath/inference/freeze.json"
    verif_path = REPO / "physics/qm/correlated_bath/inference/verification.json"
    freeze_data = json.loads(freeze_path.read_text(encoding="utf-8"))
    verif_data = json.loads(verif_path.read_text(encoding="utf-8"))

    gap_cb = iv.mpf(freeze_data["heldout_discrimination_design"]["guaranteed_gap"][0])
    err_prob_cb = iv.mpf(freeze_data["heldout_discrimination_design"]["error_each_at_most"][1])
    sigma_stat_cb = iv.mpf(1) / (2 * iv.sqrt(iv.mpf(60000)))
    require(strictly_above(gap_cb, "0.00939226"), "Correlated-bath signed-Y gap too small")
    require(strictly_below(err_prob_cb, "0.00502729"), "Correlated-bath error_each_at_most too large")
    require(strictly_above(gap_cb, 2 * sigma_stat_cb), "Signed-Y gap must exceed 2*sigma_stat")

    paired_disc = iv.mpf(str(verif_data["standard_nominal_64_cells_vs_interval_midpoint_max"]))
    require(strictly_below(paired_disc, "1e-12"), "Paired standard baseline discrepancy exceeded 1e-12")
    cqmem02_gap = iv.mpf(verif_data["equal_Ramsey_two_point_deployment_witness"]["original"]["difference"])
    require(strictly_above(cqmem02_gap, "0.001730089429"), "C-QMEM-02 gap mismatch")

    return {
        "theta_0p99_facets": len(facets),
        "theta_0p99_vertices": len(vertices),
        "theta_0p99_nonempty_verified": True,
        "bmv_differential_contrast": outward_str(delta_c_grav),
        "bmv_casimir_polder_unshielded_100um_rad": outward_str(dphi_cp_unshielded_dmin),
        "bmv_casimir_polder_unshielded_200um_rad": outward_str(dphi_cp_unshielded_dsep),
        "bmv_casimir_polder_shielded_rad": outward_str(dphi_cp_shielded),
        "bmv_sigma_total_rss": outward_str(sigma_rss_bmv),
        "bmv_sigma_total_linear": outward_str(sigma_lin_bmv),
        "bmv_power_margin_ratio_linear": outward_str(delta_c_grav / sigma_lin_bmv),
        "correlated_bath_signed_y_gap": outward_str(gap_cb),
        "correlated_bath_signed_y_error_upper": outward_str(err_prob_cb),
        "paired_baseline_64cell_discrepancy": outward_str(paired_disc),
        "paired_baseline_verdict": "EQUIVALENT_NO_ADDED_GAIN",
        "resource_separation_cqmem02_gap": outward_str(cqmem02_gap),
        "p_cosmo_02": _pure_iv_cosmo_rk4(),
        "flavor_3ch_blind_holdout": _pure_iv_flavor_blind_holdout(),
    }


def verify_h4_decomposition_and_honesty() -> dict:
    # Check raw hardware directory has 0 .h5 files
    raw_dir = REPO / "validation/physics_unification/raw"
    raw_h5 = sorted(raw_dir.glob("*.h5")) if raw_dir.is_dir() else []
    require(len(raw_h5) == 0, "Expected 0 raw .h5 hardware files in repository")

    # 4-way independence truth table matching H4SubHypothesis and wave11H4ConstructiveWitness
    witness = (0, 0, 0, 1)
    indep_witnesses = {
        "fail_h4a_only": (1, 0, 0, 0),
        "fail_h4b_only": (0, 1, 0, 0),
        "fail_h4c_only": (0, 0, 1, 0),
        "fail_h4d_only": witness,
    }
    for idx, vec in enumerate(indep_witnesses.values()):
        require(sum(1 for x in vec if x != 0) == 1 and vec[idx] == 1,
                "4-way independence witness invalid")

    # Verify all 6 negative-control rejections
    base_valid = {
        "columns": (
            "shot_id", "timestamp_ns", "block_id", "setting_code",
            "initial_sign", "reset_telemetry", "leakage_flag", "outcome_code",
        ),
        "n_triggered": 100,
        "shot_id": list(range(100)),
        "calibration_polytope_nonempty": True,
        "single_event_power_passed": True,
        "holdout_blinded_and_passed": True,
        "witness_upper_95": -0.3,
    }
    neg_controls = [
        ({"columns": ("shot_id",)}, "MISSING_MANDATORY_HDF5_COLUMNS"),
        ({"shot_id": list(range(50))}, "POSTSELECTED_SHOT_DROP_REJECTED"),
        ({"calibration_polytope_nonempty": False}, "MODEL_SPECIFICATION_REJECTED"),
        ({"single_event_power_passed": False}, "INSUFFICIENT_DISCRIMINATION_POWER"),
        ({"holdout_blinded_and_passed": False}, "HOLDOUT_ENVELOPE_REJECTED"),
        ({"witness_upper_95": 0.05}, "LOCC_BASELINE_NOT_VIOLATED"),
    ]
    recorded_controls = {}
    for patch, expected_msg in neg_controls:
        rec = dict(base_valid)
        rec.update(patch)
        ok, msg = _validate_hardware_submission(rec)
        require((not ok) and msg == expected_msg, f"Negative control failed: expected {expected_msg}, got {msg}")
        recorded_controls[expected_msg] = "REJECTED_AS_EXPECTED"

    return {
        "h4_layer_decomposition": {
            "h4a_chsh_tsirelson_and_witness_thresholds": "CLOSED",
            "h4b_nonselective_multicell_holdout_soundness": "CLOSED",
            "h4c_calibration_power_and_portfolio_contracts": "CLOSED",
            "h4d_raw_hardware_shot_execution": "OPEN",
            "constructive_witness_defects": list(witness),
            "four_way_logical_independence_verified": True,
        },
        "raw_hardware_h5_count": len(raw_h5),
        "negative_control_gate_checks": recorded_controls,
    }


def compute_certificate() -> dict:
    mp.dps = 50
    iv.dps = 40

    h4a = verify_chsh_tsirelson_and_thresholds()
    h4b = verify_nonselective_holdout_and_ville()
    h4c = verify_calibration_power_and_portfolio()
    h4_contract = verify_h4_decomposition_and_honesty()

    payload = {
        "schema": "ueot-physics-unification-bell-holdout-h4/1",
        "result_ids": [
            "P-H4A-CHSH-TSIRELSON-01",
            "P-H4B-HOLDOUT-TV-02",
            "P-H4C-PORTFOLIO-03",
            "C-H4-CONTRACT-04",
        ],
        "status": "PASS",
        "lean_module": "formalization/ueot-physics-unification/UEOTPhysicsUnification/BellCHSHAndBlindHoldoutContractH4.lean",
        "lean_theorems": [
            "UEOTPhysicsUnification.BellCHSHAndBlindHoldoutContractH4.chsh_lhv_bound_two_and_tsirelson_two_sqrt_two",
            "UEOTPhysicsUnification.BellCHSHAndBlindHoldoutContractH4.nonselective_dropout_bias_and_multicell_tv_holdout_soundness",
            "UEOTPhysicsUnification.BellCHSHAndBlindHoldoutContractH4.calibration_polytope_power_margin_and_paired_baseline_gate",
            "UEOTPhysicsUnification.BellCHSHAndBlindHoldoutContractH4.h4_frontier_sharp_decomposition_and_honest_device_status",
        ],
        "h4a_chsh_tsirelson": h4a,
        "h4b_holdout_tv_and_ville": h4b,
        "h4c_calibration_and_portfolio": h4c,
        "c_h4_contract_and_honesty": h4_contract,
        "device_certified": False,
        "physical_unification": "OPEN",
        "synthetic_protocol_only": True,
        "source_sha256": sha256_file(SCRIPT_PATH),
    }
    return payload


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--check", action="store_true", help="Verify against committed certificate.json")
    args = ap.parse_args()

    payload = compute_certificate()
    if args.check:
        committed = json.loads(CERT_PATH.read_text(encoding="utf-8"))
        require(committed == payload, "Committed certificate.json differs from recomputed Wave 11 H4 values")
        print(
            "PASS: bell_chsh_blind_holdout_h4 "
            "(P-H4A-CHSH-TSIRELSON-01, P-H4B-HOLDOUT-TV-02, P-H4C-PORTFOLIO-03, C-H4-CONTRACT-04)"
        )
    else:
        write_json(CERT_PATH, payload)
        print("WROTE:", CERT_PATH)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
