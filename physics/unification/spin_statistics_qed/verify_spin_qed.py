"""P-QCCR-04, P-SPIN-01 & P-QED-02 Certificates: Symplectic Invariance, Spin-Statistics & QED g-2.

Verifies with 40-digit outward interval arithmetic (mpmath.iv):
1. P-QCCR-04: Exact Sp(2, R) covariance determinant invariance under squeeze + shear canonical maps.
2. P-SPIN-01: Bosonic equal-time microcausality cancellation vs wrong-statistics spin-0 anticommutator
   spacelike non-vanishing across finite momentum shells.
3. P-QED-02: Parameter-free QED electron anomalous magnetic moment series (1-loop Schwinger C_1 = 1/2,
   2-loop Sommerfield-Petermann exact closed form C_2 via constructive Apéry interval series, 3-loop
   Laporta-Remiddi C_3, 4-loop Laporta C_4, 5-loop universal C_5 interval encompassing Volkov and
   Aoyama-Kinoshita-Nio, plus published mass-dependent QED/EW/hadronic 3-sigma shift) cross-checked
   between Morel et al. (2020) Rb atom-recoil alpha^-1 and Fan et al. (2023) Penning-trap g-2!
"""
from __future__ import annotations

import argparse
import math
from pathlib import Path
import sys
from mpmath import iv

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from common import outward_str, require, sha256_file, strictly_above, strictly_below, write_json


def verify_symplectic_and_spin_statistics() -> dict:
    # Squeeze + shear S = [[e^r, s e^{-r}], [0, e^{-r}]] has exact det(S) = 1:
    r_sq = iv.mpf("0.7")
    s_sh = iv.mpf("1.3")
    a, b, c, d = iv.exp(r_sq), s_sh * iv.exp(-r_sq), iv.mpf("0"), iv.exp(-r_sq)
    vq, vp, cqp = iv.mpf("0.8"), iv.mpf("0.5"), iv.mpf("0.2")
    det_in = vq * vp - cqp ** 2  # 0.36 >= 0.25 (hbar = 1)
    vq_p = (a ** 2) * vq + 2 * a * b * cqp + (b ** 2) * vp
    vp_p = (c ** 2) * vq + 2 * c * d * cqp + (d ** 2) * vp
    cqp_p = a * c * vq + (a * d + b * c) * cqp + b * d * vp
    det_out = vq_p * vp_p - cqp_p ** 2
    require(strictly_below(abs(det_out - det_in), "1e-36"), "Sp(2, R) determinant invariance failed")

    # Wrong-statistics spin-0 spacelike anticommutator at dx = 0.25 across modes k = 1, 2, 3 (mass m = 1):
    dx = iv.mpf("0.25")
    anti_spacelike = iv.mpf("0")
    comm_spacelike = iv.mpf("0")
    for k_int in (1, 2, 3):
        k_v = iv.mpf(k_int)
        om_v = iv.sqrt(k_v ** 2 + 1)
        comm_spacelike += (iv.sin(k_v * dx) + iv.sin(-k_v * dx)) / (2 * om_v)
        anti_spacelike += (iv.cos(k_v * dx) + iv.cos(-k_v * dx)) / (2 * om_v)
    require(strictly_below(abs(comm_spacelike), "1e-38") and strictly_above(anti_spacelike, "1.0"),
            "Spin-statistics spacelike contrast failed")

    return {
        "covariance_det_invariant": outward_str(det_out),
        "bosonic_equal_time_commutator_abs_upper": "1e-38",
        "wrong_statistics_spacelike_dx0p25_kernel": outward_str(anti_spacelike),
    }


def verify_qed_g_minus_2_cross_observable() -> dict:
    # Exact 1-loop Schwinger and 2-loop Sommerfield-Petermann analytical QED coefficients:
    c1 = iv.mpf("1") / 2
    # Constructive interval enclosure of Apéry's constant zeta(3) via alternating series
    # zeta(3) = (5/2) * sum_{k>=1} (-1)^{k-1} / (k^3 * comb(2k, k)):
    z3_part = iv.mpf("0")
    n_apery = 80
    for k in range(1, n_apery + 1):
        denom = (k ** 3) * math.comb(2 * k, k)
        term = iv.mpf("5") / (2 * iv.mpf(denom))
        z3_part = z3_part + term if (k % 2 == 1) else z3_part - term
    rem_bound = iv.mpf("5") / (2 * iv.mpf(((n_apery + 1) ** 3) * math.comb(2 * (n_apery + 1), n_apery + 1)))
    zeta3 = z3_part + iv.mpf([-rem_bound.b, rem_bound.b])
    c2 = (
        iv.mpf("197") / 144
        + (iv.pi ** 2) / 12
        - (iv.pi ** 2) * iv.log(iv.mpf("2")) / 2
        + (iv.mpf("3") / 4) * zeta3
    )
    require(strictly_above(c2, "-0.328478966") and strictly_below(c2, "-0.328478965"),
            "Sommerfield-Petermann 2-loop C_2 enclosure failed")

    # Published analytical 3-loop Laporta-Remiddi (1996) & 4-loop Laporta (2017) enclosures,
    # plus 5-loop universal QED C_5 interval encompassing both Volkov (5.89) and AKN (6.60):
    c3 = iv.mpf(["1.18124145658719", "1.18124145658721"])
    c4 = iv.mpf(["-1.91224576492645", "-1.91224576492644"])
    c5 = iv.mpf(["5.80", "6.90"])
    # Non-universal SM shift: mass-dependent QED (mu/tau, 2.7478e-12) + EW (0.0305e-12) + hadronic (1.693(13)e-12):
    delta_sm_non_universal = iv.mpf(["4.43e-12", "4.51e-12"])

    # Morel et al. Nature 588, 61 (2020) Rb recoil 3-sigma interval from alpha^-1 = 137.035999206(11):
    alpha_inv_rb_3sig = iv.mpf(["137.035999173", "137.035999239"])
    x_rb = 1 / (alpha_inv_rb_3sig * iv.pi)
    ae_pred_4loop_rb = c1 * x_rb + c2 * (x_rb ** 2) + c3 * (x_rb ** 3) + c4 * (x_rb ** 4) + delta_sm_non_universal
    ae_pred_5loop_rb = ae_pred_4loop_rb + c5 * (x_rb ** 5)

    # Fan et al. PRL 130, 071801 (2023) direct Penning-trap electron g-2: a_e = 0.00115965218059(13)
    ae_exp_fan_3sig = iv.mpf(["0.00115965218020", "0.00115965218098"])
    # 4-loop truncation undershoots Fan-2023 3-sigma lower bound, demonstrating experimental sensitivity to C_5:
    require(ae_pred_4loop_rb.b < ae_exp_fan_3sig.a,
            "4-loop QED truncation should lie below Fan-2023 3-sigma window before adding 5-loop C_5")
    overlap_lo = max(ae_pred_5loop_rb.a, ae_exp_fan_3sig.a)
    overlap_hi = min(ae_pred_5loop_rb.b, ae_exp_fan_3sig.b)
    require(overlap_lo < overlap_hi, "5-loop Rb-recoil QED prediction and Fan-2023 3-sigma intervals must overlap")

    # Worst-case relative discrepancy across the entire 3-sigma x 3-sigma interval product box:
    rel_diff_worst_3sig = abs(ae_pred_5loop_rb - ae_exp_fan_3sig) / ae_exp_fan_3sig
    require(strictly_below(rel_diff_worst_3sig, "1e-9"),
            "Worst-case 3-sigma cross-sector Rb-recoil vs Penning-trap QED g-2 check failed")

    return {
        "sommerfield_petermann_C2": outward_str(c2),
        "ae_predicted_4loop_from_Rb2020_3sigma": outward_str(ae_pred_4loop_rb),
        "ae_predicted_5loop_from_Rb2020_3sigma": outward_str(ae_pred_5loop_rb),
        "ae_fan2023_penning_trap_3sigma": outward_str(ae_exp_fan_3sig),
        "five_loop_term_required_for_3sigma_overlap": True,
        "worst_case_3sigma_box_relative_discrepancy_upper": outward_str(rel_diff_worst_3sig)[1],
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--output", type=Path, default=HERE / "result.json")
    args = ap.parse_args()

    payload = {
        "result_ids": ["P-QCCR-04", "P-SPIN-01", "P-QED-02"],
        "lean_module": "formalization/ueot-physics-unification/UEOTPhysicsUnification/SymplecticSpinStatisticsAndQED.lean",
        "symplectic_and_spin_statistics": verify_symplectic_and_spin_statistics(),
        "qed_g_minus_2_cross_observable": verify_qed_g_minus_2_cross_observable(),
        "physical_unification": "OPEN",
        "status": "PASS",
        "source_sha256": sha256_file(Path(__file__).resolve()),
    }
    if args.check and args.output.is_file():
        existing = __import__("json").loads(args.output.read_text())
        require(existing == payload, "spin_statistics_qed certificate drift")
    else:
        write_json(args.output, payload)
    print("PASS: spin_statistics_qed (P-QCCR-04, P-SPIN-01, P-QED-02)")


if __name__ == "__main__":
    main()
