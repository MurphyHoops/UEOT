"""P-MICRO-06B & P-MICRO-11 Certificates: Galerkin Duhamel Defect & Correlated Two-Mode Gaussian Tails.

Verifies with 40-digit outward interval arithmetic (mpmath.iv) and exact matrix algebra:
1. P-MICRO-06B: Exact multi-step noncommutative Galerkin telescoping identity
   U^N J - J U_K^N = sum_{m=0}^{N-1} U^{N-1-m} (U J - J U_K) U_K^m to machine precision (< 1e-14).
2. P-MICRO-11: Chapter 71 correlated two-mode Gaussian bath (omega = (1, 3/2), g = (1, 3/5),
   segments a = 2/3, b = 3/4) on both Ramsey-degenerate witness triples (3/10, 1/2, 1/4) and
   (1/3, 31/100, 81/400):
   - Encloses the exact normal-mode Fock tail bound ((n+c)/(n+c+1))^(K+1) + ((n-c)/(n-c+1))^(K+1)
     across K in {8, 14, 20} and across the design-box worst corner (n = 0.6, c = 0.6 -> n_+ = 1.2),
   - Encloses the exact signed Weyl intervention phases s * lam^2 * F (0.16373162... and 0.20213780...)
     in directed outward decimal intervals.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import sys
import numpy as np
from scipy.linalg import expm
from mpmath import iv

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from common import outward_str, require, sha256_file, strictly_above, strictly_below, write_json


def verify_galerkin_telescoping() -> dict:
    # Full dim D_full = 12 vs truncated Galerkin dim D_cut = 6 for driven oscillator H = N + g(a + a^dag)
    d_full, d_cut = 12, 6
    a = np.zeros((d_full, d_full), dtype=complex)
    for m in range(1, d_full):
        a[m - 1, m] = np.sqrt(float(m))
    g_drv = 0.35
    H_full = np.diag(np.arange(d_full, dtype=float)) + g_drv * (a + a.conj().T)
    J = np.zeros((d_full, d_cut), dtype=complex)
    J[:d_cut, :d_cut] = np.eye(d_cut, dtype=complex)
    H_cut = J.conj().T @ H_full @ J

    dt = 0.1
    U = expm(-1j * dt * H_full)
    UK = expm(-1j * dt * H_cut)
    step_defect = U @ J - J @ UK

    n_steps = 8
    lhs = np.linalg.matrix_power(U, n_steps) @ J - J @ np.linalg.matrix_power(UK, n_steps)
    rhs = np.zeros_like(lhs)
    for m in range(n_steps):
        rhs += np.linalg.matrix_power(U, n_steps - 1 - m) @ step_defect @ np.linalg.matrix_power(UK, m)

    max_id_err = float(np.max(np.abs(lhs - rhs)))
    require(max_id_err < 1e-14, f"Galerkin telescoping identity error too large: {max_id_err}")

    return {
        "full_dim": d_full,
        "galerkin_cutoff_dim": d_cut,
        "steps_N": n_steps,
        "telescoping_identity_error_strictly_below": "1e-14",
    }


def verify_correlated_bath_tails_and_weyl_phases() -> dict:
    # Exact Chapter 71 two-mode bath parameters: omega = (1, 3/2), g = (1, 3/5), a = 2/3, b = 3/4
    om1, om2 = iv.mpf("1"), iv.mpf("3") / 2
    g1, g2 = iv.mpf("1"), iv.mpf("3") / 5
    t_a, t_b = iv.mpf("2") / 3, iv.mpf("3") / 4

    def mode_phase_factor(om: iv.mpf, g: iv.mpf) -> iv.mpf:
        return 4 * ((g / om) ** 2) * (iv.sin(om * t_a) + iv.sin(om * t_b) - iv.sin(om * (t_a + t_b)))

    F_weyl = mode_phase_factor(om1, g1) + mode_phase_factor(om2, g2)
    require(strictly_above(F_weyl, "1.8192401") and strictly_below(F_weyl, "1.8192403"),
            "Weyl phase kernel F enclosure mismatch")

    witnesses = {
        "witness_A_3_10": (iv.mpf("3") / 10, iv.mpf("1") / 2, iv.mpf("1") / 4),
        "witness_B_1_3": (iv.mpf("1") / 3, iv.mpf("31") / 100, iv.mpf("81") / 400),
    }
    witness_certs = {}
    for label, (lam, n_occ, c_corr) in witnesses.items():
        phase = (lam ** 2) * F_weyl
        np_occ = n_occ + c_corr
        nm_occ = n_occ - c_corr
        tails = {}
        for K in (8, 14, 20):
            tp = (np_occ / (np_occ + 1)) ** (K + 1)
            tm = (nm_occ / (nm_occ + 1)) ** (K + 1)
            exact_leak = 1 - (1 - tp) * (1 - tm)
            union_ub = tp + tm
            require(strictly_below(exact_leak, union_ub) or exact_leak == union_ub,
                    "Union bound violated")
            tails[f"K_{K}"] = {
                "exact_normal_box_leakage": outward_str(exact_leak),
                "lean_union_upper_bound": outward_str(union_ub)[1],
            }
        witness_certs[label] = {
            "signed_weyl_phase_rad": outward_str(phase),
            "normal_occupations": [outward_str(np_occ), outward_str(nm_occ)],
            "fock_box_tails": tails,
        }

    # Worst-case design-box corner (n = 0.6, |c| = 0.6 -> n_+ = 1.2, n_- = 0.0) at K = 40:
    np_max = iv.mpf("1.2")
    worst_k40_tail = (np_max / (np_max + 1)) ** 41
    require(strictly_below(worst_k40_tail, "1e-10"), "K=40 design-box tail should be < 1e-10")

    return {
        "weyl_phase_kernel_F": outward_str(F_weyl),
        "ramsey_degenerate_witness_tails": witness_certs,
        "design_box_worst_corner_K40_tail_upper": outward_str(worst_k40_tail)[1],
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--output", type=Path, default=HERE / "result.json")
    args = ap.parse_args()

    payload = {
        "result_ids": ["P-MICRO-06B", "P-MICRO-11"],
        "lean_module": "formalization/ueot-physics-unification/UEOTPhysicsUnification/CorrelatedGaussianTailAndGalerkin.lean",
        "galerkin_telescoping": verify_galerkin_telescoping(),
        "correlated_bath_tails": verify_correlated_bath_tails_and_weyl_phases(),
        "physical_unification": "OPEN",
        "status": "PASS",
        "source_sha256": sha256_file(Path(__file__).resolve()),
    }
    if args.check and args.output.is_file():
        existing = __import__("json").loads(args.output.read_text())
        require(existing == payload, "micro_gaussian_tail_galerkin certificate drift")
    else:
        write_json(args.output, payload)
    print("PASS: micro_gaussian_tail_galerkin (P-MICRO-06B, P-MICRO-11)")


if __name__ == "__main__":
    main()
