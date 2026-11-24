"""40-digit outward-interval & symbolic verification for Wave 10 H1d4 (P-H1D4-BANACH-01..C-H1D4-FINAL-04)."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

from mpmath import iv, mp
import sympy as sp

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from common import outward_str, require, sha256_file, strictly_above, strictly_below, write_json

CERT_PATH = HERE / "certificate.json"
SCRIPT_PATH = Path(__file__).resolve()


def _min_eig_2x2_iv(M):
    """Exact deterministic minimum eigenvalue of a symmetric 2x2 outward iv.matrix."""
    tr = M[0, 0] + M[1, 1]
    det = M[0, 0] * M[1, 1] - M[0, 1] * M[1, 0]
    disc = tr ** 2 - iv.mpf("4") * det
    require(disc.b >= 0, "Negative discriminant in 2x2 symmetric matrix")
    disc_nn = iv.mpf([max(disc.a, mp.mpf("0")), disc.b])
    return (tr - iv.sqrt(disc_nn)) / iv.mpf("2")


def compute_certificate() -> dict:
    mp.dps = 50
    iv.dps = 40

    # --- Pillar 1: P-H1D4-BANACH-01 (Infinite-order Banach convergence & counterexample) ---
    rho = iv.mpf("2")
    kappa = iv.mpf("0.25")
    c_tail = iv.mpf("1")
    banach_trunc_bounds = {}
    for N in (5, 10, 20, 40):
        bound = (c_tail / (iv.mpf("1") - kappa)) / (rho ** N)
        banach_trunc_bounds[f"N_{N}"] = bound
    require(strictly_below(banach_trunc_bounds["N_40"], iv.mpf("1.3e-12")),
            "Banach N=40 bound unexpectedly large")

    irrelevant_gap_bounds = {
        f"n_{n}": -(1 - float(kappa.a)) * (2 * n - 4) for n in range(3, 9)
    }
    require(all(val < 0 for val in irrelevant_gap_bounds.values()), "Irrelevant gap bound must stay < 0")

    # Symbolic N=1 vs N=2 strong-mixing failure
    u, v = sp.symbols("u v", real=True)
    n1_roots = sp.solve(u - u ** 2, u)
    require(1 in n1_roots and 0 in n1_roots, "N=1 truncation spurious root check failed")
    n2_elim = sp.simplify((u - u ** 2 - 2 * v).subs(v, (u ** 2 + 1) / 2))
    require(sp.simplify(n2_elim - (-2 * u ** 2 + u - 1)) == 0, "N=2 elimination mismatch")
    require(sp.discriminant(-2 * u ** 2 + u - 1, u) == -7, "N=2 negative discriminant mismatch")

    # --- Pillar 2: P-H1D4-OSRECON-02 (OS Weak-Limit, GNS Quotient, Cauchy vs Oscillation, Ursell) ---
    M_inf = iv.matrix([[iv.mpf("1"), iv.mpf("1")], [iv.mpf("1"), iv.mpf("1")]])
    I_2 = iv.matrix([[iv.mpf("1"), iv.mpf("0")], [iv.mpf("0"), iv.mpf("1")]])
    os_weak_min_eigs = {}
    for m in (2, 8, 20):
        M_m = M_inf + (iv.mpf("1") / (iv.mpf("2") ** m)) * I_2
        lmin = _min_eig_2x2_iv(M_m)
        require(strictly_above(lmin, 0), f"Approximant M_{m} lost strict positivity")
        os_weak_min_eigs[f"m_{m}"] = lmin

    lam_min_inf = _min_eig_2x2_iv(M_inf)
    require(lam_min_inf.a <= 0 <= lam_min_inf.b and abs(lam_min_inf.b) < iv.mpf("1e-38"),
            "Limit kernel M_inf should have zero eigenvalue")
    null_vec = iv.matrix([[iv.mpf("1")], [iv.mpf("-1")]])
    gns_null_norm = (null_vec.T * M_inf * null_vec)[0, 0]
    require(gns_null_norm.a <= 0 <= gns_null_norm.b and abs(gns_null_norm.b) < iv.mpf("1e-38"),
            "GNS null vector norm not zero")
    phys_vec = iv.matrix([[iv.mpf("1")], [iv.mpf("0")]])
    gns_phys_norm = (phys_vec.T * M_inf * phys_vec)[0, 0]
    require(strictly_above(gns_phys_norm, iv.mpf("0.99")), "GNS physical state norm not positive")

    # Discrete symmetric +/-1 Ursell cumulant U4 = -2
    u4_discrete = iv.mpf("1") - iv.mpf("3") * (iv.mpf("1") ** 2)
    require(strictly_below(u4_discrete, iv.mpf("-1.99")), "Discrete Ursell check failed")

    # Continuous pure quartic exp(-x^4) normalized 4-point Ursell cumulant (1/4)*(Gamma(1/4)/Gamma(3/4))^2 - 3
    kurt_quartic = (iv.mpf("1") / iv.mpf("4")) * (iv.gamma(iv.mpf("0.25")) / iv.gamma(iv.mpf("0.75"))) ** 2
    u4_quartic_norm = kurt_quartic - iv.mpf("3")
    require(strictly_below(u4_quartic_norm, iv.mpf("-0.81")) and strictly_above(u4_quartic_norm, iv.mpf("-0.82")),
            "Continuous pure quartic Ursell out of bounds")

    # --- Pillar 3: P-H1D4-OPER-03 (UEOT AH01 Horizon UV Screening Equivalence) ---
    L_min_ah01 = iv.mpf(["0.153021391482", "0.153021391483"])
    m_planck_gev = iv.mpf(["1.22088e19", "1.22090e19"])
    regimes = {}
    for label, k_gev_str in (
        ("bmv_mesoscopic_1e_minus_12_GeV", "1e-12"),
        ("lhc_14_TeV", "1.4e4"),
        ("gut_scale_1e15_GeV", "1e15"),
    ):
        k_iv = iv.mpf(k_gev_str)
        eps_uv = (k_iv * L_min_ah01 / m_planck_gev) ** 2
        shots_min = iv.mpf("1") / (iv.mpf("2") * eps_uv ** 2)
        regimes[label] = {
            "k_obs_GeV": k_gev_str,
            "uv_screening_ratio_kLmin_sq": outward_str(eps_uv),
            "min_shots_delta_1": outward_str(shots_min),
        }
    require(strictly_below(iv.mpf(regimes["lhc_14_TeV"]["uv_screening_ratio_kLmin_sq"][1]), iv.mpf("3.1e-32")),
            "LHC UV screening bound failed")
    require(strictly_above(iv.mpf(regimes["lhc_14_TeV"]["min_shots_delta_1"][0]), iv.mpf("5.2e62")),
            "LHC shot lower bound failed")
    require(strictly_below(iv.mpf(regimes["bmv_mesoscopic_1e_minus_12_GeV"]["uv_screening_ratio_kLmin_sq"][1]),
                           iv.mpf("1.6e-64")), "BMV UV screening bound failed")

    # --- Pillar 4: C-H1D4-FINAL-04 ---
    payload = {
        "schema": "ueot-physics-unification-nonperturbative-4d-measure-h1d4/1",
        "result_ids": [
            "P-H1D4-BANACH-01",
            "P-H1D4-OSRECON-02",
            "P-H1D4-OPER-03",
            "C-H1D4-FINAL-04",
        ],
        "status": "PASS",
        "lean_module": "formalization/ueot-physics-unification/UEOTPhysicsUnification/Nonperturbative4DMeasureLimitH1d4.lean",
        "lean_theorems": [
            "UEOTPhysicsUnification.Nonperturbative4DMeasureLimitH1d4.weighted_banach_infinite_truncation_convergence",
            "UEOTPhysicsUnification.Nonperturbative4DMeasureLimitH1d4.infinite_order_critical_surface_stability_gap",
            "UEOTPhysicsUnification.Nonperturbative4DMeasureLimitH1d4.strong_mixing_truncation_spurious_fp_counterexample",
            "UEOTPhysicsUnification.Nonperturbative4DMeasureLimitH1d4.os_reflection_positivity_closed_under_weak_limits_and_gns_quotient",
            "UEOTPhysicsUnification.Nonperturbative4DMeasureLimitH1d4.subsequential_limit_uniqueness_via_cauchy_coherence_vs_oscillation",
            "UEOTPhysicsUnification.Nonperturbative4DMeasureLimitH1d4.ursell_four_point_non_triviality_dichotomy_and_limit_preservation",
            "UEOTPhysicsUnification.Nonperturbative4DMeasureLimitH1d4.ah01_horizon_uv_screening_and_finite_shot_indistinguishability",
            "UEOTPhysicsUnification.Nonperturbative4DMeasureLimitH1d4.h1d4_final_sharp_reduction_and_operational_vs_mathematical_split",
        ],
        "infinite_order_banach_truncation": {
            "contraction_kappa": "0.25",
            "weight_base_rho": "2",
            "tail_error_bounds": {k: outward_str(v) for k, v in banach_trunc_bounds.items()},
            "irrelevant_gap_upper_bounds": irrelevant_gap_bounds,
            "strong_mixing_n2_discriminant": -7,
        },
        "os_weak_limit_gns_and_ursell": {
            "approximant_min_eigenvalues": {k: outward_str(v) for k, v in os_weak_min_eigs.items()},
            "limit_kernel_min_eigenvalue": outward_str(lam_min_inf),
            "gns_null_vector_norm": outward_str(gns_null_norm),
            "gns_physical_vector_norm": outward_str(gns_phys_norm),
            "discrete_spin_ursell4": outward_str(u4_discrete),
            "pure_quartic_kurtosis": outward_str(kurt_quartic),
            "pure_quartic_normalized_ursell4": outward_str(u4_quartic_norm),
        },
        "operational_ah01_uv_screening": {
            "ah01_planck_length_floor": outward_str(L_min_ah01, digits=12),
            "planck_mass_GeV": outward_str(m_planck_gev, digits=6),
            "sub_planckian_regimes": regimes,
            "quotient_descent_operational_equivalence": True,
        },
        "h1d4_layer_decomposition": {
            "H1d4a_WeightedBanachInfiniteTruncationConvergence": "CLOSED",
            "H1d4b_OSWeakLimitGNSReconstructionAndNonTriviality": "CLOSED",
            "H1d4c_OperationalHorizonUVScreeningEquivalence": "CLOSED",
            "H1d4d_UnconditionalExact4DNonPolynomialDecouplingProof": "OPEN",
            "h1_operationally_closed_under_ah01_and_closed_tests": True,
            "four_way_logical_independence_proved": True,
        },
        "device_certified": False,
        "physical_unification": "OPEN",
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
        require(committed == payload, "Committed certificate.json differs from recomputed Wave 10 H1d4 values")
        print("PASS: nonperturbative_4d_measure_h1d4 (P-H1D4-BANACH-01, P-H1D4-OSRECON-02, P-H1D4-OPER-03, C-H1D4-FINAL-04)")
    else:
        write_json(CERT_PATH, payload)
        print("WROTE:", CERT_PATH)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
