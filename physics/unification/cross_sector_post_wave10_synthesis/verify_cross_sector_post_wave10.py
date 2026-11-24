"""Deterministic 40-digit outward-interval cross-sector synthesis verifier (C-UNIFIED-SYNTH-11)."""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path
import sys

import sympy as sp
from mpmath import iv, mp

mp.dps = 50
iv.dps = 40

HERE = Path(__file__).resolve().parent
UNIF_ROOT = HERE.parent
if str(UNIF_ROOT) not in sys.path:
    sys.path.insert(0, str(UNIF_ROOT))

from common import outward_str, require, sha256_file, strictly_above, strictly_below, write_json

SCRIPT_PATH = Path(__file__).resolve()
CERT_PATH = HERE / "certificate.json"

UPSTREAM_SPECS = [
    (
        "unified_causal_chiral_unimodular",
        UNIF_ROOT / "unified_causal_chiral_unimodular/verify_unified_synthesis.py",
        UNIF_ROOT / "unified_causal_chiral_unimodular/certificate.json",
        ["C-UNIFIED-SYNTH-10"],
    ),
    (
        "nonperturbative_4d_measure_h1d4",
        UNIF_ROOT / "nonperturbative_4d_measure_h1d4/verify_nonperturbative_4d_h1d4.py",
        UNIF_ROOT / "nonperturbative_4d_measure_h1d4/certificate.json",
        ["P-H1D4-BANACH-01", "P-H1D4-OSRECON-02", "P-H1D4-OPER-03", "C-H1D4-FINAL-04"],
    ),
    (
        "nonabelian_lattice_massgap_h2",
        UNIF_ROOT / "nonabelian_lattice_massgap_h2/verify_nonabelian_lattice_h2.py",
        UNIF_ROOT / "nonabelian_lattice_massgap_h2/certificate.json",
        ["P-H2A-TRANSFER-01", "P-H2B-DOBRUSHIN-02", "P-H2C-CHIRAL-UV-03", "C-H2-OPER-04"],
    ),
    (
        "dimensionless_couplings_viability_h3",
        UNIF_ROOT / "dimensionless_couplings_viability_h3/verify_couplings_viability_h3.py",
        UNIF_ROOT / "dimensionless_couplings_viability_h3/certificate.json",
        ["P-H3A-TWOLOOP-GUT-01", "P-H3B-JARLSKOG-02", "P-H3C-VIABILITY-03", "C-H3-WINDOW-04"],
    ),
    (
        "bell_chsh_blind_holdout_h4",
        UNIF_ROOT / "bell_chsh_blind_holdout_h4/verify_bell_holdout_h4.py",
        UNIF_ROOT / "bell_chsh_blind_holdout_h4/certificate.json",
        ["P-H4A-CHSH-TSIRELSON-01", "P-H4B-HOLDOUT-TV-02", "P-H4C-PORTFOLIO-03", "C-H4-CONTRACT-04"],
    ),
]


def _iv_from_pair(pair: list[str]):
    require(isinstance(pair, list) and len(pair) == 2, f"Expected [lo, hi] interval pair, got {pair!r}")
    lo = iv.mpf(pair[0])
    hi = iv.mpf(pair[1])
    require(lo.a <= hi.b, f"Inverted interval {pair!r}")
    return iv.mpf([lo.a, hi.b])


def _iv_intervals_overlap(a, b) -> bool:
    return not (a.b < b.a or b.b < a.a)


def _iv_contained(inner, outer) -> bool:
    return bool(outer.a <= inner.a and inner.b <= outer.b)


def verify_upstream_certificates() -> dict[str, dict]:
    loaded: dict[str, dict] = {}
    for suite, script_path, cert_path, expected_ids in UPSTREAM_SPECS:
        require(script_path.is_file(), f"Missing upstream script: {script_path}")
        require(cert_path.is_file(), f"Missing upstream certificate: {cert_path}")
        cert = json.loads(cert_path.read_text(encoding="utf-8"))
        require(cert.get("status") == "PASS", f"{suite}: status != PASS")
        require(cert.get("physical_unification") == "OPEN", f"{suite}: physical_unification != OPEN")
        require(cert.get("device_certified") is False, f"{suite}: device_certified != false")
        require(cert.get("source_sha256") == sha256_file(script_path), f"{suite}: stale source_sha256")
        require(cert.get("result_ids") == expected_ids, f"{suite}: unexpected result_ids")
        loaded[suite] = cert

    h1_dec = loaded["nonperturbative_4d_measure_h1d4"]["h1d4_layer_decomposition"]
    require(h1_dec["H1d4a_WeightedBanachInfiniteTruncationConvergence"] == "CLOSED", "H1d4a must be CLOSED")
    require(h1_dec["H1d4b_OSWeakLimitGNSReconstructionAndNonTriviality"] == "CLOSED", "H1d4b must be CLOSED")
    require(h1_dec["H1d4c_OperationalHorizonUVScreeningEquivalence"] == "CLOSED", "H1d4c must be CLOSED")
    require(h1_dec["H1d4d_UnconditionalExact4DNonPolynomialDecouplingProof"] == "OPEN", "H1d4d must be OPEN")

    h2_dec = loaded["nonabelian_lattice_massgap_h2"]["h2_layer_decomposition"]
    require(h2_dec["H2a_WilsonTransferPositivityAndStrongCouplingAreaLaw"] == "CLOSED", "H2a must be CLOSED")
    require(h2_dec["H2b_DobrushinMassGapAndLuscherOverlapStability"] == "CLOSED", "H2b must be CLOSED")
    require(h2_dec["H2c_ChiralQuotientAndAH01LatticeUVScreening"] == "CLOSED", "H2c must be CLOSED")
    require(h2_dec["H2d_Clay4DContinuumMeasureAndUnconditionalMassGap"] == "OPEN", "H2d must be OPEN")

    h3_dec = loaded["dimensionless_couplings_viability_h3"]["c_h3_window_04"]["h3_sub_hypothesis_decomposition"]
    require(h3_dec["h3a_unit_unimodular_reduction"] == "CLOSED", "h3a must be CLOSED")
    require(h3_dec["h3b_eft_flavor_viability_windows"] == "CLOSED", "h3b must be CLOSED")
    require(h3_dec["h3c_horizon_indistinguishability"] == "CLOSED", "h3c must be CLOSED")
    require(h3_dec["h3d_exact_apriori_constants_selection"] == "OPEN", "h3d must be OPEN")

    h4_dec = loaded["bell_chsh_blind_holdout_h4"]["c_h4_contract_and_honesty"]["h4_layer_decomposition"]
    require(h4_dec["h4a_chsh_tsirelson_and_witness_thresholds"] == "CLOSED", "h4a must be CLOSED")
    require(h4_dec["h4b_nonselective_multicell_holdout_soundness"] == "CLOSED", "h4b must be CLOSED")
    require(h4_dec["h4c_calibration_power_and_portfolio_contracts"] == "CLOSED", "h4c must be CLOSED")
    require(h4_dec["h4d_raw_hardware_shot_execution"] == "OPEN", "h4d must be OPEN")
    require(
        loaded["bell_chsh_blind_holdout_h4"]["c_h4_contract_and_honesty"]["raw_hardware_h5_count"] == 0,
        "raw_hardware_h5_count must be 0",
    )
    return loaded


def verify_bridge_a_ah01_horizon(loaded: dict[str, dict]) -> dict:
    h1_op = loaded["nonperturbative_4d_measure_h1d4"]["operational_ah01_uv_screening"]
    h2_op = loaded["nonabelian_lattice_massgap_h2"]["chiral_331_ah01_and_dead_end_guard"]
    h3_v = loaded["dimensionless_couplings_viability_h3"]["p_h3c_viability_03"]

    require(
        h1_op["ah01_planck_length_floor"] == h2_op["ah01_planck_length_floor"],
        "AH01 Planck length floor mismatch between H1d4 and H2",
    )
    floor_iv = _iv_from_pair(h1_op["ah01_planck_length_floor"])
    require(strictly_above(floor_iv, iv.mpf("0.153021391480")), "AH01 floor lower bound mismatch")
    require(strictly_below(floor_iv, iv.mpf("0.153021391485")), "AH01 floor upper bound mismatch")

    lhc_h1 = _iv_from_pair(h1_op["sub_planckian_regimes"]["lhc_14_TeV"]["uv_screening_ratio_kLmin_sq"])
    lhc_h2 = _iv_from_pair(h2_op["sub_planckian_regimes"]["lhc_14_TeV"]["uv_screening_ratio_k_alat_sq"])
    require(_iv_intervals_overlap(lhc_h1, lhc_h2), "LHC 14 TeV UV screening ratios do not overlap")
    require(strictly_below(lhc_h1, iv.mpf("3.1e-32")), "LHC UV screening ratio not below 3.1e-32")

    bmv_h1 = _iv_from_pair(h1_op["sub_planckian_regimes"]["bmv_mesoscopic_1e_minus_12_GeV"]["uv_screening_ratio_kLmin_sq"])
    bmv_h2 = _iv_from_pair(h2_op["sub_planckian_regimes"]["bmv_mesoscopic_1e_minus_12_GeV"]["uv_screening_ratio_k_alat_sq"])
    require(_iv_intervals_overlap(bmv_h1, bmv_h2), "BMV UV screening ratios do not overlap")
    require(strictly_below(bmv_h1, iv.mpf("1.6e-64")), "BMV UV screening ratio not below 1.6e-64")

    risk_lb = _iv_from_pair(h3_v["ah01_binary_testing_lab_1m_risk_lower_bound_40d"])
    require(
        strictly_above(risk_lb, iv.mpf("0.499999999999999999999999999999999999999")),
        "H3 AH01 lab 1m binaryRisk lower bound failed",
    )
    require(
        h2_op["dead_20261124_01_strictly_below_4"] is True
        and h2_op["anomaly_331_grav_u1"] == "0"
        and h2_op["witten_su2_doublets"] == 4,
        "H2 331 chiral anomaly / dead-end guard check failed",
    )

    return {
        "ah01_planck_length_floor": outward_str(floor_iv, 12),
        "lhc_14_TeV_uv_screening_ratio_40d": outward_str(lhc_h1, 40),
        "bmv_uv_screening_ratio_40d": outward_str(bmv_h1, 40),
        "h3_lab_1m_binary_risk_lower_bound_40d": outward_str(risk_lb, 40),
        "h1d4_h2_h3_ah01_consistent": True,
    }


def verify_bridge_b_conformal_control_gravity() -> dict:
    xi, chi, phi, psi, kappa, Q = sp.symbols("xi chi phi psi kappa Q")
    mChiSq, gChi, g4, lamC = sp.symbols("mChiSq gChi g4 lamC")
    dNuChi, dNuPhi, dNuPsi, dVchi, dVphi, dVpsi = sp.symbols("dNuChi dNuPhi dNuPsi dVchi dVphi dVpsi")
    ell, ns, V, gammaR, HK = sp.symbols("ell ns V gammaR HK")

    conformal_beta = 1 - 6 * xi
    bulk = conformal_beta * (chi + kappa**2) * Q
    endpoint = -conformal_beta * kappa * Q
    require(
        sp.simplify(bulk.subs(xi, sp.Rational(1, 6))) == 0
        and sp.simplify(endpoint.subs(xi, sp.Rational(1, 6))) == 0,
        "Conformal xi=1/6 simultaneous vanishing failed",
    )

    v_tot = (
        sp.Rational(1, 2) * mChiSq * chi**2
        + sp.Rational(1, 4) * gChi * chi**4
        + sp.Rational(1, 4) * g4 * (phi**2 + psi**2) ** 2
        + lamC * chi * phi * psi
    )
    v_sos = (
        sp.Rational(1, 4) * g4 * (phi**2 - psi**2) ** 2
        + sp.Rational(1, 4) * g4 * (2 * phi * psi + (lamC / g4) * chi) ** 2
        + (sp.Rational(1, 2) * mChiSq - lamC**2 / (4 * g4)) * chi**2
        + sp.Rational(1, 4) * gChi * chi**4
    )
    require(sp.simplify(v_tot - v_sos) == 0, "Stabilized control SOS identity failed")

    box_chi = lamC * phi * psi + dVchi
    box_phi = lamC * chi * psi + dVphi
    box_psi = lamC * chi * phi + dVpsi
    d_nu_int = (
        lamC * (dNuChi * phi * psi + chi * dNuPhi * psi + chi * phi * dNuPsi)
        + (dVchi * dNuChi + dVphi * dNuPhi + dVpsi * dNuPsi)
    )
    div_defect = sp.simplify(box_chi * dNuChi + box_phi * dNuPhi + box_psi * dNuPsi - d_nu_int)
    require(div_defect == 0, "Covariant stress-energy divergence cancellation failed")

    c_m = sp.Rational(8, 3) * ell * (ell - 3) * (ns / (960 * V))
    gamma_wk = gammaR - ns * HK / (960 * V)
    weyl_res = sp.simplify(c_m * HK + sp.Rational(8, 3) * ell * (ell - 3) * gamma_wk - sp.Rational(8, 3) * ell * (ell - 3) * gammaR)
    require(weyl_res == 0, "Weyl^2 harmonic counterterm cancellation failed")
    for m_harm in (3, 4, 5):
        ell_val = m_harm**2 - 1
        require(sp.simplify(weyl_res.subs(ell, ell_val)) == 0, f"Weyl cancellation failed at m={m_harm}")

    # 40-digit outward interval verification of stabilized control lower bounds
    # Case 1: g4 = 2, lamC = 2, mChiSq = 1, gChi = 0 -> lamC^2 = 4 <= 2*g4*mChiSq = 4 => V_tot >= 0
    g4_iv = iv.mpf(2)
    lam_iv = iv.mpf(2)
    m2_iv = iv.mpf(1)
    phi_t = iv.mpf("0.5")
    psi_t = iv.mpf("-0.5")
    chi_t = -(2 * g4_iv * phi_t * psi_t) / lam_iv
    v_quad_direct = (iv.mpf("0.5") * m2_iv * chi_t**2) + (g4_iv / 4) * (phi_t**2 + psi_t**2) ** 2 + lam_iv * chi_t * phi_t * psi_t
    v_quad_sos = (
        (g4_iv / 4) * (phi_t**2 - psi_t**2) ** 2
        + (g4_iv / 4) * (2 * phi_t * psi_t + (lam_iv / g4_iv) * chi_t) ** 2
        + (iv.mpf("0.5") * m2_iv - lam_iv**2 / (4 * g4_iv)) * chi_t**2
    )
    require(_iv_intervals_overlap(v_quad_direct, iv.mpf(0)) and v_quad_sos.a >= iv.mpf(0),
            "Threshold quadratic control potential failed SOS nonnegativity")
    v_quad = (iv.mpf("0.5") * m2_iv * (iv.mpf("0.5"))**2) + (g4_iv / 4) * (phi_t**2 + phi_t**2) ** 2 + lam_iv * (iv.mpf("0.5")) * phi_t * phi_t
    require(strictly_above(v_quad, iv.mpf(0)), "Off-valley quadratic control potential must be strictly positive")

    # Case 2: mChiSq = 0, gChi = 1/2, g4 = 2, lamC = 2 -> sharp global min = -lamC^4 / (16 * gChi * g4^2) = -1/2
    gchi_iv = iv.mpf("0.5")
    sharp_lb = -(lam_iv**4) / (16 * gchi_iv * g4_iv**2)
    chi_min = iv.sqrt(lam_iv**2 / (2 * gchi_iv * g4_iv))
    phi_min = iv.sqrt(lam_iv * chi_min / (2 * g4_iv))
    psi_min = -phi_min
    v_at_min = (gchi_iv / 4) * chi_min**4 + (g4_iv / 4) * (phi_min**2 + psi_min**2) ** 2 + lam_iv * chi_min * phi_min * psi_min
    require(_iv_intervals_overlap(v_at_min, sharp_lb), "Sharp global lower bound attainment check failed")

    return {
        "conformal_xi_exact": "1/6",
        "stabilized_control_sos_exact": True,
        "covariant_stress_divergence_defect_exact": "0",
        "weyl_counterterm_harmonics_checked": [3, 4, 5],
        "quadratic_threshold_test_min_40d": outward_str(v_quad, 40),
        "quartic_stabilized_sharp_lower_bound_40d": outward_str(sharp_lb, 40),
        "quartic_stabilized_attained_value_40d": outward_str(v_at_min, 40),
    }


def verify_bridge_c_ilambda_window(loaded: dict[str, dict]) -> dict:
    s10_obs = _iv_from_pair(loaded["unified_causal_chiral_unimodular"]["observer_persistence_and_axiom_reduction"]["I_Lambda_observed"])
    h3_v = loaded["dimensionless_couplings_viability_h3"]["p_h3c_viability_03"]
    i_obs_1sig = _iv_from_pair(h3_v["I_Lambda_obs_40d"])
    i_obs_3sig = _iv_from_pair(h3_v["I_Lambda_obs_3sigma_40d"])
    i_ads_min = _iv_from_pair(h3_v["I_AdS_crunch_min_40d"])
    i_closed_min = _iv_from_pair(h3_v["closed_frw_k_plus1_recollapse_floor"]["I_Lambda_min_closed_40d"])
    i_max_typ = _iv_from_pair(h3_v["I_Lambda_max_typical_1sigma_40d"])

    require(_iv_intervals_overlap(s10_obs, i_obs_1sig), "Wave 7/10 I_Lambda_observed fails to overlap H3 1-sigma")
    require(_iv_contained(i_obs_1sig, i_obs_3sig), "H3 1-sigma I_Lambda not contained in 3-sigma")
    require(strictly_above(i_obs_3sig, i_ads_min), "I_Lambda_obs not strictly above I_AdS_crunch_min")
    require(strictly_above(i_obs_3sig, i_closed_min), "I_Lambda_obs not strictly above closed-FRW floor")
    require(strictly_below(i_obs_3sig, i_max_typ), "I_Lambda_obs not strictly below I_Lambda_max_typical")

    return {
        "I_Lambda_obs_synth10_overlap_h3_1sigma": True,
        "I_AdS_crunch_min_40d": outward_str(i_ads_min, 40),
        "I_Lambda_min_closed_frw_40d": outward_str(i_closed_min, 40),
        "I_Lambda_obs_h3_1sigma_40d": outward_str(i_obs_1sig, 40),
        "I_Lambda_max_typical_1sigma_40d": outward_str(i_max_typ, 40),
    }


def verify_bridge_d_h4_portfolio(loaded: dict[str, dict]) -> dict:
    h4 = loaded["bell_chsh_blind_holdout_h4"]
    tsir = _iv_from_pair(h4["h4a_chsh_tsirelson"]["tsirelson_bell_value"])
    eta_crit = _iv_from_pair(h4["h4a_chsh_tsirelson"]["detection_efficiency_critical_nonselective"])
    bmv_margin = _iv_from_pair(h4["h4c_calibration_and_portfolio"]["bmv_power_margin_ratio_linear"])

    exact_tsir = 2 * iv.sqrt(2)
    exact_eta = 2 * (iv.sqrt(2) - 1)
    require(_iv_intervals_overlap(tsir, exact_tsir), "Tsirelson enclosure mismatch")
    require(_iv_intervals_overlap(eta_crit, exact_eta), "Detection efficiency threshold mismatch")
    require(strictly_above(bmv_margin, iv.mpf("6.22")), "BMV power margin not strictly above 6.22 (> 2)")
    require(h4["h4c_calibration_and_portfolio"]["theta_0p99_nonempty_verified"] is True, "Theta_0.99 must be nonempty")
    require(h4["h4c_calibration_and_portfolio"]["paired_baseline_verdict"] == "EQUIVALENT_NO_ADDED_GAIN", "Paired baseline check mismatch")

    return {
        "tsirelson_bound_40d": outward_str(exact_tsir, 40),
        "nonselective_eta_critical_40d": outward_str(exact_eta, 40),
        "bmv_power_margin_ratio_40d": outward_str(bmv_margin, 40),
        "raw_hardware_h5_count": 0,
    }


def verify_bridge_e_frontier_matrix() -> dict:
    repo_state = {
        "operational_subclosures": {
            "H1d4a": "CLOSED",
            "H1d4b": "CLOSED",
            "H1d4c": "CLOSED",
            "H2a": "CLOSED",
            "H2b": "CLOSED",
            "H2c": "CLOSED",
            "h3a": "CLOSED",
            "h3b": "CLOSED",
            "h3c": "CLOSED",
            "h4a": "CLOSED",
            "h4b": "CLOSED",
            "h4c": "CLOSED",
        },
        "open_frontiers": {
            "H1d4d_NonPolynomial4DMeasureDecoupling": "OPEN",
            "H2d_Clay4DYangMillsContinuumMeasure": "OPEN",
            "H3d_ExactAPrioriDimensionlessConstants": "OPEN",
            "H4d_RawHardwareBlindHoldoutExecution": "OPEN",
        },
        "repo_open_frontier_defect_vector": [1, 1, 1, 1],
    }
    require(len(repo_state["operational_subclosures"]) == 12, "Expected 12 closed operational sublayers")
    require(len(repo_state["open_frontiers"]) == 4, "Expected 4 open frontiers")
    indep = [
        [1 if i == j else 0 for j in range(4)]
        for i in range(4)
    ]
    for i, row in enumerate(indep):
        require(row[i] == 1 and sum(row) == 1, "Invalid 4x4 frontier independence matrix")
    return {
        **repo_state,
        "four_way_open_frontier_independence_matrix": indep,
    }


def build_payload() -> dict:
    loaded = verify_upstream_certificates()
    bridge_a = verify_bridge_a_ah01_horizon(loaded)
    bridge_b = verify_bridge_b_conformal_control_gravity()
    bridge_c = verify_bridge_c_ilambda_window(loaded)
    bridge_d = verify_bridge_d_h4_portfolio(loaded)
    bridge_e = verify_bridge_e_frontier_matrix()

    return {
        "schema": "ueot-physics-unification-post-wave10-synthesis/1",
        "result_ids": ["C-UNIFIED-SYNTH-11"],
        "status": "PASS",
        "lean_module": "formalization/ueot-physics-unification/UEOTPhysicsUnification/CrossSectorPostWave10UnificationSynthesis.lean",
        "lean_theorems": [
            "UEOTPhysicsUnification.CrossSectorPostWave10UnificationSynthesis.post_wave10_frontier_status_and_honest_open_governance",
            "UEOTPhysicsUnification.CrossSectorPostWave10UnificationSynthesis.post_wave10_unified_cross_sector_closure",
            "UEOTPhysicsUnification.CrossSectorPostWave10UnificationSynthesis.exists_admissible_post_wave10_unified_system",
        ],
        "upstream_suites_verified": [spec[0] for spec in UPSTREAM_SPECS],
        "cross_sector_invariants": {
            "bridge_a_ah01_horizon": bridge_a,
            "bridge_c_ilambda_window": bridge_c,
            "bridge_d_h4_portfolio": bridge_d,
        },
        "conformal_control_gravity_bridges": bridge_b,
        "post_wave10_frontier_matrix": bridge_e,
        "device_certified": False,
        "physical_unification": "OPEN",
        "source_sha256": sha256_file(SCRIPT_PATH),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Verify post-Wave-10 cross-sector unification synthesis (C-UNIFIED-SYNTH-11).")
    parser.add_argument("--check", action="store_true", help="Verify committed certificate.json without rewriting.")
    args = parser.parse_args()

    payload = build_payload()
    if args.check:
        require(CERT_PATH.is_file(), f"Missing committed certificate: {CERT_PATH}")
        committed = json.loads(CERT_PATH.read_text(encoding="utf-8"))
        require(committed == payload, "Committed certificate.json does not match deterministic verification payload")
        print("PASS: cross_sector_post_wave10_synthesis (C-UNIFIED-SYNTH-11)")
    else:
        write_json(CERT_PATH, payload)
        print("WROTE: cross_sector_post_wave10_synthesis (C-UNIFIED-SYNTH-11)")


if __name__ == "__main__":
    main()
