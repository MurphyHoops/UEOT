"""C-CORE-CONST-01 & P-GUT-DESERT-02 Certificate: Buckingham-Quotient Unit-Gauge Elimination & 1-Loop Gauge Unification Defect.

Verifies with exact integer linear algebra (sympy) and 40-digit outward interval arithmetic (mpmath.iv, iv.dps = 40):
1. C-CORE-CONST-01 (Read-Only Core v3 QuotientDescent & FisherGauge Unit-Gauge Elimination):
   - Exact integer (M, L, T) dimensional matrix M_Planck of (G, hbar, c) with det = 2 and integer adjugate
     M_Planck * adj_Planck = 2 * I_3 (even-parity sublattice index 2), exact unimodular factorization
     M_Planck = M_Planck_unimodular * B_even with det(M_Planck_unimodular) = -1 and explicit GL_3(Z) inverse,
     exact GL_4(Z) Buckingham monomial matrix U_Buckingham (det = 1), and 1D integer nullspace Z * (1, 1, -3, 1).
   - 40-digit outward-interval enclosure of CODATA-2022 + Planck-2018+BAO observed cosmological-Planck invariant
     I_Lambda^obs = G * hbar * Lambda_obs / c^3 in [2.8e-122, 3.0e-122] vs PR #468 RC05/RC12 sub-critical bounce
     model I_Lambda^model = G_model * Lambda_model ~ 3.93909e-82 (> 1.33e40 scale gap), plus explicit verification
     of the unique (R_{>0})^3 torsor gauge transformation (1/m_P, 1/l_P, 1/t_P) to Planck units (1, I_Lambda, 1, 1).
2. P-GUT-DESERT-02 (Exact 1-Loop (3,3,1) Gauge Unification Triangle & PDG-2024 Desert Exclusion):
   - Exact SU(5)-normalized (3/5) 1-loop (3,3,1) SM beta coefficients (b_1, b_2, b_3) = (41/10, -19/6, -7)
     and generation-independence of pairwise differences (b_1 - b_2, b_2 - b_3, b_3 - b_1) = (109/15, 23/6, -111/10).
   - 40-digit outward-interval enclosure of PDG-2024 MS-bar couplings at M_Z certifying scale-free collinearity
     defect Delta_123^obs in [-41.27, -40.10] (1-sigma) and < -38 (3-sigma), excluding naive single-step 1-loop
     minimal SM desert unification at > 83 sigma (>> 10 sigma), alongside Georgi-Quinn-Weinberg sin^2(theta_W)
     mismatch (~0.2076 vs 0.23129) and M_12 ~ 1.03e13 GeV proton-decay / M_23 ~ 9.9e16 GeV triangle splitting.
3. Updated Minimal Dimensionless Postulate Inventory (Core_v3_modified = False, physical_unification = "OPEN"):
   - Compresses AH11's 4 raw dimensional constants (G, Lambda, hbar, c) modulo 3 unit-gauge torsor degrees
     to 1 irreducible gravitational-vacuum invariant I_Lambda plus dimensionless EW/SM couplings, preserving full
     epistemic honesty that neither I_Lambda nor threshold scales are derived from read-only Core v3.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
import sympy as sp
from mpmath import iv

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

from physics.unification.common import (
    outward_str,
    require,
    sha256_file,
    strictly_above,
    strictly_below,
    write_json,
)

DIGITS = 40


def out40(x) -> list[str]:
    return outward_str(x, digits=DIGITS)


def finish(payload: dict, args: argparse.Namespace) -> None:
    if args.check:
        require(args.output.is_file(), f"Missing certificate file for --check: {args.output}")
        committed = json.loads(args.output.read_text())
        require(committed == payload, "core_dimensionless_constants certificate drift")
    else:
        write_json(args.output, payload)


def verify_buckingham_lattice_and_planck_invariant() -> dict:
    # 1. Exact integer dimensional matrices and unimodular factorizations over Z:
    m_planck = sp.Matrix([
        [-1, 3, -2],
        [1, 2, -1],
        [0, 1, -1],
    ])
    adj_planck = sp.Matrix([
        [-1, 1, 1],
        [1, 1, -3],
        [1, 1, -5],
    ])
    b_even = sp.Matrix([
        [1, 1, 0],
        [0, 2, 0],
        [0, 1, -1],
    ])
    m_unimod = sp.Matrix([
        [-1, 1, 2],
        [1, 0, 1],
        [0, 0, 1],
    ])
    m_unimod_inv = sp.Matrix([
        [0, 1, -1],
        [1, 1, -3],
        [0, 0, 1],
    ])
    dim_3x4 = sp.Matrix([
        [-1, 1, 0, 0],
        [3, 2, 1, -2],
        [-2, -1, -1, 0],
    ])
    u_buck = sp.Matrix([
        [1, 0, 0, 0],
        [0, 1, 0, 0],
        [0, 0, 1, 0],
        [1, 1, -3, 1],
    ])
    u_buck_inv = sp.Matrix([
        [1, 0, 0, 0],
        [0, 1, 0, 0],
        [0, 0, 1, 0],
        [-1, -1, 3, 1],
    ])

    require(m_planck.det() == 2, "M_Planck in raw (M,L,T) units must have det = 2")
    require(m_planck * adj_planck == 2 * sp.eye(3) and adj_planck * m_planck == 2 * sp.eye(3),
            "Exact integer adjugate identity M_Planck * adj_Planck = 2 I_3 failed")
    require(m_unimod * b_even == m_planck, "Parity-sublattice factorization M_Planck = M_unimod * B_even failed")
    require(m_unimod.det() == -1 and m_unimod * m_unimod_inv == sp.eye(3) and m_unimod_inv * m_unimod == sp.eye(3),
            "Unimodular GL_3(Z) inverse check failed")
    require(u_buck.det() == 1 and u_buck * u_buck_inv == sp.eye(4) and u_buck_inv * u_buck == sp.eye(4),
            "Unimodular GL_4(Z) Buckingham monomial inverse check failed")

    null_vecs = dim_3x4.nullspace()
    require(len(null_vecs) == 1 and null_vecs[0] == sp.Matrix([1, 1, -3, 1]),
            "3x4 dimensional matrix nullspace must be spanned uniquely by (1, 1, -3, 1)")

    # 2. 40-digit outward-interval CODATA-2022 + Planck-2018+BAO enclosure of I_Lambda^obs:
    c_si = iv.mpf("299792458")
    h_si = iv.mpf(662607015) / (iv.mpf(10) ** 42)
    hbar_si = h_si / (2 * iv.pi)
    g_si = iv.mpf(["6.67415e-11", "6.67445e-11"])  # CODATA-2022 6.67430(15)e-11 m^3 kg^-1 s^-2

    l_pl_sq = g_si * hbar_si / (c_si ** 3)
    l_pl = iv.sqrt(l_pl_sq)
    t_pl = l_pl / c_si
    m_pl = iv.sqrt(hbar_si * c_si / g_si)

    # Exact IAU 2012/2015 astronomical unit & megaparsec: 1 pc = (648000 / pi) * 149597870700 m
    au_m = iv.mpf("149597870700")
    mpc_m = iv.mpf("1000000") * (iv.mpf("648000") * au_m / iv.pi)

    # Planck-2018 TT,TE,EE+lowE+lensing+BAO (Aghanim et al., A&A 641, A6 (2020), Table 2):
    # H_0 = 67.66 +- 0.42 km s^-1 Mpc^-1, Omega_Lambda = 0.6889 +- 0.0056
    h0_si = iv.mpf(["67.24", "68.08"]) * iv.mpf("1000") / mpc_m
    omega_lam = iv.mpf(["0.6833", "0.6945"])
    lambda_obs_m2 = 3 * omega_lam * (h0_si ** 2) / (c_si ** 2)
    i_lambda_obs = g_si * hbar_si * lambda_obs_m2 / (c_si ** 3)

    require(strictly_above(i_lambda_obs, "2.8e-122") and strictly_below(i_lambda_obs, "3.0e-122"),
            "Observed I_Lambda^obs must lie strictly inside [2.8e-122, 3.0e-122]")

    # Verify explicit (R_{>0})^3 torsor gauge transformation (lam_M, lam_L, lam_T) = (1/m_P, 1/l_P, 1/t_P)
    # on a deterministic point G_mid inside CODATA-2022 to avoid interval dependency inflation:
    g_mid = iv.mpf("6.67430e-11")
    lam_mid = iv.mpf("1.1056e-52")
    s_len = iv.sqrt(c_si ** 3 / (g_mid * hbar_si))
    lam_l = s_len
    lam_t = s_len * c_si
    lam_m = c_si / (hbar_si * s_len)
    g_gauge = ((lam_l ** 3) / (lam_m * (lam_t ** 2))) * g_mid
    hbar_gauge = (lam_m * (lam_l ** 2) / lam_t) * hbar_si
    c_gauge = (lam_l / lam_t) * c_si
    lam_gauge = (1 / (lam_l ** 2)) * lam_mid
    i_mid = g_mid * hbar_si * lam_mid / (c_si ** 3)
    torsor_err = max(
        abs(g_gauge - 1).b,
        abs(hbar_gauge - 1).b,
        abs(c_gauge - 1).b,
        abs(lam_gauge - i_mid).b,
    )
    require(torsor_err < iv.mpf("1e-38").a, "Planck torsor gauge transformation residual too large")

    # 3. Comparison with RC05 / RC12 sub-critical closed-FRW bounce model:
    # alpha_G = 1/10, g = 1e-40 => G_model = 3 g^2 / (40 pi); lam_L = 550001/1000000 => Lambda_model = 3 lam_L
    g_rc = iv.mpf("1e-40")
    g_model = 3 * (g_rc ** 2) / (40 * iv.pi)
    lam_l_rc = iv.mpf("550001") / iv.mpf("1000000")
    lambda_model = 3 * lam_l_rc
    i_lambda_model = g_model * lambda_model

    # Cross-check unit-invariance against RC12 physical SI turnaround calibration R_S3 = l_P / sqrt(G_model):
    r_s3_m = l_pl / iv.sqrt(g_model)
    lambda_model_si = lambda_model / (r_s3_m ** 2)
    i_lambda_model_si = g_si * hbar_si * lambda_model_si / (c_si ** 3)
    require(iv.mpf("0") in (i_lambda_model_si - i_lambda_model),
            "Unit-rescaling invariance between RC05 dimensionless and RC12 SI units must contain 0")

    model_to_obs_ratio = i_lambda_model / i_lambda_obs
    log10_model_to_obs = iv.log(model_to_obs_ratio) / iv.log(iv.mpf("10"))
    require(strictly_above(log10_model_to_obs, "40.1"),
            "RC05/RC12 model I_Lambda must exceed observed cosmological I_Lambda by > 40 decades")

    # Required clock coupling g_cosmo to match observed I_Lambda^obs on the RC05 alpha_G=1/10 bounce branch:
    g_cosmo_required = iv.sqrt(40 * iv.pi * i_lambda_obs / (9 * lam_l_rc))
    require(strictly_above(g_cosmo_required, "8.4e-61") and strictly_below(g_cosmo_required, "8.7e-61"),
            "Cosmological bounce clock coupling enclosure outside expected [8.4e-61, 8.7e-61]")

    return {
        "m_planck_det_raw_MLT": 2,
        "m_planck_unimodular_det_parity_sublattice": -1,
        "u_buckingham_4x4_det": 1,
        "primitive_integer_nullvector_G_hbar_c_Lambda": [1, 1, -3, 1],
        "planck_length_m_40d": out40(l_pl),
        "planck_mass_kg_40d": out40(m_pl),
        "planck_time_s_40d": out40(t_pl),
        "lambda_obs_planck2018_bao_m_inv2_40d": out40(lambda_obs_m2),
        "I_Lambda_obs_codata2022_planck2018_40d": out40(i_lambda_obs),
        "I_Lambda_obs_strictly_in_2p8e_minus122_to_3p0e_minus122": True,
        "I_Lambda_model_RC05_RC12_40d": out40(i_lambda_model),
        "log10_I_Lambda_model_over_obs_40d": out40(log10_model_to_obs),
        "required_RC05_bounce_coupling_g_for_observed_Lambda_40d": out40(g_cosmo_required),
        "torsor_planck_gauge_max_residual_upper": "1e-38",
    }


def verify_pdg2024_one_loop_gauge_unification_defect() -> dict:
    # Exact rational 1-loop (3,3,1) SM beta coefficients in SU(5) 3/5 hypercharge normalization:
    b1_q = sp.Rational(41, 10)
    b2_q = sp.Rational(-19, 6)
    b3_q = sp.Rational(-7, 1)
    require((b2_q - b3_q, b3_q - b1_q, b1_q - b2_q) == (
        sp.Rational(23, 6),
        sp.Rational(-111, 10),
        sp.Rational(109, 15),
    ), "Exact rational pairwise SM 1-loop beta differences mismatch")
    require((b2_q - b3_q) * b1_q + (b3_q - b1_q) * b2_q + (b1_q - b2_q) * b3_q == 0,
            "Cyclic RG scale-invariance identity must vanish identically")

    b1 = iv.mpf("41") / iv.mpf("10")
    b2 = -iv.mpf("19") / iv.mpf("6")
    b3 = -iv.mpf("7")

    # PDG-2024 MS-bar electroweak & strong couplings at M_Z = 91.1880 +- 0.0020 GeV:
    # alpha_em^-1(M_Z) = 127.951 +- 0.009, sin^2(theta_W)(M_Z) = 0.23129 +- 0.00004, alpha_s(M_Z) = 0.1180 +- 0.0009
    mz_gev = iv.mpf(["91.1860", "91.1900"])
    a_em_inv_1s = iv.mpf(["127.942", "127.960"])
    s2w_1s = iv.mpf(["0.23125", "0.23133"])
    alpha_s_1s = iv.mpf(["0.1171", "0.1189"])

    a1_inv = (iv.mpf("3") / iv.mpf("5")) * (1 - s2w_1s) * a_em_inv_1s
    a2_inv = s2w_1s * a_em_inv_1s
    a3_inv = 1 / alpha_s_1s

    delta123_1s = (b2 - b3) * a1_inv + (b3 - b1) * a2_inv + (b1 - b2) * a3_inv

    # Verify exact agreement with Georgi-Quinn-Weinberg linear decomposition:
    delta123_gqw = (iv.mpf("23") / 10 - (iv.mpf("67") / 5) * s2w_1s) * a_em_inv_1s + (iv.mpf("109") / 15) * a3_inv
    require(iv.mpf("0") in (delta123_1s - delta123_gqw), "GQW decomposition identity mismatch")

    # Propagated 1-sigma uncertainty of Delta_123 across the 1-sigma box:
    d_daem = iv.mpf("23") / 10 - (iv.mpf("67") / 5) * s2w_1s
    d_ds2w = -(iv.mpf("67") / 5) * a_em_inv_1s
    d_das = -(iv.mpf("109") / 15) / (alpha_s_1s ** 2)
    sigma_delta123 = iv.sqrt(
        (d_daem * iv.mpf("0.009")) ** 2
        + (d_ds2w * iv.mpf("0.00004")) ** 2
        + (d_das * iv.mpf("0.0009")) ** 2
    )
    exclusion_sigma = abs(delta123_1s) / sigma_delta123

    require(strictly_below(delta123_1s, "-40.0") and strictly_above(delta123_1s, "-41.3"),
            "1-sigma Delta_123^obs outside [-41.3, -40.0]")
    require(strictly_above(exclusion_sigma, "80.0") and strictly_above(exclusion_sigma, "10.0"),
            "Minimal 1-loop SM desert unification must be excluded at > 80 sigma (>> 10 sigma)")

    # Full 3-sigma conservative hyper-rectangle check matching Lean theorem pdg2024_3sigma_excludes_sm_desert_unification:
    a_em_inv_3s = iv.mpf(["127.924", "127.978"])
    s2w_3s = iv.mpf(["0.23117", "0.23141"])
    alpha_s_3s = iv.mpf(["0.1153", "0.1207"])
    delta123_3s = (
        (iv.mpf("23") / 10 - (iv.mpf("67") / 5) * s2w_3s) * a_em_inv_3s
        + (iv.mpf("109") / 15) * (1 / alpha_s_3s)
    )
    require(strictly_below(delta123_3s, "-38.0"),
            "Full 3-sigma box Delta_123^obs must satisfy Delta_123 < -38 < 0")

    # Predicted 1-loop minimal SM desert sin^2(theta_W)(M_Z) and pairwise unification triangle scales:
    s2w_desert_pred = (iv.mpf("23") / 134) + (iv.mpf("109") / 201) * (a3_inv / a_em_inv_1s)
    require(strictly_above(s2w_desert_pred, "0.207") and strictly_below(s2w_desert_pred, "0.208"),
            "Predicted 1-loop minimal SM desert sin^2(theta_W) must lie in (0.207, 0.208)")

    t_12 = (a1_inv - a2_inv) / (b1 - b2)
    t_23 = (a2_inv - a3_inv) / (b2 - b3)
    m_12_gev = mz_gev * iv.exp(2 * iv.pi * t_12)
    m_23_gev = mz_gev * iv.exp(2 * iv.pi * t_23)
    log10_m23_over_m12 = (2 * iv.pi * (t_23 - t_12)) / iv.log(iv.mpf("10"))
    require(strictly_below(m_12_gev, "1.04e13") and strictly_above(m_23_gev, "8.7e16"),
            "Pairwise crossing scales M_12 and M_23 mismatch")
    require(strictly_above(log10_m23_over_m12, "3.92"),
            "Unification triangle scale gap log10(M_23 / M_12) must exceed 3.92 decades")

    return {
        "su5_hypercharge_normalization": "3/5",
        "one_loop_sm_betas_exact_rational": {"b1": "41/10", "b2": "-19/6", "b3": "-7"},
        "alpha1_inv_MZ_1sigma_40d": out40(a1_inv),
        "alpha2_inv_MZ_1sigma_40d": out40(a2_inv),
        "alpha3_inv_MZ_1sigma_40d": out40(a3_inv),
        "Delta_123_obs_1sigma_40d": out40(delta123_1s),
        "Delta_123_obs_3sigma_box_40d": out40(delta123_3s),
        "Delta_123_propagated_1sigma_uncertainty_40d": out40(sigma_delta123),
        "desert_exclusion_significance_sigma_40d": out40(exclusion_sigma),
        "desert_excluded_above_10_sigma": True,
        "predicted_1loop_desert_sin2_thetaW_MZ_40d": out40(s2w_desert_pred),
        "pairwise_crossing_M12_GeV_40d": out40(m_12_gev),
        "pairwise_crossing_M23_GeV_40d": out40(m_23_gev),
        "unification_triangle_log10_M23_over_M12_40d": out40(log10_m23_over_m12),
    }


def build_minimal_dimensionless_postulate_inventory() -> dict:
    inventory = {
        "C_CORE_DERIVED": [
            "quotient_descent_minimal_realization",
            "finite_quantitative_transport_chain_bound",
            "buckingham_unit_gauge_quotient_descent_and_fisher_zero_modes",
        ],
        "B_CONDITIONAL_BRIDGE": [
            "lieb_robinson_emergent_null_cone_to_minkowski_conformal_class",
            "gpt_self_dual_psd_cone_and_hurwitz_complex_selection",
            "squeezing_proof_operational_planck_sensor_floor",
            "planck_torsor_unit_calibration_eliminating_G_hbar_c_gauge_redundancy",
        ],
        "S_ANOMALY_OR_STABILITY_SELECTED": [
            "spacetime_dimension_D_eq_4",
            "conformal_scalar_coupling_xi_eq_1_over_6",
            "quartic_sos_vacuum_stability_and_gate_free_3d_dirac_closure",
            "su3c_su3l_u1x_anomaly_and_ir_asymptotic_freedom_selection",
            "su5_hypercharge_3_over_5_trace_equality_and_1loop_desert_collinearity_obstruction",
        ],
        "P_IRREDUCIBLE_PHYSICAL_POSTULATE": [
            "dimensionless_cosmological_planck_invariant_I_Lambda_and_sm_ew_couplings",
            "einstein_hilbert_weyl_squared_gravitational_action_dimensionless_couplings",
            "declared_relativistic_apparatus_and_matter_field_multiplet",
            "canonical_fock_hilbert_space_quantization",
        ],
        "X_OPEN_UNIFICATION_FRONTIER": [
            "nonperturbative_operator_quantum_einstein_geometry",
            "nonperturbative_4d_chiral_gauge_fermion_continuum_qft",
            "first_principles_origin_of_I_Lambda_and_intermediate_threshold_scales",
            "matched_protocol_quantum_hardware_blind_holdout_certification",
        ],
    }
    require(len(inventory["P_IRREDUCIBLE_PHYSICAL_POSTULATE"]) == 4, "Expected 4 irreducible postulate classes")
    require(len(inventory["X_OPEN_UNIFICATION_FRONTIER"]) == 4, "Expected 4 open frontier classes")
    return {
        "Core_v3_modified": False,
        "raw_gravitational_constants_count": 4,
        "eliminated_unit_gauge_degrees_G_hbar_c": 3,
        "remaining_irreducible_gravitational_vacuum_dimensionless_parameters": 1,
        "I_Lambda_derived_from_Core_v3": False,
        "premise_classification_inventory": inventory,
        "irreducible_postulate_class_count": len(inventory["P_IRREDUCIBLE_PHYSICAL_POSTULATE"]),
        "open_unification_frontier_count": len(inventory["X_OPEN_UNIFICATION_FRONTIER"]),
        "unification_claim_permitted": False,
    }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--write", action="store_true", help="Write deterministic 40-digit outward-interval certificate")
    ap.add_argument("--check", action="store_true", help="Verify existing certificate without modifying files")
    ap.add_argument("--output", type=Path, default=HERE / "certificate.json")
    args = ap.parse_args()
    require(not (args.write and args.check), "Cannot pass both --write and --check simultaneously")

    payload = {
        "schema": "ueot-physics-unification-suite-certificate/1",
        "result_ids": ["C-CORE-CONST-01", "P-GUT-DESERT-02"],
        "lean_module": (
            "formalization/ueot-physics-unification/UEOTPhysicsUnification/"
            "CoreUnitGaugeAndDimensionlessConstants.lean"
        ),
        "Core_v3_modified": False,
        "device_certified": False,
        "buckingham_unit_gauge_and_planck_invariant": verify_buckingham_lattice_and_planck_invariant(),
        "pdg2024_one_loop_gauge_unification_defect": verify_pdg2024_one_loop_gauge_unification_defect(),
        "minimal_dimensionless_postulate_inventory": build_minimal_dimensionless_postulate_inventory(),
        "physical_unification": "OPEN",
        "status": "PASS",
        "source_sha256": sha256_file(Path(__file__).resolve()),
    }
    finish(payload, args)
    print("PASS: core_dimensionless_constants (C-CORE-CONST-01, P-GUT-DESERT-02)")


if __name__ == "__main__":
    main()
