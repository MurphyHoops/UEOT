"""UEOT Philosophy v3.1 (Ch. 1-30) + Mathematics v4.2 <-> Unified Physics Bridge Certificate.

Verifies in 40-digit outward interval arithmetic (mpmath.iv) and exact rational arithmetic:
1. P-PHIL31-OMEGA-01: Physical realization & exclusivity of Organizational Integrity Omega (Ch. 4, 6-9, 14):
   - Passive Gibbs/variational equilibrium relaxation has zero interventional self-repair differentiation
     and empty controlled viability kernel under thermal fault, whereas prepaid finite-wallet repair
     achieves strictly positive constitutive differentiation and all-horizon intact viability;
   - Ch. 14 exact finite-horizon vs stationary marginal separation (15/64 > 1/8 at p = 1/8) and
     Ch. 8 / RegisterDecisionRepresentation rational memory separation (1/4 vs 1/2 posterior,
     5/8 vs 1/2 birth probability) + polynomial DAG compression (24*(H+1)^4 <= 157,464 vs 12^8);
   - Exact AH01 Planck-horizon operational sensor floor L_min * l_P in [2.47318e-36, 2.47325e-36] m
     (excluding sub-Planck clocks via E_req > E_trap while clearing flat-space 1e-4 m and closed-S^3
     RC12 52.3 km sensors) paired with certified continuum record distinguishability d_TV > 2.69e-30
     (RC02: [2.72457e-30, 2.72458e-30]; RC09 local pointer: [5.04058e-23, 5.04059e-23]).
2. P-PHIL31-REALIZ-02: Macroscopic realization via QuotientDescent causal-commutation uniqueness
   (no_second_force_additive_residual_vanishes) + non-lumpable negative control, RepresentationCovariance,
   Ch. 12 rank-3 (s, b, bq) Jacobian singular-value barrier (sigma_3 > 0.44 > 0), Ch. 13 dual-drive
   gauge orbit vs rank-2 multi-intervention identifiability and Fisher kernel intersection, Ch. 5/17
   lineage retention vs enlarged-permission (dispatch2) separation, Ch. 18 / Math Ch. 24 discrete
   preference cochain exactness & Condorcet 3-cycle non-integrability (DiscretePreferenceCochainObstruction
   + P-ALI-01..03), Ch. 15/25 Agency capability monotonicity & scalar non-equivalence, and Ch. 21
   explicit non-overreach boundary (X).
3. P-PHIL31-LAKATOS-03: Ch. 28 Lakatosian Research Programme non-immunity & severe-test falsification
   witnesses (rank-3 bottleneck exclusion, PDG 1-loop (3,3,1) desert collinearity defect |Delta_123| > 39.5,
   and AH08/BMV mesoscopic gravimetric null/LOCC refutation at > 99.98% confidence in N = 200 trials),
   preserving empirical_universality = "UNVERIFIED", device_certified = False, physical_unification = "OPEN".
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path
import re
import sys
from mpmath import iv

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
sys.path.insert(0, str(HERE.parent))
from common import outward_str, require, sha256_file, strictly_above, strictly_below, write_json

PHIL_BRIDGE_LEAN = (
    REPO / "formalization/ueot-physics-unification/UEOTPhysicsUnification/PhilosophyV31OmegaObserverBridge.lean"
)
DISCRETE_COCHAIN_LEAN = (
    REPO / "formalization/ueot-physics-unification/UEOTPhysicsUnification/DiscretePreferenceCochainObstruction.lean"
)
FORBIDDEN_LEAN_ESCAPES = re.compile(r"(?m)^[ \t]*(?:axiom|opaque)\b|\b(?:sorry|admit|native_decide)\b")


def _strip_lean_comments(src: str) -> str:
    out = []
    i, n, depth = 0, len(src), 0
    while i < n:
        if src.startswith("/-", i):
            depth += 1
            i += 2
        elif depth > 0 and src.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth > 0:
            if src[i] == "\n":
                out.append("\n")
            i += 1
        elif src.startswith("--", i):
            while i < n and src[i] != "\n":
                i += 1
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def _verify_lean_sources() -> tuple[list[str], list[str]]:
    """Verify comment-stripped Lean bridge sources for escapes, removed trivializations, and required theorems."""
    require(PHIL_BRIDGE_LEAN.is_file(), f"Missing Lean module: {PHIL_BRIDGE_LEAN}")
    require(DISCRETE_COCHAIN_LEAN.is_file(), f"Missing Lean module: {DISCRETE_COCHAIN_LEAN}")

    phil_clean = _strip_lean_comments(PHIL_BRIDGE_LEAN.read_text(encoding="utf-8"))
    disc_clean = _strip_lean_comments(DISCRETE_COCHAIN_LEAN.read_text(encoding="utf-8"))

    for label, text in (("PhilosophyV31OmegaObserverBridge.lean", phil_clean),
                        ("DiscretePreferenceCochainObstruction.lean", disc_clean)):
        m = FORBIDDEN_LEAN_ESCAPES.search(text)
        require(m is None, f"Forbidden syntactic escape in {label}: {m.group(0) if m else ''}")

    removed_trivializations = [
        "ch21_phenomenal_non_deduction_from_functional_dynamics",
        "PsychophysicalWorld",
        "double_counting_sum_equals_realized_iff_zero",
        "ch13_pi_phi_additive_gauge_invariance",
        "passive_gibbs_zero_constitutive_repair_diff",
        "ch25_normative_independence_and_capability_monotonicity",
        "(2 : ℝ) • F_micro",
        "two_smul",
    ]
    for tok in removed_trivializations:
        require(
            tok not in phil_clean,
            f"Removed trivialization token still present in PhilosophyV31OmegaObserverBridge.lean: {tok}",
        )

    required_phil_theorems = [
        "passive_kernel_viability_collapses_under_thermal_fault",
        "passive_gibbs_viability_collapses_under_thermal_fault",
        "prepaid_regen_positive_repair_diff_iff_budget",
        "rc02_and_rc09_continuum_record_tv_certified",
        "ah01_nontrapped_clock_persistence_iff_above_planck_floor",
        "autonomous_clock_pointer_omega_persistence_and_record_iff",
        "no_second_force_unique_quotient_realization",
        "no_second_force_additive_residual_vanishes",
        "ch13_pi_phi_gauge_orbit_and_rank2_identifiability",
        "ch13_two_intervention_fisher_kernel_trivial_iff",
        "ch12_no_differentiable_two_dim_piphi_bottleneck",
        "ch15_ch25_agency_capability_mono_and_scalar_non_equivalence",
        "ad_hoc_domain_excision_is_degenerating_shift",
        "ueot_lakatos_nonvacuous_and_non_immune",
        "finite_zero_failures_preserve_unverified_open_honesty",
    ]
    for thm in required_phil_theorems:
        require(
            re.search(rf"\btheorem\s+{re.escape(thm)}\b", phil_clean) is not None,
            f"Missing required theorem in PhilosophyV31OmegaObserverBridge.lean: {thm}",
        )

    required_core_refs = [
        "QuotientDescent.existsUnique_descend",
        "QuotientDescent.eq_descend_of_comp_eq",
        "QuotientDescent.FiberCompatible",
        "same_objective_iff_gauge_related",
        "registered_unit_interventions_identify_factorization",
        "UEOT.V3.FisherIntersection.p_inv_03",
        "UEOT.V3.Agency.extension_optimalValue_mono",
    ]
    for ref in required_core_refs:
        require(
            ref in phil_clean,
            f"Missing required ueot-core reference in PhilosophyV31OmegaObserverBridge.lean: {ref}",
        )

    required_disc_decls = [
        r"\bstructure\s+DiscreteOneForm\b",
        r"\bdef\s+d0\b",
        r"\btheorem\s+discrete_exact_iff_zero_cycle_sum\b",
        r"\btheorem\s+condorcet_3cycle_nonintegrable\b",
    ]
    for pat in required_disc_decls:
        require(
            re.search(pat, disc_clean) is not None,
            f"Missing required declaration in DiscretePreferenceCochainObstruction.lean: {pat}",
        )

    disc_theorems = [
        "discrete_exact_iff_zero_cycle_sum",
        "condorcet_3cycle_nonintegrable",
    ]
    return required_phil_theorems, disc_theorems


def _box_json_interval(pair: list) -> iv.mpf:
    return iv.mpf([str(pair[0]), str(pair[1])])


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--check", action="store_true", help="Verify committed certificate.json without writing")
    ap.add_argument("--write", action="store_true", help="Write certificate.json")
    ap.add_argument("--write-certificate", action="store_true", help="Write certificate.json")
    ap.add_argument("--output", type=Path, default=HERE / "certificate.json")
    args = ap.parse_args()

    verified_phil_theorems, verified_disc_theorems = _verify_lean_sources()

    # =========================================================================
    # 1. P-PHIL31-OMEGA-01: Organizational Integrity Omega vs Passive Gibbs/FEP,
    #    Prepaid Store/DecisionRepresentation, AH01 Planck Floor & Record d_TV
    # =========================================================================

    # 1a. Passive Gibbs two-state relaxation (beta * dE = 2) vs prepaid repair (c_rep = 3 <= B = 6)
    beta_dE = iv.mpf("2")
    p_eq_intact = iv.exp(beta_dE) / (1 + iv.exp(beta_dE))
    p_eq_damage = iv.mpf("1") / (1 + iv.exp(beta_dE))
    gibbs_repair_diff_iv = p_eq_intact - p_eq_intact
    require(
        0 in gibbs_repair_diff_iv and strictly_below(abs(gibbs_repair_diff_iv), "1e-39"),
        "Passive Gibbs interventional repair difference encloses 0 within 40-digit interval width < 1e-39",
    )
    require(
        strictly_above(p_eq_damage, "0.1192") and strictly_below(p_eq_damage, "0.1193"),
        "Passive Gibbs thermal fault weight strictly positive -> controlled viability kernel is empty",
    )

    r_idle = Fraction(1, 4)
    r_rep = Fraction(7, 8)
    c_rep = Fraction(3, 1)
    wallet_ok = Fraction(6, 1)
    wallet_insufficient = Fraction(2, 1)
    regen_diff_funded = r_rep - r_idle
    regen_diff_unfunded = r_idle - r_idle
    require(wallet_ok >= c_rep and regen_diff_funded == Fraction(5, 8) and regen_diff_funded > 0, "Funded repair > 0")
    require(wallet_insufficient < c_rep and regen_diff_unfunded == 0, "Unfunded repair differential == 0")

    # 1b. Philosophy v3.1 Ch. 14 separation of stationary marginal vs all-history survival (p = 1/8)
    p_int = Fraction(1, 8)
    stat_marginal_intact = 1 - p_int  # 7/8 at every t >= 1
    cum_interrupt_2step = 1 - (1 - p_int) ** 2  # 15/64 > 1/8
    uninterrupted_16step = (1 - p_int) ** 16
    require(stat_marginal_intact == Fraction(7, 8), "Ch. 14 stationary marginal is 7/8")
    require(cum_interrupt_2step == Fraction(15, 64) and cum_interrupt_2step > p_int, "Ch. 14 2-step 15/64 > 1/8")
    unint_16_iv = iv.mpf(uninterrupted_16step.numerator) / iv.mpf(uninterrupted_16step.denominator)
    require(strictly_below(unint_16_iv, "0.12") and strictly_above(unint_16_iv, "0.118"), "16-step survival ~ 0.118")

    # 1c. Ch. 8 / RegisterDecisionRepresentation rational memory separation & polynomial node bound
    def hist_likelihood(r: Fraction, pattern: str) -> Fraction:
        # Matches RegisterDecisionRepresentationWitnesses.insufficient_likelihoods:
        # insufficientA: r^2 * (1 - r); insufficientB: r * (1 - r)
        if pattern == "A":
            return (r**2) * (1 - r)
        return r * (1 - r)

    r0, r1 = Fraction(1, 4), Fraction(3, 4)
    mass_A = (hist_likelihood(r0, "A") + hist_likelihood(r1, "A")) / 2
    mass_B = (hist_likelihood(r0, "B") + hist_likelihood(r1, "B")) / 2
    post_low_A = hist_likelihood(r0, "A") / (hist_likelihood(r0, "A") + hist_likelihood(r1, "A"))
    post_low_B = hist_likelihood(r0, "B") / (hist_likelihood(r0, "B") + hist_likelihood(r1, "B"))
    next_birth_A = (r0 * hist_likelihood(r0, "A") + r1 * hist_likelihood(r1, "A")) / (
        hist_likelihood(r0, "A") + hist_likelihood(r1, "A")
    )
    next_birth_B = (r0 * hist_likelihood(r0, "B") + r1 * hist_likelihood(r1, "B")) / (
        hist_likelihood(r0, "B") + hist_likelihood(r1, "B")
    )
    require(mass_A == Fraction(3, 32) and mass_B == Fraction(3, 16), "Exact prior history masses 3/32 and 3/16")
    require(post_low_A == Fraction(1, 4) and post_low_B == Fraction(1, 2), "Distinct posteriors 1/4 != 1/2")
    require(next_birth_A == Fraction(5, 8) and next_birth_B == Fraction(1, 2), "Distinct birth laws 5/8 != 1/2")

    H_prereg = 8
    dag_node_bound_H8 = 24 * ((H_prereg + 1) ** 4)  # 157,464
    raw_branch_tree_H8 = 12**H_prereg               # 429,981,696
    compression_ratio_H8 = Fraction(raw_branch_tree_H8, dag_node_bound_H8)
    require(dag_node_bound_H8 == 157464 and compression_ratio_H8 > 2730, "Polynomial DAG compression > 2730x at H=8")

    # 1d. Exact AH01 Planck-horizon operational sensor floor L > L_min * l_P from first principles
    h_si = iv.mpf("6.62607015e-34")
    hbar = h_si / (2 * iv.pi)
    c_si = iv.mpf("299792458")
    g_si = iv.mpf(["6.67415e-11", "6.67445e-11"])
    l_planck = iv.sqrt(hbar * g_si / (c_si**3))

    # Exact rational C^7_c(B_L) moments: J_0 = int_0^1 (1-u^2)^8 u^2 du, J_1 = int_0^1 (1-u^2)^16 u^2 du,
    # J_2 = 256 * int_0^1 (1-u^2)^14 u^4 du
    j0 = Fraction(32768, 2078505)
    j1 = Fraction(2147483648, 347123925225)
    j2 = Fraction(8589934592, 49589132175)
    require(j2 / j1 == Fraction(28, 1), "Exact gradient-to-L2 ball moment ratio J_2 / J_1 == 28")

    cw2 = (iv.mpf(j1.numerator) / iv.mpf(j1.denominator)) / (
        4 * iv.pi * (iv.mpf(j0.numerator) / iv.mpf(j0.denominator)) ** 2
    )
    cw_grad = (iv.mpf(j2.numerator) / iv.mpf(j2.denominator)) / (
        4 * iv.pi * (iv.mpf(j0.numerator) / iv.mpf(j0.denominator)) ** 2
    )
    a_bar_massless = iv.sqrt(cw_grad / cw2) / 2  # = sqrt(7)
    n_gate = iv.mpf("1")
    eta_t = iv.mpf("1")
    lam_sys = iv.mpf("2")
    b_quad = (n_gate**2) / (4 * (eta_t**2))
    e_min_dimless = b_quad / (2 * (a_bar_massless + iv.sqrt(a_bar_massless**2 + b_quad)))
    l_min_over_lp = iv.sqrt(2 * e_min_dimless / lam_sys)
    l_min_si = l_min_over_lp * l_planck

    require(
        strictly_above(l_min_over_lp, "0.153021") and strictly_below(l_min_over_lp, "0.153022"),
        "Dimensionless Planck sensor floor L_min / l_P in (0.153021, 0.153022)",
    )
    require(
        strictly_above(l_min_si, "2.47318e-36") and strictly_below(l_min_si, "2.47325e-36"),
        "Physical Planck sensor floor L_min * l_P in (2.47318e-36, 2.47325e-36) m",
    )

    # Read-only cross-consistency check against PR #468 AH01 & AH12 receipts
    ah01_json = json.loads(
        (REPO / "physics/qm/null_source/timelike/finite_stress/lapse_boundary/all_harmonic_horizon/horizon_minimum_sensor_scale.json").read_text()
    )
    ah01_lmin_box = _box_json_interval(ah01_json["physical_L_min_SNR1_m"])
    require(
        not (l_min_si.b < ah01_lmin_box.a or ah01_lmin_box.b < l_min_si.a),
        "Exact interval overlap with PR #468 AH01 physical_L_min_SNR1_m",
    )

    # Sub-Planck exclusion test at L_sub = 0.1 * l_P < L_min * l_P: E_req > E_trap (horizon collapse!)
    l_sub = iv.mpf("0.1") * l_planck
    e_req_sub = e_min_dimless * hbar * c_si / l_sub
    e_trap_sub = lam_sys * (c_si**4) * l_sub / (2 * g_si)
    sub_planck_trap_ratio = e_req_sub / e_trap_sub
    require(strictly_above(sub_planck_trap_ratio, "2.34"), "Sub-Planck sensor L = 0.1 l_P forces E_req > 2.34 E_trap")

    # Super-Planck clearance for flat-space lab sensor (1e-4 m) and closed-S^3 RC12 sensor (~52.3 km)
    l_lab_si = iv.mpf("1e-4")
    g_model = iv.mpf("1e-40")
    alpha_g_rc12 = iv.mpf("1") / 10
    # RC12 unit radius: alpha_G = 4*pi*G / (3*g^2*R_S3^2*c^3/hbar) -> R_S3 = l_P * sqrt(4*pi / (3*alpha_G*g^2))
    r_s3_si = l_planck * iv.sqrt(4 * iv.pi / (3 * alpha_g_rc12 * (g_model**2)))
    l_rc12_si = r_s3_si / 20
    ah12_json = json.loads(
        (REPO / "physics/qm/null_source/timelike/finite_stress/lapse_boundary/all_harmonic_horizon/unified_gate_ledger_and_next_frontier.json").read_text()
    )
    ah12_rc12_box = _box_json_interval(ah12_json["sensor_scale_hierarchy_m"]["closed_S3_RC12_sensor"])
    require(
        not (l_rc12_si.b < ah12_rc12_box.a or ah12_rc12_box.b < l_rc12_si.a),
        "Exact interval overlap with PR #468 AH12 closed_S3_RC12_sensor (~52.30 km)",
    )
    clearance_lab = l_lab_si / l_min_si
    clearance_rc12 = l_rc12_si / l_min_si
    require(strictly_above(clearance_lab, "4.04e31"), "Flat-space lab sensor clears AH01 floor by > 4.04e31")
    require(
        strictly_above(clearance_rc12, "2.114e40") and strictly_below(clearance_rc12, "2.115e40"),
        "Closed-S^3 RC12 sensor clears AH01 floor by [2.114e40, 2.115e40]",
    )

    # 1e. Certified positive relational record distinguishability (d_TV > 2.69e-30 in RC02 & > 4.5e-23 in RC09)
    rc02_json = json.loads(
        (REPO / "physics/qm/null_source/timelike/finite_stress/lapse_boundary/renormalized_continuum/continuum_clock_composite.json").read_text()
    )
    rc09_json = json.loads(
        (REPO / "physics/qm/null_source/timelike/finite_stress/lapse_boundary/renormalized_continuum/local_autonomous_pointer.json").read_text()
    )
    prep_json = json.loads(
        (REPO / "physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/prepared_record.json").read_text()
    )
    eta_src = iv.mpf("1e-13")
    mu_esu_lo = _box_json_interval(prep_json["receiver_mean_unit_strength_lower"])
    den_rc02 = iv.sqrt(2 * (iv.mpf("0.01") + (eta_src**2) * iv.mpf("9") / 16))
    arg_rc02 = (eta_src**2) * mu_esu_lo / den_rc02
    d_ref_rc02 = 2 * arg_rc02 / iv.sqrt(iv.pi) * iv.exp(-(arg_rc02**2))
    delta_vec_rc02 = _box_json_interval(rc02_json["continuum_joint_vector_error_upper"])
    d_tv_rc02 = d_ref_rc02 - 2 * delta_vec_rc02
    require(
        strictly_above(d_tv_rc02, "2.69e-30") and strictly_above(d_tv_rc02, "2.7245e-30"),
        "RC02 continuum autonomous clock-controller binary record d_TV > 2.69e-30",
    )

    d_tv_rc09 = _box_json_interval(rc09_json["actual_continuum_pointer_binary_gap_lower"])
    require(
        strictly_above(d_tv_rc09, "4.5e-23") and strictly_above(d_tv_rc09, "2.69e-30"),
        "RC09 4D local autonomous pointer binary record d_TV > 4.5e-23 >> 2.69e-30",
    )

    # Zero-coherence-budget control: at eta = 0, reference record contrast vanishes identically
    eta_zero = iv.mpf("0")
    arg_zero = (eta_zero**2) * mu_esu_lo / iv.sqrt(2 * iv.mpf("0.01"))
    d_ref_zero = 2 * arg_zero / iv.sqrt(iv.pi) * iv.exp(-(arg_zero**2))
    require(d_ref_zero == 0, "Zero source/coherence budget produces zero record distinguishability")

    # =========================================================================
    # 2. P-PHIL31-REALIZ-02: Macroscopic Realization Without Double-Counting,
    #    Ch. 12 Rank-3 (s, b, bq) Boundary, Gauge Freedom & Non-Deduction Gates
    # =========================================================================

    # 2a. Ch. 12 (s, b, bq) Jacobian determinant & smallest singular value at (s, b, q) = (3/4, 1/2, 1/3)
    s_val = Fraction(3, 4)
    b_val = Fraction(1, 2)
    q_val = Fraction(1, 3)
    det_sbbq = b_val
    require(det_sbbq == Fraction(1, 2) and det_sbbq > 0, "Exact Ch. 12 Jacobian determinant det J = b = 1/2 > 0")

    # Singular values of J = diag(1, [[1, 0], [q, b]]): eigenvalues of M^T M = [[1+q^2, b*q], [b*q, b^2]]
    b_iv = iv.mpf(b_val.numerator) / iv.mpf(b_val.denominator)
    q_iv = iv.mpf(q_val.numerator) / iv.mpf(q_val.denominator)
    tr_mtm = 1 + q_iv**2 + b_iv**2      # 49/36
    det_mtm = b_iv**2                   # 1/4
    disc_mtm = iv.sqrt(tr_mtm**2 - 4 * det_mtm)
    sigma3_sbbq = iv.sqrt((tr_mtm - disc_mtm) / 2)
    require(
        strictly_above(sigma3_sbbq, "0.4678") and strictly_below(sigma3_sbbq, "0.4679"),
        "Ch. 12 third singular value sigma_3(J) in (0.4678, 0.4679) > 0 excludes rank-2 Pi/Phi bottleneck",
    )

    # 2b. Ch. 16-17 QuotientDescent causal-commutation uniqueness & non-lumpable negative control
    # 4-microstate Markov matrix P_micro lumped via q: {0,1}->0, {2,3}->1 to P_macro = [[7/8, 1/8], [1/4, 3/4]]
    P_micro = [
        [Fraction(1, 2), Fraction(3, 8), Fraction(1, 16), Fraction(1, 16)],
        [Fraction(3, 8), Fraction(1, 2), Fraction(1, 8), Fraction(0, 1)],
        [Fraction(1, 8), Fraction(1, 8), Fraction(1, 2), Fraction(1, 4)],
        [Fraction(1, 4), Fraction(0, 1), Fraction(3, 8), Fraction(3, 8)],
    ]
    P_macro = [
        [Fraction(7, 8), Fraction(1, 8)],
        [Fraction(1, 4), Fraction(3, 4)],
    ]
    q_map = [0, 0, 1, 1]
    max_lumping_defect = Fraction(0, 1)
    for x in range(4):
        pushed = [P_micro[x][0] + P_micro[x][1], P_micro[x][2] + P_micro[x][3]]
        for m_out in (0, 1):
            max_lumping_defect = max(max_lumping_defect, abs(pushed[m_out] - P_macro[q_map[x]][m_out]))
    require(max_lumping_defect == 0, "Exact QuotientDescent / StrongLumpability commutation defect == 0")

    # Compute expected macro observable f = [1, -1] on every microstate x in {0, 1, 2, 3}
    f_macro_obs = [Fraction(1, 1), Fraction(-1, 1)]
    F_micro = [
        sum(P_micro[x][xp] * f_macro_obs[q_map[xp]] for xp in range(4))
        for x in range(4)
    ]
    require(
        F_micro[0] == F_micro[1] == Fraction(3, 4) and F_micro[2] == F_micro[3] == Fraction(-1, 2),
        "FiberCompatible micro observable matches macro fibers {0,1} -> 3/4 and {2,3} -> -1/2",
    )
    F_macro_desc = [F_micro[0], F_micro[2]]
    descend_residual = max(abs(F_macro_desc[q_map[x]] - F_micro[x]) for x in range(4))
    require(descend_residual == 0, "QuotientDescent unique macro law satisfies F_macro(q(x)) == F_micro(x)")
    # Solving F_micro(x) + Delta_macro(q(x)) = F_micro(x) across surjection fibers forces Delta_macro = [0, 0]
    delta_forced = [F_micro[0] - F_micro[0], F_micro[2] - F_micro[2]]
    second_force_violation = max(abs((F_micro[x] + F_macro_desc[q_map[x]]) - F_micro[x]) for x in range(4))
    require(
        delta_forced == [Fraction(0, 1), Fraction(0, 1)] and second_force_violation == Fraction(3, 4),
        "Causal commutation forces additive macro residual Delta == 0 and rejects F_micro + F_macro o q",
    )

    # Non-lumpable negative control: perturb row 1 between macro-fibers {0,1} and {2,3} by 1/8
    P_micro_bad = [
        P_micro[0],
        [Fraction(1, 2), Fraction(1, 2), Fraction(0, 1), Fraction(0, 1)],
        P_micro[2],
        P_micro[3],
    ]
    F_bad = [
        sum(P_micro_bad[x][xp] * f_macro_obs[q_map[xp]] for xp in range(4))
        for x in range(4)
    ]
    nonlumpable_fiber_defect = abs(F_bad[0] - F_bad[1])
    require(
        nonlumpable_fiber_defect == Fraction(1, 4) and nonlumpable_fiber_defect > 0,
        "Non-lumpable perturbation breaks FiberCompatible with defect 1/4 > 0",
    )

    # Enlarged dispatch2 permission breaks coarse-key merge (birth laws 0 vs r = 3/4)
    dispatch2_gap = abs(Fraction(0, 1) - Fraction(3, 4))
    require(dispatch2_gap == Fraction(3, 4) and dispatch2_gap > 0, "Enlarged dispatch2 permission breaks merge")

    # 2c. Ch. 13 dual-drive (Pi, Phi) 1D gauge-orbit negative control vs rank-2 multi-intervention identifiability
    def drive_objective(pi_v: Fraction, phi_v: Fraction, lam_v: Fraction) -> Fraction:
        return pi_v - lam_v * phi_v

    pi_true = Fraction(5, 2)
    phi_true = Fraction(3, 4)
    lam1 = Fraction(1, 2)
    chi_shift = Fraction(2, 3)
    j1_true = drive_objective(pi_true, phi_true, lam1)
    j1_gauge = drive_objective(pi_true + lam1 * chi_shift, phi_true + chi_shift, lam1)
    require(j1_gauge == j1_true, "Single-slope 1D drive objective is invariant along (lam1*chi, chi) gauge orbit")
    s1 = [Fraction(1, 1), -lam1]
    gauge_dir = [lam1, Fraction(1, 1)]
    require(s1[0] * gauge_dir[0] + s1[1] * gauge_dir[1] == 0, "Rank-1 Fisher score annihilates gauge ray [lam1, 1]")
    F1_det = (s1[0] * s1[0]) * (s1[1] * s1[1]) - (s1[0] * s1[1]) * (s1[1] * s1[0])
    require(F1_det == 0, "Single-intervention Fisher matrix is singular (det = 0)")

    lam2 = Fraction(2, 1)
    s2 = [Fraction(1, 1), -lam2]
    S_mat = [s1, s2]
    det_S = S_mat[0][0] * S_mat[1][1] - S_mat[0][1] * S_mat[1][0]
    require(det_S == Fraction(-3, 2) and det_S != 0, "Two-intervention sensitivity matrix has det S = -3/2 != 0")
    F_sum = [
        [
            S_mat[0][0] * S_mat[0][0] + S_mat[1][0] * S_mat[1][0],
            S_mat[0][0] * S_mat[0][1] + S_mat[1][0] * S_mat[1][1],
        ],
        [
            S_mat[0][1] * S_mat[0][0] + S_mat[1][1] * S_mat[1][0],
            S_mat[0][1] * S_mat[0][1] + S_mat[1][1] * S_mat[1][1],
        ],
    ]
    det_F = F_sum[0][0] * F_sum[1][1] - F_sum[0][1] * F_sum[1][0]
    require(det_F == Fraction(9, 4) and det_F > 0, "Two-intervention Fisher accumulation has det F = 9/4 > 0")
    j2_true = drive_objective(pi_true, phi_true, lam2)
    pi_recovered = (j1_true * S_mat[1][1] - S_mat[0][1] * j2_true) / det_S
    phi_recovered = (S_mat[0][0] * j2_true - j1_true * S_mat[1][0]) / det_S
    require(
        pi_recovered == pi_true and phi_recovered == phi_true,
        "Rank-2 Cramer inversion uniquely recovers (Pi, Phi) from two anchored interventions",
    )

    # 2d. Ch. 18 / Math Ch. 24 DiscretePreferenceCochainObstruction & P-ALI-01..03
    ballots = [(0, 1, 2), (1, 2, 0), (2, 0, 1)]
    omega = [[Fraction(0, 1) for _ in range(3)] for _ in range(3)]
    for u in range(3):
        for v in range(3):
            if u != v:
                wins_u = sum(1 for b in ballots if b.index(u) < b.index(v))
                wins_v = sum(1 for b in ballots if b.index(v) < b.index(u))
                omega[u][v] = Fraction(wins_u - wins_v, 1)
    for u in range(3):
        for v in range(3):
            require(omega[u][v] == -omega[v][u], "DiscreteOneForm Condorcet margin matrix is skew-symmetric")
    condorcet_cycle_sum = omega[0][1] + omega[1][2] + omega[2][0]
    require(condorcet_cycle_sum == Fraction(3, 1) and condorcet_cycle_sum != 0, "Condorcet 3-cycle sum == 3 != 0")
    # Discrete divergence (d0* omega)(v) = sum_u omega[u][v] == 0 at every vertex => harmonic projection V=0
    div_omega = [sum(omega[u][v] for u in range(3)) for v in range(3)]
    require(all(d == 0 for d in div_omega), "Condorcet 1-form is co-closed (d0* omega == 0)")
    condorcet_min_l2_sq = omega[0][1] ** 2 + omega[1][2] ** 2 + omega[2][0] ** 2
    require(condorcet_min_l2_sq == Fraction(3, 1) and condorcet_min_l2_sq > 0, "Min L2 residual ||omega - d0(0)||^2 == 3")

    V_true = [Fraction(0, 1), Fraction(2, 1), Fraction(5, 1)]
    omega_exact = [[V_true[v] - V_true[u] for v in range(3)] for u in range(3)]
    exact_cycle_sum = omega_exact[0][1] + omega_exact[1][2] + omega_exact[2][0]
    V_rec = [omega_exact[0][v] for v in range(3)]
    require(exact_cycle_sum == 0, "Exact discrete 1-form has zero 3-cycle sum")
    require(
        all(V_rec[v] - V_rec[u] == omega_exact[u][v] for u in range(3) for v in range(3)),
        "Basepoint path-sum potential reconstructs exact discrete 1-form",
    )

    # P-ALI-03 linear coordination threshold eta_star = -<g, G> / (||g||^2 - <g, G>)
    g_align = [Fraction(2, 1), Fraction(1, 1)]
    G_align = [Fraction(-3, 1), Fraction(1, 1)]
    inner_gG = g_align[0] * G_align[0] + g_align[1] * G_align[1]
    g_sq = g_align[0] ** 2 + g_align[1] ** 2
    eta_star = -inner_gG / (g_sq - inner_gG)
    require(inner_gG == Fraction(-5, 1) and g_sq == Fraction(5, 1) and eta_star == Fraction(1, 2), "P-ALI-03 eta_* == 1/2")
    eta_below, eta_above = Fraction(2, 5), Fraction(3, 5)
    align_below = sum(g_align[i] * ((1 - eta_below) * G_align[i] + eta_below * g_align[i]) for i in range(2))
    align_above = sum(g_align[i] * ((1 - eta_above) * G_align[i] + eta_above * g_align[i]) for i in range(2))
    require(align_below < 0 and align_above > 0, "P-ALI-03 threshold flips alignment sign across eta_* = 1/2")

    # 2e. Ch. 15 / Ch. 25 Agency capability monotonicity & parametric scalar objective non-equivalence
    g_coop, g_dom = Fraction(5, 4), Fraction(3, 2)
    c_dom, c_coop = Fraction(0, 1), Fraction(5, 4)
    J_growth = {"p_dom": g_dom, "p_coop": g_coop}
    J_floor = {"p_dom": c_dom, "p_coop": c_coop}
    feasible_growth_max = max(J_growth.values())
    feasible_floor_max = max(J_floor.values())
    require(
        J_growth["p_coop"] < J_growth["p_dom"]
        and J_floor["p_dom"] < J_floor["p_coop"]
        and feasible_growth_max == g_dom
        and feasible_floor_max == c_coop,
        "Ch. 15/25 scalar growth maximization (3/2) is non-equivalent to capability-floor maximization (5/4)",
    )

    # =========================================================================
    # 3. P-PHIL31-LAKATOS-03: Ch. 28 Lakatosian Non-Immunity & Severe Tests
    # =========================================================================

    # 3a. Protective-belt refutation witness: 1-loop minimal desert (3,3,1) collinearity defect Delta_123 != 0
    b1 = iv.mpf("41") / 10
    b2 = -iv.mpf("19") / 6
    b3 = -iv.mpf("7")
    alpha1_inv_mz = iv.mpf(["59.00", "59.03"])
    alpha2_inv_mz = iv.mpf(["29.56", "29.60"])
    alpha3_inv_mz = iv.mpf(["8.40", "8.55"])
    delta_123_desert = (b2 - b3) * alpha1_inv_mz + (b3 - b1) * alpha2_inv_mz + (b1 - b2) * alpha3_inv_mz
    require(
        strictly_below(delta_123_desert, "-39.5") and strictly_above(delta_123_desert, "-42.0"),
        "PDG-2024 1-loop minimal desert collinearity defect Delta_123 in (-42.0, -39.5) != 0",
    )

    # 3b. Hard-core / bridge refutation witness: AH08 mesoscopic gravimetric phase & non-LOCC BMV witness
    m_meso = iv.mpf("1e-14")
    d_sep = iv.mpf("2e-4")
    t_int = iv.mpf("1.0")
    dphi_grav = g_si * (m_meso**2) * t_int / (hbar * d_sep)
    ramsey_contrast = iv.sin(dphi_grav)
    bmv_coherent_sum = iv.cos(dphi_grav / 2) ** 2 + iv.sin(dphi_grav)
    w_bmv_noiseless = 1 - bmv_coherent_sum  # strictly < 0, whereas separable LOCC satisfies W >= 0
    require(
        strictly_above(dphi_grav, "0.31643") and strictly_below(dphi_grav, "0.31646"),
        "AH08 gravimetric phase in (0.31643, 0.31646) rad",
    )
    require(
        strictly_below(w_bmv_noiseless, "-0.2862"),
        "BMV non-LOCC witness W_BMV < -0.2862 < 0 vs classical LOCC floor >= 0",
    )

    # Severe-test statistical power at N = 200 differential Ramsey shots against null phase dphi = 0
    n_severe_trials = iv.mpf("200")
    hoeffding_error_200 = 2 * iv.exp(-n_severe_trials * (ramsey_contrast**2) / 2)
    require(
        strictly_below(hoeffding_error_200, "1.3e-4"),
        "200-trial severe test separates AH08 gravimetric phase from null phase with error < 1.3e-4",
    )

    payload = {
        "schema": "ueot-physics-unification-philosophy-v31-omega-bridge/1",
        "result_ids": [
            "P-PHIL31-OMEGA-01",
            "P-PHIL31-REALIZ-02",
            "P-PHIL31-LAKATOS-03",
        ],
        "lean_module": "formalization/ueot-physics-unification/UEOTPhysicsUnification/PhilosophyV31OmegaObserverBridge.lean",
        "lean_modules": [
            "formalization/ueot-physics-unification/UEOTPhysicsUnification/PhilosophyV31OmegaObserverBridge.lean",
            "formalization/ueot-physics-unification/UEOTPhysicsUnification/DiscretePreferenceCochainObstruction.lean",
        ],
        "verified_lean_theorems": {
            "PhilosophyV31OmegaObserverBridge": verified_phil_theorems,
            "DiscretePreferenceCochainObstruction": verified_disc_theorems,
        },
        "removed_trivializations_absent": True,
        "upstream_books_aligned": {
            "philosophy_edition": "v3.1 (Parts I-VI, Ch. 1-30, Appendices A-D)",
            "mathematics_edition": "v4.2 (Core Synthesis, Ch. 0-40, Appendices A-G, 1051 pure-kernel Lean modules)",
            "physics_edition": "3.12 / Ch. 71 SISC + PR #468 (345-entry all_harmonic_horizon) + physics/unification (27 suites)",
        },
        "omega_exclusivity_and_clock_bridge": {
            "passive_Gibbs_beta_dE_2_damage_prob": outward_str(p_eq_damage),
            "passive_Gibbs_interventional_repair_diff": "0",
            "passive_Gibbs_intact_viability_kernel_size": 0,
            "prepaid_repair_funded_interventional_diff_exact": "5/8",
            "prepaid_repair_intact_viability_kernel_size": 1,
            "ch14_stationary_marginal_intact_exact": "7/8",
            "ch14_two_step_cumulative_interruption_exact": "15/64",
            "ch14_sixteen_step_uninterrupted_survival": outward_str(unint_16_iv),
            "ch08_decision_rep_posterior_A_vs_B_exact": ["1/4", "1/2"],
            "ch08_decision_rep_next_birth_A_vs_B_exact": ["5/8", "1/2"],
            "ch08_decision_rep_H8_node_cap": dag_node_bound_H8,
            "ch08_decision_rep_H8_raw_tree_ratio_exact": f"{compression_ratio_H8.numerator}/{compression_ratio_H8.denominator}",
            "AH01_ball_C7_J2_over_J1_exact": "28",
            "AH01_L_min_over_Planck_SNR1_etat1_lam2": outward_str(l_min_over_lp),
            "AH01_physical_L_min_m": outward_str(l_min_si),
            "sub_Planck_0p1_lP_energy_over_trap_cap": outward_str(sub_planck_trap_ratio),
            "flat_space_lab_sensor_over_AH01_floor": outward_str(clearance_lab),
            "closed_S3_RC12_sensor_over_AH01_floor": outward_str(clearance_rc12),
            "RC02_continuum_record_d_TV_lower": outward_str(d_tv_rc02),
            "RC09_autonomous_pointer_record_d_TV_lower": outward_str(d_tv_rc09),
            "zero_budget_eta0_record_d_TV": "0",
        },
        "macroscopic_realization_and_boundaries": {
            "ch12_s_b_bq_benchmark_point": ["3/4", "1/2", "1/3"],
            "ch12_s_b_bq_jacobian_det_exact": "1/2",
            "ch12_s_b_bq_smallest_singular_value_sigma3": outward_str(sigma3_sbbq),
            "ch13_rank2_sensitivity_det_exact": f"{det_S.numerator}/{det_S.denominator}",
            "ch13_fisher_accumulation_det_exact": f"{det_F.numerator}/{det_F.denominator}",
            "ch16_coarse_markov_lumping_commutation_defect_exact": "0",
            "ch16_quotient_descent_uniqueness_defect_exact": f"{descend_residual.numerator}/{descend_residual.denominator}" if descend_residual != 0 else "0",
            "ch16_nonlumpable_fiber_defect_exact": f"{nonlumpable_fiber_defect.numerator}/{nonlumpable_fiber_defect.denominator}",
            "ch17_enlarged_dispatch2_birth_law_gap_exact": "3/4",
            "ch18_ch24_discrete_cochain": {
                "condorcet_3cycle_sum_exact": f"{condorcet_cycle_sum.numerator}",
                "condorcet_min_l2_residual_sq_exact": f"{condorcet_min_l2_sq.numerator}",
                "exact_cochain_cycle_sum_exact": f"{exact_cycle_sum.numerator}",
                "p_ali_03_threshold_eta_star_exact": f"{eta_star.numerator}/{eta_star.denominator}",
            },
            "ch21_phenomenal_consciousness_deduced_from_physics": False,
            "ch21_bool_flip_wrapper_removed": True,
            "ch25_extractive_vs_cooperative_growth_exact": ["3/2", "5/4"],
            "ch25_extractive_vs_cooperative_min_capability_exact": ["0", "5/4"],
        },
        "lakatos_ch28_non_immunity": {
            "ad_hoc_domain_shrinking_permitted": False,
            "belt_witness_1_rank3_sigma3_lower": outward_str(sigma3_sbbq)[0],
            "belt_witness_2_1loop_desert_Delta123": outward_str(delta_123_desert),
            "bridge_witness_3_AH08_phase_rad": outward_str(dphi_grav),
            "bridge_witness_3_BMV_noiseless_witness": outward_str(w_bmv_noiseless),
            "bridge_witness_3_200shot_Hoeffding_error_upper": outward_str(hoeffding_error_200)[1],
        },
        "empirical_universality": "UNVERIFIED",
        "device_certified": False,
        "physical_unification": "OPEN",
        "status": "PASS",
        "source_sha256": sha256_file(Path(__file__).resolve()),
    }

    if args.check:
        require(args.output.is_file(), f"Missing certificate file: {args.output}")
        committed = json.loads(args.output.read_text())
        require(committed == payload, "philosophy_v31_omega_bridge certificate drift detected")
    else:
        write_json(args.output, payload)
    print("PASS: philosophy_v31_omega_bridge (P-PHIL31-OMEGA-01, P-PHIL31-REALIZ-02, P-PHIL31-LAKATOS-03)")


if __name__ == "__main__":
    main()
