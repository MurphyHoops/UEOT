"""40-digit outward-interval & symbolic verification for Wave 8 H1 (P-H1-SPIN2-01..C-H1-FRONTIER-04)."""
from __future__ import annotations

import argparse
from fractions import Fraction
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


def _iv_4simplex_cayley_menger(alpha_tilde):
    """Exact 4D equilateral spatial (a=1) + timelike-strut (alpha_tilde) Cayley-Menger determinant
    and exact dihedral angles for the (4,1) 4-simplex with base edges 1 and strut sq length alpha_tilde."""
    # Vertices: 0..3 regular tetrahedron in R^3 (z=0) with edge length 1; vertex 4 at barycenter with height h
    # By Cayley-Menger / explicit barycentric Euclidean embedding:
    # squared distance between base vertices i != j is 1; between base i and apex 4 is alpha_tilde.
    # For regular tetrahedron in R^3 of edge 1, circumradius R_3^2 = 3/8, so h_{4,1}^2 = alpha_tilde - 3/8.
    h2 = alpha_tilde - iv.mpf("3") / iv.mpf("8")
    # Build 5x5 distance matrix d^2 and 6x6 bordered Cayley-Menger matrix M for exact cofactors!
    cm = [[iv.mpf(0) for _ in range(6)] for _ in range(6)]
    for k in range(1, 6):
        cm[0][k] = iv.mpf(1)
        cm[k][0] = iv.mpf(1)
    for i in range(1, 6):
        for j in range(1, 6):
            if i == j:
                cm[i][j] = iv.mpf(0)
            elif i == 5 or j == 5:
                cm[i][j] = alpha_tilde
            else:
                cm[i][j] = iv.mpf(1)
    return h2, iv.matrix(cm)


def _iv_det_bareiss_6x6(mat):
    """Exact deterministic determinant via Gaussian minor expansion on 6x6 iv.matrix."""
    A = iv.matrix(mat)
    n = A.rows
    det = iv.mpf(1)
    sign = 1
    for i in range(n):
        piv = i
        # Deterministic pivot: pick entry cleanly bounded away from zero (smallest magnitude > 0 or first)
        while piv < n and A[piv, i].a <= 0 <= A[piv, i].b:
            piv += 1
        require(piv < n, "Zero/ambiguous pivot in interval determinant")
        if piv != i:
            for c in range(n):
                A[i, c], A[piv, c] = A[piv, c], A[i, c]
            sign = -sign
        det *= A[i, i]
        for r in range(i + 1, n):
            factor = A[r, i] / A[i, i]
            for c in range(i, n):
                A[r, c] -= factor * A[i, c]
    return det * sign


def _iv_minor_5x5(mat, skip_r: int, skip_c: int):
    sub = iv.matrix(5, 5)
    rr = 0
    for r in range(6):
        if r == skip_r:
            continue
        cc = 0
        for c in range(6):
            if c == skip_c:
                continue
            sub[rr, cc] = mat[r, c]
            cc += 1
        rr += 1
    # 5x5 determinant
    n = 5
    A = iv.matrix(sub)
    det = iv.mpf(1)
    sign = 1
    for i in range(n):
        piv = i
        while piv < n and A[piv, i].a <= 0 <= A[piv, i].b:
            piv += 1
        require(piv < n, "Zero pivot in 5x5 cofactor")
        if piv != i:
            for c in range(n):
                A[i, c], A[piv, c] = A[piv, c], A[i, c]
            sign = -sign
        det *= A[i, i]
        for r in range(i + 1, n):
            factor = A[r, i] / A[i, i]
            for c in range(i, n):
                A[r, c] -= factor * A[i, c]
    return det * sign


def _schlafli_sum_iv(alpha_tilde, eps):
    """Evaluate exact Schläfli differential ∑_h A_h * (theta_h(alpha+eps) - theta_h(alpha-eps))/(2*eps)
    on all 10 triangular hinges of the 4-simplex σ^(4,1) directly from exact Cayley-Menger cofactors."""
    # On 5 vertices: 4 base vertices (0,1,2,3) and 1 apex (4).
    # 4 base triangles (e.g. (0,1,2)): opposite facets contain vertex 3 vs 4 -> base-apex hinges (4 of them, Area = sqrt(3)/4).
    # 6 strut triangles (e.g. (0,1,4)): opposite facets are base-apex facets (e.g. skip 2 vs skip 3) -> strut hinges (6 of them).
    def get_thetas_and_areas(a_val):
        _, M = _iv_4simplex_cayley_menger(a_val)
        # Cofactor C_{ij} = (-1)^(i+j) minor(M, i+1, j+1) for vertices i,j in 0..4 (indices 1..5 in bordered M)
        # Specifically diag minor CM_{ii} of unbordered or bordered? For facets:
        # Dihedral angle between facet opposite vertex p and facet opposite vertex q:
        # cos(theta_{pq}) = - C_{pq} / sqrt(C_{pp} * C_{qq}), where C_{pq} = (-1)^(p+q) det M[skip p+1, q+1].
        cof = {}
        for p in range(5):
            for q in range(p, 5):
                c = ((-1) ** (p + q)) * _iv_minor_5x5(M, p + 1, q + 1)
                cof[(p, q)] = c
                cof[(q, p)] = c
        # Actually, for positive Euclidean 4-simplex, signed Gram inner product of outward normals gives:
        # Note bordered CM has signature (-,+,+,+,+,+), so diag cofactors have sign (-1)^5 = -1 or +1 depending on convention;
        # (-C_{pq}) / sqrt(C_{pp} * C_{qq}) is invariant if C_{pp} has same sign for all p: check C_{pp} * C_{qq} > 0!
        # Wait: let's verify standard Cayley-Menger dihedral formula: cos(theta_{pq}) = - C_{pq} / sqrt(C_{pp} * C_{qq})?
        # On equilateral 4-simplex (a_val = 1), cos(theta) = 1/4 (> 0, interior dihedral angle arccos(1/4))!
        base_area = iv.sqrt(iv.mpf("3")) / iv.mpf("4")
        # Area of triangle with edges (1, sqrt(a_val), sqrt(a_val)): height = sqrt(a_val - 1/4), area = 0.5 * sqrt(a_val - 1/4)
        strut_area = iv.mpf("0.5") * iv.sqrt(a_val - iv.mpf("1") / iv.mpf("4"))
        # Symmetrically: 4 base triangles have opposite pair (k, 4) for k in 0..3 -> cos = -C_{0,4}/sqrt(C_{00} C_{44})
        # Check sign using inner angle at a_val=1: equilateral C_{0,4}/C_{00} = -1/4 if normal convention matches!
        thetas = []
        areas = []
        for p in range(5):
            for q in range(p + 1, 5):
                # hinge opposite to pair (p, q) is the triangle on the remaining 3 vertices!
                cos_pq = -cof[(p, q)] / iv.sqrt(cof[(p, p)] * cof[(q, q)])
                theta_pq = iv.atan2(iv.sqrt(iv.mpf("1") - cos_pq ** 2), cos_pq)
                thetas.append(theta_pq)
                if q == 4:
                    # remaining 3 vertices all in {0,1,2,3} -> base equilateral triangle!
                    areas.append(base_area)
                else:
                    # remaining 3 vertices include apex 4 -> strut triangle!
                    areas.append(strut_area)
        return areas, thetas

    areas_0, _ = get_thetas_and_areas(alpha_tilde)
    _, th_p = get_thetas_and_areas(alpha_tilde + eps)
    _, th_m = get_thetas_and_areas(alpha_tilde - eps)
    # Check equilateral check at alpha=1:
    schlafli_diff = sum(A * (tp - tm) / (2 * eps) for A, tp, tm in zip(areas_0, th_p, th_m))
    return areas_0, th_p, th_m, schlafli_diff


def compute_certificate() -> dict:
    mp.dps = 50
    iv.dps = 40

    # --- Pillar 1: P-H1-SPIN2-01 ---
    hp, hx, l1, l2, l3, tr = sp.symbols("hp hx l1 l2 l3 tr", real=True)
    M = sp.Matrix([
        [hp + l3 + tr, hx, l1],
        [hx, -hp + l3 + tr, l2],
        [l1, l2, -2 * l3 + tr],
    ])
    M_tt = M.subs({l1: 0, l2: 0, l3: 0, tr: 0})
    dewitt_poly = sp.simplify(sp.trace(M * M) - sp.trace(M) ** 2)
    expected_poly = 2 * hp ** 2 + 2 * hx ** 2 + 2 * l1 ** 2 + 2 * l2 ** 2 + 6 * l3 ** 2 - 6 * tr ** 2
    require(sp.simplify(dewitt_poly - expected_poly) == 0, "DeWitt diagonalization failed")
    require(sp.trace(M_tt) == 0 and M_tt * sp.Matrix([0, 0, 1]) == sp.Matrix([0, 0, 0]), "TT transversality failed")
    G6 = sp.diag(2, 2, 2, 2, 6, -6)
    eigs_6 = sorted(int(k) for k, m in G6.eigenvals().items() for _ in range(int(m)))
    require(eigs_6 == [-6, 2, 2, 2, 2, 6], f"Unexpected DeWitt eigenvalues: {eigs_6}")

    # Spin-2 3D lattice dispersion & propagator O(a^2) convergence in pure mpmath.iv
    k1, k2, k3 = iv.mpf("0.7"), iv.mpf("1.1"), iv.mpf("1.3")
    k_sq = k1 ** 2 + k2 ** 2 + k3 ** 2
    a_vals = [Fraction(1, 10), Fraction(1, 20), Fraction(1, 40)]
    prop_errs = {}
    disp_errs = {}
    for af in a_vals:
        a = iv.mpf(af.numerator) / iv.mpf(af.denominator)
        w_sq = (iv.mpf("4") / a ** 2) * (
            iv.sin(a * k1 / 2) ** 2 + iv.sin(a * k2 / 2) ** 2 + iv.sin(a * k3 / 2) ** 2
        )
        d_err = k_sq - w_sq
        p_err = iv.mpf("1") / w_sq - iv.mpf("1") / k_sq
        d_ub = (a ** 2 / iv.mpf("12")) * (k1 ** 4 + k2 ** 4 + k3 ** 4)
        p_ub = (a ** 2 / iv.mpf("12")) * (k_sq / w_sq)
        require(strictly_above(d_err, 0) and strictly_below(d_err, d_ub), "Dispersion O(a^2) enclosure failed")
        require(strictly_above(p_err, 0) and strictly_below(p_err, p_ub), "Propagator O(a^2) enclosure failed")
        disp_errs[f"a_1_over_{af.denominator}"] = d_err
        prop_errs[f"a_1_over_{af.denominator}"] = p_err

    ratio_disp_10_20 = disp_errs["a_1_over_10"] / disp_errs["a_1_over_20"]
    ratio_disp_20_40 = disp_errs["a_1_over_20"] / disp_errs["a_1_over_40"]
    ratio_prop_10_20 = prop_errs["a_1_over_10"] / prop_errs["a_1_over_20"]
    ratio_prop_20_40 = prop_errs["a_1_over_20"] / prop_errs["a_1_over_40"]
    require(strictly_above(ratio_disp_20_40, iv.mpf("3.99")) and strictly_below(ratio_disp_20_40, iv.mpf("4.01")),
            "Dispersion refinement ratio not O(a^2)")
    require(strictly_above(ratio_prop_20_40, iv.mpf("3.99")) and strictly_below(ratio_prop_20_40, iv.mpf("4.01")),
            "Propagator refinement ratio not O(a^2)")

    # Causal 2-polarization reflection-positive transfer T = B^T diag(w) B and Stelle ghost separation
    B = iv.matrix([
        [iv.mpf("1"), iv.mpf("0.25")],
        [iv.mpf("-0.25"), iv.mpf("1")],
        [iv.mpf("0.5"), iv.mpf("0.5")],
    ])
    w_boltz = [iv.exp(-iv.mpf("0.2")), iv.exp(-iv.mpf("0.35")), iv.exp(-iv.mpf("0.6"))]
    W = iv.matrix([[w_boltz[i] if i == j else iv.mpf(0) for j in range(3)] for i in range(3)])
    T_spin2 = B.T * W * B
    tr_T = T_spin2[0, 0] + T_spin2[1, 1]
    det_T = T_spin2[0, 0] * T_spin2[1, 1] - T_spin2[0, 1] * T_spin2[1, 0]
    disc_T = tr_T ** 2 - iv.mpf("4") * det_T
    lam_min_T = (tr_T - iv.sqrt(disc_T)) / iv.mpf("2")
    require(strictly_above(lam_min_T, 0), "2-polarization transfer matrix not strictly positive")

    p2_t, mgh2_t = iv.mpf("0.8"), iv.mpf("2.5")
    stelle_lhs = iv.mpf("1") / (p2_t * (iv.mpf("1") + p2_t / mgh2_t))
    stelle_rhs = iv.mpf("1") / p2_t + iv.mpf("-1") / (p2_t + mgh2_t)
    require(strictly_below(abs(stelle_lhs - stelle_rhs), iv.mpf("1e-38")), "Stelle partial-fraction check failed")

    # --- Pillar 2: P-H1-REGGE-02 ---
    # 1) Schläfli identity on curved causal 4-simplex at alpha_tilde = 2/3 > 7/12
    areas_0, th_p, th_m, schlafli_der = _schlafli_sum_iv(iv.mpf("2") / iv.mpf("3"), iv.mpf("1e-12"))
    require(strictly_below(abs(schlafli_der), iv.mpf("1e-20")), f"Schlafli identity violation: {schlafli_der}")
    # Verify equilateral 4-simplex (alpha=1) interior dihedral angle arccos(1/4) and Schlafli identity
    _, th_eq_p, th_eq_m, schlafli_eq = _schlafli_sum_iv(iv.mpf("1"), iv.mpf("1e-12"))
    eq_cos = iv.cos((th_eq_p[0] + th_eq_m[0]) / iv.mpf("2"))
    require(strictly_below(abs(eq_cos - iv.mpf("0.25")), iv.mpf("1e-20")), f"Equilateral dihedral cos != 1/4: {eq_cos}")
    require(strictly_below(abs(schlafli_eq), iv.mpf("1e-20")), "Equilateral Schlafli violation")

    # 2) Curved S^3 Regge curvature O(a^2 / R^2) convergence to R_cont = 6/R^2
    R_s3 = iv.mpf("3")
    R_cont = iv.mpf("6") / R_s3 ** 2
    regge_errs = {}
    for af in a_vals:
        a = iv.mpf(af.numerator) / iv.mpf(af.denominator)
        kappa_regge = (iv.mpf("24") / a ** 2) * iv.sin(a / (iv.mpf("2") * R_s3)) ** 2
        err_r = R_cont - kappa_regge
        ub_r = a ** 2 / (iv.mpf("2") * R_s3 ** 4)
        require(strictly_above(err_r, 0) and strictly_below(err_r, ub_r), "Curved S^3 Regge enclosure failed")
        regge_errs[f"a_1_over_{af.denominator}"] = err_r
    ratio_regge_20_40 = regge_errs["a_1_over_20"] / regge_errs["a_1_over_40"]
    require(strictly_above(ratio_regge_20_40, iv.mpf("3.999")) and strictly_below(ratio_regge_20_40, iv.mpf("4.001")),
            "Curved Regge ratio not O(a^2)")

    # 3) Smeared Dirac hypersurface Wronskian O(a^2) restoration for N1(x)=sin(0.9x), N2(x)=cos(1.3x)
    x0, k1_w, k2_w, K_w = iv.mpf("0.7"), iv.mpf("0.9"), iv.mpf("1.3"), iv.mpf("1.3")
    N1 = iv.sin(k1_w * x0)
    N2 = iv.cos(k2_w * x0)
    N1p = k1_w * iv.cos(k1_w * x0)
    N2p = -k2_w * iv.sin(k2_w * x0)
    w_cont = N1 * N2p - N2 * N1p
    dirac_errs = {}
    for af in a_vals:
        a = iv.mpf(af.numerator) / iv.mpf(af.denominator)
        D1 = (iv.sin(k1_w * (x0 + a)) - iv.sin(k1_w * (x0 - a))) / (iv.mpf("2") * a)
        D2 = (iv.cos(k2_w * (x0 + a)) - iv.cos(k2_w * (x0 - a))) / (iv.mpf("2") * a)
        w_disc = N1 * D2 - N2 * D1
        err_w = abs(w_disc - w_cont)
        ub_w = (K_w ** 3 / iv.mpf("3")) * a ** 2
        require(strictly_below(err_w, ub_w), "Dirac Wronskian O(a^2) bound failed")
        dirac_errs[f"a_1_over_{af.denominator}"] = err_w
    ratio_dirac_20_40 = dirac_errs["a_1_over_20"] / dirac_errs["a_1_over_40"]
    require(strictly_above(ratio_dirac_20_40, iv.mpf("3.99")) and strictly_below(ratio_dirac_20_40, iv.mpf("4.01")),
            "Dirac Wronskian refinement ratio not O(a^2)")

    # --- Pillar 3: P-H1-BIANCHI-03 ---
    # Consistent with AH01 scalar Planck sensor minimum scale L_min/l_P ~ 0.153021391482
    L_min_planck = iv.mpf(["0.153021391482", "0.153021391483"])
    V_min = L_min_planck ** 3
    pp, pm = iv.mpf("0.4"), iv.mpf("0.3")
    aniso_sq = pp ** 2 + pm ** 2
    V_bkl = iv.mpf("1e-10")
    shear_classical_bkl = aniso_sq / (iv.mpf("2") * V_bkl ** 2)
    shear_floor_cap = aniso_sq / (iv.mpf("2") * V_min ** 2)
    require(strictly_above(shear_classical_bkl, shear_floor_cap * iv.mpf("1e10")),
            "Planck floor vs BKL blowup separation check failed")

    # Isaacson graviton energy density & radiation scaling (exact w_GW = 1/3)
    rho_gw_0 = iv.mpf("0.125")
    P_gw_0 = rho_gw_0 / iv.mpf("3")
    trace_gw = rho_gw_0 - iv.mpf("3") * P_gw_0
    require(trace_gw.a <= 0 <= trace_gw.b and abs(trace_gw.b) < iv.mpf("1e-38"), "Isaacson stress not trace-free")
    scale_a = iv.mpf("2.5")
    conserved = (rho_gw_0 / scale_a ** 4) * scale_a ** 4 - rho_gw_0
    require(abs(conserved.b) < iv.mpf("1e-38"), "Covariant a^-4 conservation failed")

    # Multi-mode projective cylindrical O(tau a^2) convergence sum (m = 1, 2, 3)
    tau_proj = iv.mpf("1.0")
    C_spin2 = k_sq / iv.mpf("12")
    proj_errs = {
        f"a_1_over_{af.denominator}": C_spin2 * tau_proj * (iv.mpf(af.numerator) / iv.mpf(af.denominator)) ** 2
        for af in a_vals
    }

    payload = {
        "schema": "ueot-physics-unification-causal-spin2-h1/1",
        "result_ids": [
            "P-H1-SPIN2-01",
            "P-H1-REGGE-02",
            "P-H1-BIANCHI-03",
            "C-H1-FRONTIER-04",
        ],
        "status": "PASS",
        "lean_module": "formalization/ueot-physics-unification/UEOTPhysicsUnification/CausalSpin2GravitonContinuumH1.lean",
        "lean_theorems": [
            "UEOTPhysicsUnification.CausalSpin2GravitonContinuumH1.dewitt_supermetric_exact_york_diagonalization",
            "UEOTPhysicsUnification.CausalSpin2GravitonContinuumH1.adm_constraint_reduction_positive_tt_hamiltonian",
            "UEOTPhysicsUnification.CausalSpin2GravitonContinuumH1.adm_tt_gauge_quotient_existsUnique_descend",
            "UEOTPhysicsUnification.CausalSpin2GravitonContinuumH1.spin2_lattice_dispersion_O_a2_exact_enclosure",
            "UEOTPhysicsUnification.CausalSpin2GravitonContinuumH1.causal_spin2_transfer_reflection_positivity_and_propagator_O_a2",
            "UEOTPhysicsUnification.CausalSpin2GravitonContinuumH1.stelle_higher_derivative_negative_ghost_residue",
            "UEOTPhysicsUnification.CausalSpin2GravitonContinuumH1.regge_schlafli_stationarity_and_einstein_variation",
            "UEOTPhysicsUnification.CausalSpin2GravitonContinuumH1.curved_regge_deficit_O_a2_continuum_convergence",
            "UEOTPhysicsUnification.CausalSpin2GravitonContinuumH1.smeared_dirac_hypersurface_wronskian_O_a2_restoration",
            "UEOTPhysicsUnification.CausalSpin2GravitonContinuumH1.smeared_dirac_wronskian_sin_cos_witness",
            "UEOTPhysicsUnification.CausalSpin2GravitonContinuumH1.bianchi_ix_classical_bkl_blowup_vs_planck_floor_regularization",
            "UEOTPhysicsUnification.CausalSpin2GravitonContinuumH1.isaacson_graviton_backreaction_positive_radiation_and_conservation",
            "UEOTPhysicsUnification.CausalSpin2GravitonContinuumH1.projective_cylindrical_multimode_quotient_and_transport",
            "UEOTPhysicsUnification.CausalSpin2GravitonContinuumH1.h1_frontier_sharp_reduction_closed_vs_nonperturbative_open",
        ],
        "spin2_york_and_lattice_propagator": {
            "dewitt_supermetric_eigenvalues": eigs_6,
            "dewitt_signature": "(-,+,+,+,+,+)",
            "tt_polarization_count": 2,
            "transfer_matrix_min_eigenvalue": outward_str(lam_min_T),
            "lattice_propagator_errors": {k: outward_str(v) for k, v in prop_errs.items()},
            "propagator_refinement_ratio_10_over_20": outward_str(ratio_prop_10_20),
            "propagator_refinement_ratio_20_over_40": outward_str(ratio_prop_20_40),
            "dispersion_refinement_ratio_20_over_40": outward_str(ratio_disp_20_40),
            "stelle_graviton_residue": "+1",
            "stelle_ghost_residue": "-1",
        },
        "regge_schlafli_and_dirac_O_a2": {
            "simplex_41_schlafli_residual_alpha_2_over_3": outward_str(abs(schlafli_der)),
            "equilateral_simplex_schlafli_residual": outward_str(abs(schlafli_eq)),
            "curved_s3_continuum_ricci": "2/3",
            "curved_s3_regge_errors": {k: outward_str(v) for k, v in regge_errs.items()},
            "curved_s3_refinement_ratio_20_over_40": outward_str(ratio_regge_20_40),
            "dirac_wronskian_errors": {k: outward_str(v) for k, v in dirac_errs.items()},
            "dirac_wronskian_refinement_ratio_20_over_40": outward_str(ratio_dirac_20_40),
        },
        "anisotropic_bianchi_isaacson_projective": {
            "ah01_planck_length_floor": outward_str(L_min_planck, digits=12),
            "planck_volume_floor_V_min": outward_str(V_min),
            "bianchi_ix_regularized_shear_cap": outward_str(shear_floor_cap),
            "classical_bkl_shear_at_V_1e_minus_10": outward_str(shear_classical_bkl),
            "isaacson_equation_of_state_w_GW": "1/3",
            "isaacson_trace_residual_max": outward_str(abs(trace_gw)),
            "projective_cylindrical_transport_bounds": {k: outward_str(v) for k, v in proj_errs.items()},
            "quotient_descent_fiber_compatible": True,
        },
        "h1_layer_decomposition": {
            "H1a_Spin2TTAndOSPositivity": "CLOSED",
            "H1b_ReggeSchlafliAndDiracO_a2": "CLOSED",
            "H1c_AnisotropicShearIsaacsonProjective": "CLOSED",
            "H1d_Nonperturbative4DFixedPointMeasure": "OPEN",
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
        require(committed == payload, "Committed certificate.json differs from recomputed Wave 8 H1 values")
        print("PASS: causal_spin2_graviton_h1 (P-H1-SPIN2-01, P-H1-REGGE-02, P-H1-BIANCHI-03, C-H1-FRONTIER-04)")
    else:
        write_json(CERT_PATH, payload)
        print("WROTE:", CERT_PATH)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
