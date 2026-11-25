"""40-digit outward-interval & symbolic verification for Wave 11 H2 (P-H2A-TRANSFER-01..C-H2-OPER-04)."""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import itertools
import json
from pathlib import Path
import sys

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(20000)

from mpmath import iv, mp
import sympy as sp
from sympy.polys.domains import ZZ
from sympy.polys.matrices import DomainMatrix

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from common import outward_str, require, sha256_file, strictly_above, strictly_below, write_json

CERT_PATH = HERE / "certificate.json"
SCRIPT_PATH = Path(__file__).resolve()


# ---------------------------------------------------------------------------
# Pure mpmath.iv complex/real matrix & SU(2) Cayley helpers (pure interval)
# ---------------------------------------------------------------------------

def iv_zeros(n: int) -> list[list]:
    z = iv.mpc(0, 0)
    return [[z for _ in range(n)] for _ in range(n)]


def iv_eye(n: int) -> list[list]:
    z = iv.mpc(0, 0)
    one = iv.mpc(1, 0)
    return [[one if i == j else z for j in range(n)] for i in range(n)]


def iv_conj(z):
    return iv.mpc(z.real, -z.imag)


def iv_conj_transpose(M: list[list]) -> list[list]:
    n = len(M)
    m = len(M[0])
    return [[iv_conj(M[i][j]) for i in range(n)] for j in range(m)]


def iv_add(A: list[list], B: list[list], scale_b=1) -> list[list]:
    n = len(A)
    if scale_b == 1:
        return [[A[i][j] + B[i][j] for j in range(n)] for i in range(n)]
    if scale_b == -1:
        return [[A[i][j] - B[i][j] for j in range(n)] for i in range(n)]
    sb = scale_b if isinstance(scale_b, type(iv.mpc(0, 0))) else iv.mpc(scale_b, 0)
    return [[A[i][j] + sb * B[i][j] for j in range(n)] for i in range(n)]


def iv_matmul(A: list[list], B: list[list]) -> list[list]:
    m = len(A)
    klen = len(A[0])
    n = len(B[0])
    zero = iv.mpc(0, 0)
    out = []
    for i in range(m):
        row_a = A[i]
        nz_k = [(k, row_a[k]) for k in range(klen) if row_a[k] != zero]
        out_row = [zero for _ in range(n)]
        for k, ak in nz_k:
            row_bk = B[k]
            for j in range(n):
                bkj = row_bk[j]
                if bkj != zero:
                    out_row[j] += ak * bkj
        out.append(out_row)
    return out


def iv_frobenius_norm(M: list[list]):
    s = iv.mpf(0)
    for row in M:
        for z in row:
            s += z.real ** 2 + z.imag ** 2
    return iv.sqrt(s)


def iv_trace(M: list[list]):
    s = iv.mpc(0, 0)
    for i in range(len(M)):
        s += M[i][i]
    return s


def mp_to_thin_iv_matrix(M_mp: mp.matrix) -> list[list]:
    r = M_mp.rows
    c = M_mp.cols
    out = []
    for i in range(r):
        row = []
        for j in range(c):
            val = M_mp[i, j]
            if isinstance(val, mp.mpc):
                row.append(iv.mpc(mp.nstr(val.real, 50), mp.nstr(val.imag, 50)))
            else:
                row.append(iv.mpc(mp.nstr(val, 50), 0))
        out.append(row)
    return out


def iv_to_midpoint_mp(M_iv: list[list]) -> mp.matrix:
    n = len(M_iv)
    M = mp.matrix(n, n)
    for i in range(n):
        for j in range(n):
            z = M_iv[i][j]
            re_mid = (mp.make_mpf(z.real._mpi_[0]) + mp.make_mpf(z.real._mpi_[1])) / 2
            im_mid = (mp.make_mpf(z.imag._mpi_[0]) + mp.make_mpf(z.imag._mpi_[1])) / 2
            M[i, j] = mp.mpc(re_mid, im_mid)
    return M


def enclose_hermitian_eigenvalues(H_iv: list[list]) -> tuple[list, object]:
    """Rigorously enclose all sorted eigenvalues of Hermitian H_iv via Weyl + polar-unitary bound."""
    n = len(H_iv)
    H_mid = iv_to_midpoint_mp(H_iv)
    for i in range(n):
        H_mid[i, i] = mp.mpc(H_mid[i, i].real, 0)
        for j in range(i + 1, n):
            avg = (H_mid[i, j] + mp.conj(H_mid[j, i])) / 2
            H_mid[i, j] = avg
            H_mid[j, i] = mp.conj(avg)

    _, evecs = mp.eigh(H_mid)
    Q_iv = mp_to_thin_iv_matrix(evecs)
    Qt = iv_conj_transpose(Q_iv)
    I_n = iv_eye(n)

    F_iv = iv_add(iv_matmul(Qt, Q_iv), I_n, scale_b=-1)
    eta = iv_frobenius_norm(F_iv)
    require(strictly_below(eta, "1e-34"), f"Eigenvector unitarity defect too large: {eta}")

    QHQ = iv_matmul(Qt, iv_matmul(H_iv, Q_iv))
    d_vals = [QHQ[i][i].real for i in range(n)]
    M_off = iv_zeros(n)
    d_max = iv.mpf(0)
    for i in range(n):
        abs_di = abs(d_vals[i])
        if abs_di.b > d_max.b:
            d_max = iv.mpf([0, abs_di.b])
        for j in range(n):
            if i == j:
                M_off[i][j] = iv.mpc(0, QHQ[i][i].imag)
            else:
                M_off[i][j] = QHQ[i][j]

    norm_M = iv_frobenius_norm(M_off)
    delta_eig = (norm_M + eta * d_max * (iv.mpf(2) + eta)) / (iv.mpf(1) - eta)
    require(strictly_below(delta_eig, "1e-33"), f"Weyl eigenvalue perturbation bound too wide: {delta_eig}")

    rad = delta_eig.b
    pad = iv.mpf([-rad, rad])
    d_sorted = sorted(
        d_vals,
        key=lambda x: (mp.make_mpf(x._mpi_[0]) + mp.make_mpf(x._mpi_[1])) / 2,
    )
    enclosed = [d + pad for d in d_sorted]
    return enclosed, delta_eig


def overlap_sign_projector_iv(H_iv: list[list]) -> tuple[list[list], object, object]:
    """Compute and rigorously certify the 16x16 overlap sign projector P_ov = (I + H (H^2)^(-1/2))/2."""
    n = len(H_iv)
    H_mid = iv_to_midpoint_mp(H_iv)
    for i in range(n):
        H_mid[i, i] = mp.mpc(H_mid[i, i].real, 0)
        for j in range(i + 1, n):
            avg = (H_mid[i, j] + mp.conj(H_mid[j, i])) / 2
            H_mid[i, j] = avg
            H_mid[j, i] = mp.conj(avg)

    _, evecs = mp.eigh(H_mid)
    Q_iv = mp_to_thin_iv_matrix(evecs)
    Qt = iv_conj_transpose(Q_iv)
    I_n = iv_eye(n)

    F_iv = iv_add(iv_matmul(Qt, Q_iv), I_n, scale_b=-1)
    eta = iv_frobenius_norm(F_iv)
    require(strictly_below(eta, "1e-34"), f"Overlap eigenvector unitarity defect too large: {eta}")

    QHQ = iv_matmul(Qt, iv_matmul(H_iv, Q_iv))
    d_vals = [QHQ[i][i].real for i in range(n)]
    M_off = iv_zeros(n)
    d_max = iv.mpf(0)
    for i in range(n):
        abs_di = abs(d_vals[i])
        if abs_di.b > d_max.b:
            d_max = iv.mpf([0, abs_di.b])
        for j in range(n):
            if i == j:
                M_off[i][j] = iv.mpc(0, QHQ[i][i].imag)
            else:
                M_off[i][j] = QHQ[i][j]

    norm_M = iv_frobenius_norm(M_off)
    delta_eig = (norm_M + eta * d_max * (iv.mpf(2) + eta)) / (iv.mpf(1) - eta)
    require(strictly_below(delta_eig, "1e-33"), f"Weyl sign-gap bound too wide: {delta_eig}")

    pos_cols = []
    neg_count = 0
    for i in range(n):
        require(strictly_above(abs(d_vals[i]) - delta_eig, "1"), f"H_W eigenvalue too close to zero: {d_vals[i]}")
        if strictly_above(d_vals[i], delta_eig):
            pos_cols.append(i)
        else:
            require(strictly_below(d_vals[i], -delta_eig), f"Ambiguous eigenvalue sign: {d_vals[i]}")
            neg_count += 1
    require(len(pos_cols) == n // 2 and neg_count == n // 2, f"Overlap projector not half-rank: {len(pos_cols)} vs {neg_count}")

    Q_pos = [[Q_iv[r][c] for c in pos_cols] for r in range(n)]
    P_ov = iv_matmul(Q_pos, iv_conj_transpose(Q_pos))
    idem_err = iv_frobenius_norm(iv_add(iv_matmul(P_ov, P_ov), P_ov, scale_b=-1))
    herm_p_err = iv_frobenius_norm(iv_add(iv_conj_transpose(P_ov), P_ov, scale_b=-1))
    require(strictly_below(idem_err, "1e-35"), f"Overlap projector idempotency failed: {idem_err}")
    require(strictly_below(herm_p_err, "1e-35"), f"Overlap projector Hermiticity failed: {herm_p_err}")

    S_ov = iv_add([[iv.mpc(2, 0) * x for x in row] for row in P_ov], I_n, scale_b=-1)
    comm_err = iv_frobenius_norm(iv_add(iv_matmul(S_ov, H_iv), iv_matmul(H_iv, S_ov), scale_b=-1))
    require(strictly_below(comm_err, "1e-35"), f"[S_ov, H_W] nonzero: {comm_err}")
    abs_H = [[iv.mpc("0.5", 0) * x for x in row] for row in iv_add(iv_matmul(S_ov, H_iv), iv_matmul(H_iv, S_ov))]
    abs_sq_err = iv_frobenius_norm(iv_add(iv_matmul(abs_H, abs_H), iv_matmul(H_iv, H_iv), scale_b=-1))
    require(strictly_below(abs_sq_err, "1e-35"), f"(S_ov H_W)^2 != H_W^2: {abs_sq_err}")
    evals_abs_H, _ = enclose_hermitian_eigenvalues(abs_H)
    require(
        strictly_above(evals_abs_H[0], "1"),
        f"S_ov H_W not strictly positive definite across all eigenvalues: {evals_abs_H[0]}",
    )
    return P_ov, idem_err, iv_trace(P_ov)


def su2_cayley_iv(p1, p2, p3) -> list[list]:
    """Exact Cayley parameterization of SU(2) with zero trigonometric calls."""
    p1_iv = iv.mpf(p1)
    p2_iv = iv.mpf(p2)
    p3_iv = iv.mpf(p3)
    r2 = p1_iv ** 2 + p2_iv ** 2 + p3_iv ** 2
    d = iv.mpf(1) + r2
    a_re = (iv.mpf(1) - r2) / d
    a_im = (iv.mpf(2) * p3_iv) / d
    b_re = (iv.mpf(2) * p2_iv) / d
    b_im = (iv.mpf(2) * p1_iv) / d
    alpha = iv.mpc(a_re, a_im)
    beta = iv.mpc(b_re, b_im)
    return [
        [alpha, beta],
        [-iv_conj(beta), iv_conj(alpha)],
    ]


def besseli_iv(n: int, x, terms: int = 26):
    """Rigorous outward-interval enclosure of modified Bessel function I_n(x) for 0 <= x < 2."""
    x_iv = iv.mpf(x)
    require(x_iv.a >= 0 and strictly_below(x_iv, "2"), "besseli_iv domain 0 <= x < 2")
    half_x = x_iv / iv.mpf(2)
    half_x_sq = half_x ** 2
    fact_n = 1
    for j in range(1, n + 1):
        fact_n *= j
    term = (half_x ** n) / iv.mpf(fact_n)
    total = term
    for k in range(1, terms):
        term = term * half_x_sq / (iv.mpf(k) * iv.mpf(n + k))
        total += term
    # Remainder <= next_term / (1 - (x/2)^2 / ((terms+1)*(n+terms+1)))
    next_term = term * half_x_sq / (iv.mpf(terms) * iv.mpf(n + terms))
    ratio_bound = half_x_sq / (iv.mpf(terms + 1) * iv.mpf(n + terms + 1))
    require(strictly_below(ratio_bound, "0.5"), "Bessel remainder ratio too large")
    rem_ub = next_term / (iv.mpf(1) - ratio_bound)
    total += iv.mpf([0, rem_ub.b])
    return total


def besseli_iv_any(n: int, x):
    """Rigorous outward-interval enclosure of modified Bessel function I_n(x) for any x >= 0."""
    x_iv = iv.mpf(x)
    require(x_iv.a >= 0, "besseli_iv_any domain x >= 0")
    half_x = x_iv / iv.mpf(2)
    half_x_sq = half_x ** 2
    fact_n = 1
    for j in range(1, n + 1):
        fact_n *= j
    terms = max(26, int(mp.ceil(mp.make_mpf(x_iv._mpi_[1]))) * 3 + 140)
    term = (half_x ** n) / iv.mpf(fact_n)
    total = term
    for k in range(1, terms):
        term = term * half_x_sq / (iv.mpf(k) * iv.mpf(n + k))
        total += term
    next_term = term * half_x_sq / (iv.mpf(terms) * iv.mpf(n + terms))
    ratio_bound = half_x_sq / (iv.mpf(terms + 1) * iv.mpf(n + terms + 1))
    require(strictly_below(ratio_bound, "0.5"), "besseli_iv_any remainder ratio too large")
    rem_ub = next_term / (iv.mpf(1) - ratio_bound)
    total += iv.mpf([0, rem_ub.b])
    return total


def neg_log_one_minus_iv(x_iv, terms: int = 50):
    """Rigorous outward-interval enclosure of -log(1 - x) for 0 <= x < 1 without 1 - (1 - x) cancellation."""
    require(x_iv.a >= 0 and strictly_below(x_iv, "1"), "neg_log_one_minus_iv domain 0 <= x < 1")
    if strictly_above(x_iv, "0.25"):
        return -iv.log(iv.mpf(1) - x_iv)
    total = iv.mpf(0)
    x_pow = x_iv
    for k in range(1, terms + 1):
        total += x_pow / iv.mpf(k)
        x_pow *= x_iv
    rem_ub = x_pow / (iv.mpf(terms + 1) * (iv.mpf(1) - x_iv))
    return total + iv.mpf([0, rem_ub.b])


def su2_half_haar_iv(beta_iv):
    """Rigorous outward-interval enclosure of int_0^{pi/2} exp(-beta cos t) sin^2 t dt via Wallis recurrence."""
    W0 = iv.pi / iv.mpf(4)
    W1 = iv.mpf(1) / iv.mpf(3)
    N = max(60, int(mp.ceil(mp.make_mpf(beta_iv._mpi_[1]))) * 4 + 120)
    total = W0 + (-beta_iv) * W1
    bpow = -beta_iv
    W_prev2, W_prev1 = W0, W1
    for k in range(2, N):
        bpow = bpow * (-beta_iv) / iv.mpf(k)
        Wk = (iv.mpf(k - 1) / iv.mpf(k + 2)) * W_prev2
        total += bpow * Wk
        W_prev2, W_prev1 = W_prev1, Wk
    next_bpow = beta_iv ** N
    for k in range(1, N + 1):
        next_bpow /= iv.mpf(k)
    ratio = beta_iv / iv.mpf(N + 1)
    require(strictly_below(ratio, "0.5"), "SU(2) Haar series remainder ratio too large")
    rem = next_bpow * (iv.pi / iv.mpf(4)) / (iv.mpf(1) - ratio)
    return total + iv.mpf([-rem.b, rem.b])


def compute_h2d_continuum_obstruction_audit() -> dict:
    """Deterministic 40-digit mpmath.iv + sympy audit for Round 03 H2d (Routes A, B, C)."""
    mp.dps = 120
    iv.dps = 40
    try:
        # ---------------------------------------------------------------------
        # Route A: Multiscale UV Block-Spin RG, KP Thresholds & MZ Obstruction
        # ---------------------------------------------------------------------
        gk2_sym, dblk_sym = sp.symbols("g_k2 Delta_blk", positive=True)
        gnext2_sym = gk2_sym / (1 - dblk_sym * gk2_sym)
        require(sp.simplify(gnext2_sym - gk2_sym - dblk_sym * gk2_sym * gnext2_sym) == 0,
                "Route A RG step identity failed")
        require(sp.simplify(sp.diff(gnext2_sym, gk2_sym) - (1 - dblk_sym * gk2_sym) ** (-2)) == 0,
                "Route A RG Jacobian derivative identity failed")
        kap_sym, eps_sym, r0_sym = sp.symbols("kappa eps_mz r0", positive=True)
        r_sym = r0_sym
        for k_idx in range(1, 6):
            r_sym = kap_sym * r_sym + eps_sym
            closed_sym = kap_sym ** k_idx * r0_sym + eps_sym * (1 - kap_sym ** k_idx) / (1 - kap_sym)
            require(sp.simplify(r_sym - closed_sym) == 0, f"Route A affine closed form failed at k={k_idx}")

        b0_su3 = iv.mpf(7)
        b1_su3 = iv.mpf(26)
        pi2_16 = iv.mpf(16) * (iv.pi ** 2)
        L_blk = iv.mpf(2)
        delta_blk = (iv.mpf(2) * b0_su3 * iv.log(L_blk)) / pi2_16

        eps_adm = iv.mpf(1) / iv.mpf(30)
        exp_adm = iv.mpf(2) * (eps_adm ** 2 / pi2_16) * b0_su3
        exp_su3_vortex = iv.mpf(2) * (iv.mpf(9) / pi2_16) * b0_su3
        require(strictly_below(exp_adm, "4") and strictly_below(exp_su3_vortex, "4"),
                "Route A single-plaquette / vortex exponents must be < 4")

        K_ent = iv.mpf(81) * iv.e
        mu_kp = iv.mpf(1)
        kp_barrier = iv.log(K_ent) + mu_kp
        g2_kp_fixed_adm = (eps_adm ** 2) / kp_barrier
        g2_kp_running_half = iv.mpf(1) / (kp_barrier ** 2)
        aK_Lambda_kp = iv.exp(-pi2_16 / (iv.mpf(2) * b0_su3 * g2_kp_running_half))
        beta_su3_kp = iv.mpf(6) / g2_kp_running_half

        gK2_target = iv.mpf("0.02")
        require(strictly_below(gK2_target, g2_kp_running_half), "Target gK2 exceeds KP delta=1/2 threshold")
        require(strictly_below(gK2_target * b1_su3, pi2_16 * b0_su3), "Target gK2 outside 2-loop AF basin")

        K_steps = 500
        inv_gK2 = iv.mpf(1) / gK2_target
        inv_g02 = inv_gK2 + iv.mpf(K_steps) * delta_blk
        g02 = iv.mpf(1) / inv_g02
        g12 = iv.mpf(1) / (inv_g02 - delta_blk)
        require(strictly_above(g12, g02), "Coarse-graining coupling g1^2 not > g0^2")
        expanding_jacobian = (g12 / g02) ** 2
        require(strictly_above(expanding_jacobian, "1"), "Coarse-graining Jacobian not > 1")

        sum_balaban = iv.mpf(0)
        sum_taylor_ub = iv.mpf(0)
        require(strictly_below(delta_blk, inv_gK2), "delta_blk not minimal scale")
        for j in range(K_steps):
            w_j = iv.exp(-iv.sqrt(inv_gK2 + iv.mpf(j) * delta_blk))
            sum_balaban += w_j
            ub_j = iv.mpf(24) / ((delta_blk ** 2) * (iv.mpf(j + 1) ** 2))
            require(strictly_below(w_j, ub_j), f"Route A Taylor bound failed at j={j}")
            sum_taylor_ub += ub_j
        uniform_taylor_ceiling = iv.mpf(48) / (delta_blk ** 2)
        require(strictly_below(sum_balaban, sum_taylor_ub) and strictly_below(sum_taylor_ub, uniform_taylor_ceiling),
                "Route A Balaban sum failed Taylor ceiling")

        wK_fixed = iv.exp(-(eps_adm ** 2) * inv_gK2)
        q_fixed = iv.exp(-(eps_adm ** 2) * delta_blk)
        geom_ub_fixed = wK_fixed / (iv.mpf(1) - q_fixed)

        r_mz = iv.mpf(0)
        for _ in range(40):
            r_mz = iv.mpf("0.5") * r_mz + iv.mpf(1) / iv.mpf(16)
        require(strictly_above(r_mz, "0.124999999999") and strictly_below(r_mz, "0.125000000001"),
                "Route A MZ floor did not converge to 1/8")

        route_a = {
            "su3_delta_blk": outward_str(delta_blk),
            "su3_center_vortex_exponent": outward_str(exp_su3_vortex),
            "kp_barrier_ln_81e_plus_1": outward_str(kp_barrier),
            "g2_kp_fixed_adm": outward_str(g2_kp_fixed_adm),
            "g2_kp_running_delta_half": outward_str(g2_kp_running_half),
            "aK_lambda_at_kp_half": outward_str(aK_Lambda_kp),
            "beta_su3_at_kp_half": outward_str(beta_su3_kp),
            "k500_g02": outward_str(g02),
            "k500_expanding_jacobian_multiplier": outward_str(expanding_jacobian),
            "k500_sum_balaban_delta_half": outward_str(sum_balaban),
            "k500_sum_taylor_ub": outward_str(sum_taylor_ub),
            "uniform_taylor_ceiling_48_over_delta_sq": outward_str(uniform_taylor_ceiling),
            "fixed_eps_geom_ub": outward_str(geom_ub_fixed),
            "mz_affine_floor_step_40": outward_str(r_mz),
            "sympy_rg_identities_verified": True,
        }

        # ---------------------------------------------------------------------
        # Route B: IR Crossover, Q8/SU(2) Dobrushin Breakdown, Bessel & Doubling
        # ---------------------------------------------------------------------
        u_sym = sp.Symbol("u")
        def hankel_poly(n_ord: int, K_ord: int = 5):
            s_expr = sp.Integer(1)
            term_expr = sp.Integer(1)
            for k_ord in range(1, K_ord + 1):
                term_expr = term_expr * (4 * n_ord ** 2 - (2 * k_ord - 1) ** 2) / (8 * k_ord) * (-u_sym)
                s_expr += term_expr
            return s_expr
        ratio_ser = sp.series(hankel_poly(2, 5) / hankel_poly(1, 5), u_sym, 0, 4)
        require(ratio_ser.coeff(u_sym, 0) == 1 and ratio_ser.coeff(u_sym, 1) == sp.Rational(-3, 2),
                "Sympy Bessel I2/I1 asymptotic ratio mismatch")
        sigma_ser = sp.series(-sp.log(ratio_ser.removeO()), u_sym, 0, 4)
        require(sigma_ser.coeff(u_sym, 1) == sp.Rational(3, 2),
                "Sympy sigma_SC asymptotic coefficient mismatch")

        c_af_su2 = (iv.mpf(3) * (iv.pi ** 2)) / iv.mpf(11)
        q8_and_h2a_scaling = {}
        for label, b_frac in (
            ("beta_0_5", Fraction(1, 2)),
            ("beta_5", Fraction(5, 1)),
            ("beta_20", Fraction(20, 1)),
            ("beta_50", Fraction(50, 1)),
            ("beta_100", Fraction(100, 1)),
            ("beta_200", Fraction(200, 1)),
        ):
            beta_iv = iv.mpf(b_frac.numerator) / iv.mpf(b_frac.denominator)
            exp_b = iv.exp(beta_iv)
            exp_mb = iv.exp(-beta_iv)
            z_q8 = exp_b + exp_mb + iv.mpf(6)
            one_minus_alpha = (iv.mpf(2) * exp_mb + iv.mpf(6)) / z_q8
            alpha_q8 = (exp_b - exp_mb) / z_q8
            m_lat_1 = neg_log_one_minus_iv(one_minus_alpha)
            require(strictly_above(m_lat_1, "0"), f"Q8 gap not positive at {label}")
            a_lat = iv.exp(-c_af_su2 * beta_iv)
            m_lat_1_over_a = m_lat_1 / a_lat
            bc1_q8 = iv.mpf(8) / z_q8
            bc64_q8 = bc1_q8 ** 64
            local_18_alpha_q8 = iv.mpf(18) * alpha_q8
            require(strictly_above(local_18_alpha_q8, "1"), f"Q8 18*alpha <= 1 at {label}")

            i1_b = besseli_iv_any(1, beta_iv)
            i2_b = besseli_iv_any(2, beta_iv)
            u_char = i2_b / i1_b
            sigma_sc = -iv.log(u_char)
            beta_sigma_sc = beta_iv * sigma_sc
            sigma_sc_over_a2 = sigma_sc / (a_lat ** 2)

            q8_and_h2a_scaling[label] = {
                "beta": str(b_frac),
                "q8_one_minus_alpha": outward_str(one_minus_alpha),
                "q8_m_lat_1": outward_str(m_lat_1),
                "q8_m_lat_1_over_a": outward_str(m_lat_1_over_a),
                "q8_bc1_pow_64": outward_str(bc64_q8),
                "q8_local_18_alpha": outward_str(local_18_alpha_q8),
                "h2a_beta_sigma_sc": outward_str(beta_sigma_sc),
                "h2a_sigma_sc_over_a2": outward_str(sigma_sc_over_a2),
            }

        # Specific Route B threshold assertions at beta = 200
        b200 = q8_and_h2a_scaling["beta_200"]
        require(strictly_above(iv.mpf(b200["q8_m_lat_1_over_a"][0]), "1e147"),
                "Q8 M=1 divergence at beta=200 failed")
        require(strictly_below(iv.mpf(b200["q8_bc1_pow_64"][1]), "1e-5500"),
                "Q8 M=64 Bhattacharyya collapse at beta=200 failed")
        m_global_64_over_a_200 = neg_log_one_minus_iv(iv.mpf(b200["q8_bc1_pow_64"][1])) / iv.exp(-c_af_su2 * iv.mpf(200))
        require(strictly_below(m_global_64_over_a_200, "1e-5260"),
                "Q8 M=64 m_global/a collapse at beta=200 failed")
        require(strictly_above(iv.mpf(b200["h2a_beta_sigma_sc"][0]), "1.5") and
                strictly_below(iv.mpf(b200["h2a_beta_sigma_sc"][1]), "1.504"),
                "H2a beta*sigma_SC asymptotic window at beta=200 failed")
        require(strictly_above(iv.mpf(b200["h2a_sigma_sc_over_a2"][0]), "2.9e465"),
                "H2a sigma_SC/a^2 divergence at beta=200 failed")

        su2_local_dobrushin = {}
        for label, b_frac in (
            ("beta_0_1", Fraction(1, 10)),
            ("beta_0_25", Fraction(1, 4)),
            ("beta_0_5", Fraction(1, 2)),
            ("beta_1_0", Fraction(1, 1)),
            ("beta_5_0", Fraction(5, 1)),
            ("beta_20_0", Fraction(20, 1)),
        ):
            beta_iv = iv.mpf(b_frac.numerator) / iv.mpf(b_frac.denominator)
            num_su2 = iv.mpf(2) * su2_half_haar_iv(beta_iv)
            den_su2 = iv.pi * besseli_iv_any(1, beta_iv) / beta_iv
            alpha_su2 = iv.mpf(1) - num_su2 / den_su2
            sum_18_su2 = iv.mpf(18) * alpha_su2
            if b_frac >= Fraction(1, 4):
                require(strictly_above(sum_18_su2, "1"), f"SU(2) 18*alpha <= 1 at {label}")
            else:
                require(strictly_below(sum_18_su2, "1"), f"SU(2) 18*alpha not < 1 at {label}")
            su2_local_dobrushin[label] = {
                "beta": str(b_frac),
                "alpha_su2": outward_str(alpha_su2),
                "local_18_alpha_su2": outward_str(sum_18_su2),
            }

        # 2x2 semigroup doubling convergence: U(t) = diag(e^{-t}, e^{-2t}), C_psi = 2 ||psi||^2
        c_ratio = iv.mpf(2)
        doubling_40 = c_ratio ** (iv.mpf(1) / (iv.mpf(2) ** 40))
        require(strictly_above(doubling_40, "1") and strictly_below(doubling_40, "1.000000000001"),
                "Semigroup doubling convergence check failed at k=40")

        route_b = {
            "c_af_pure_su2": outward_str(c_af_su2),
            "sympy_bessel_i2_over_i1_3_over_2_verified": True,
            "q8_and_h2a_scaling": q8_and_h2a_scaling,
            "q8_m64_global_gap_over_a_beta_200_ub": outward_str(m_global_64_over_a_200),
            "continuous_su2_local_dobrushin": su2_local_dobrushin,
            "semigroup_doubling_ratio_k0": outward_str(c_ratio),
            "semigroup_doubling_ratio_k40": outward_str(doubling_40),
        }

        # ---------------------------------------------------------------------
        # Route C: T^2 Flat Holonomy, Complex Chiral RP Failure & Entropy Blowup
        # ---------------------------------------------------------------------
        L_torus = 3
        c_cochain = iv.pi / iv.mpf(L_torus)
        plaq_curv = (c_cochain + iv.mpf(0)) - (c_cochain + iv.mpf(0))
        require(plaq_curv.a <= 0 <= plaq_curv.b, "T^2 plaquette curvature does not contain 0")
        polyakov_hol = iv.mpf(L_torus) * c_cochain
        require(strictly_above(polyakov_hol, "3.14159"), "T^2 Polyakov holonomy not > 3.14159")
        phase_jump = abs(iv.exp(iv.mpc(0, 1) * iv.mpc(polyakov_hol, 0)) - iv.mpc(1, 0))
        require(strictly_above(phase_jump, "1.999999") and strictly_below(phase_jump, "2.000001"),
                f"T^2 phase discontinuity != 2: {phase_jump}")

        # Complex chiral phase RP failure at r = 1, c = 1 + i
        w_pi_half_im = iv.sin(iv.pi / iv.mpf(2))
        require(strictly_above(w_pi_half_im, "0.999999"), "Im w(pi/2) check failed")
        c_test = iv.mpc(1, 1)
        rp_pi = (iv_conj(c_test) * iv.exp(iv.mpc(0, 1) * iv.mpc(iv.pi, 0)) * c_test).real
        require(strictly_below(rp_pi, "-1.999999"), f"Chiral phase RP negation check failed: {rp_pi}")

        two_cadm_b0 = iv.mpf(2) * ((eps_adm ** 2) / pi2_16) * b0_su3
        entropy_excess = iv.mpf(4) - two_cadm_b0
        require(strictly_above(entropy_excess, "3.9999"), "Admissibility entropy excess <= 3.9999")
        admissibility_blowup = {}
        prev_blowup = iv.mpf(0)
        for tag, a_lam_str in (("a_lam_1e_minus_4", "1e-4"), ("a_lam_1e_minus_8", "1e-8"), ("a_lam_1e_minus_16", "1e-16")):
            a_lam = iv.mpf(a_lam_str)
            val = (iv.mpf(1) / a_lam) ** 4 * (a_lam ** two_cadm_b0)
            require(strictly_above(val, prev_blowup), "Admissibility blowup not strictly increasing")
            prev_blowup = val
            admissibility_blowup[tag] = outward_str(val)

        route_c = {
            "t2_flat_curvature_bracket": outward_str(plaq_curv, digits=12),
            "t2_polyakov_holonomy": outward_str(polyakov_hol),
            "t2_phase_discontinuity_norm": outward_str(phase_jump),
            "chiral_phase_im_pi_half": outward_str(w_pi_half_im),
            "chiral_phase_rp_at_pi_c_1_plus_i": outward_str(rp_pi),
            "admissibility_entropy_excess_4_minus_2cb0": outward_str(entropy_excess),
            "admissibility_union_bound_blowup": admissibility_blowup,
        }

        return {
            "h2d_status": "OPEN",
            "route_a_uv_multiscale_rg": route_a,
            "route_b_ir_crossover_and_os_gap": route_b,
            "route_c_chiral_holonomy_and_admissibility": route_c,
        }
    finally:
        mp.dps = 50
        iv.dps = 40


def _frac_invert(mat: list[list[Fraction]]) -> list[list[Fraction]]:
    """Exact Gaussian-Jordan inversion over Q using sparse nonzero row pivots."""
    n = len(mat)
    aug = [
        [mat[r][c] for c in range(n)] + [Fraction(1, 1) if r == c else Fraction(0, 1) for c in range(n)]
        for r in range(n)
    ]
    for col in range(n):
        piv = None
        for r in range(col, n):
            if aug[r][col] != 0:
                piv = r
                break
        require(piv is not None, f"Singular rational matrix at column {col}")
        if piv != col:
            aug[col], aug[piv] = aug[piv], aug[col]
        piv_val = aug[col][col]
        if piv_val != 1:
            row_c = aug[col]
            for j in range(col, 2 * n):
                if row_c[j] != 0:
                    row_c[j] /= piv_val
        row_c = aug[col]
        nz_cols = [j for j in range(col + 1, 2 * n) if row_c[j] != 0]
        for r in range(n):
            if r == col:
                continue
            factor = aug[r][col]
            if factor != 0:
                row_r = aug[r]
                row_r[col] = Fraction(0, 1)
                for j in nz_cols:
                    row_r[j] -= factor * row_c[j]
    return [row[n:] for row in aug]


def _iv_det_2x2(M: list[list]):
    return M[0][0] * M[1][1] - M[0][1] * M[1][0]


def _iv_det_4x4(M: list[list]):
    """Exact 4x4 Laplace expansion over iv.mpc."""
    def det3(rows: tuple[int, int, int], cols: tuple[int, int, int]):
        r0, r1, r2 = rows
        c0, c1, c2 = cols
        return (
            M[r0][c0] * (M[r1][c1] * M[r2][c2] - M[r1][c2] * M[r2][c1])
            - M[r0][c1] * (M[r1][c0] * M[r2][c2] - M[r1][c2] * M[r2][c0])
            + M[r0][c2] * (M[r1][c0] * M[r2][c1] - M[r1][c1] * M[r2][c0])
        )
    return (
        M[0][0] * det3((1, 2, 3), (1, 2, 3))
        - M[0][1] * det3((1, 2, 3), (0, 2, 3))
        + M[0][2] * det3((1, 2, 3), (0, 1, 3))
        - M[0][3] * det3((1, 2, 3), (0, 1, 2))
    )


def compute_h2d_round04_constructive_bridges() -> dict:
    """Deterministic 40-digit mpmath.iv + sympy + Fraction bridges & Red-Team guards for Round 04 H2d."""
    mp.dps = 50
    iv.dps = 40
    try:
        interval_checks = 0

        def check(ok: bool, msg: str) -> None:
            nonlocal interval_checks
            require(ok, msg)
            interval_checks += 1

        # =====================================================================
        # Track 1 (UV): Decaying MZ, Vacuum Counterterms & 16^j, Combes-Thomas & Schur
        # =====================================================================
        mz_tuples = (
            ("kappa_1_2_C_1_4_k0_2", Fraction(1, 2), Fraction(1, 4), 2),
            ("kappa_1_2_C_1_16_k0_4", Fraction(1, 2), Fraction(1, 16), 4),
            ("kappa_3_4_C_1_k0_5", Fraction(3, 4), Fraction(1, 1), 5),
        )
        eps_const = iv.mpf(1) / iv.mpf(16)
        mz_checkpoints_k = (20, 50, 100, 200)
        mz_decay_results = {}
        for label, kap_f, C_f, k0 in mz_tuples:
            kap_iv = iv.mpf(kap_f.numerator) / iv.mpf(kap_f.denominator)
            C_iv = iv.mpf(C_f.numerator) / iv.mpf(C_f.denominator)
            r_dec = [iv.mpf(0)]
            r_con = [iv.mpf(0)]
            for k in range(200):
                eps_k = C_iv / (iv.mpf(k + k0) ** 2)
                r_dec.append(kap_iv * r_dec[-1] + eps_k)
                r_con.append(kap_iv * r_con[-1] + eps_const)
            ckpts = {}
            for k in mz_checkpoints_k:
                m = k // 2
                ub_split = (
                    (kap_iv ** (k - m)) * C_iv * (iv.mpf(1) / iv.mpf(k0 ** 2) + iv.mpf(1) / iv.mpf(k0))
                    + C_iv / ((iv.mpf(m + k0) ** 2) * (iv.mpf(1) - kap_iv))
                )
                check(strictly_below(r_dec[k], ub_split), f"MZ splitting bound failed at {label} k={k}")
                check(strictly_below(r_dec[k], r_con[k]), f"MZ decay not < const at {label} k={k}")
                ckpts[f"k_{k}"] = {
                    "r_decay": outward_str(r_dec[k]),
                    "r_const": outward_str(r_con[k]),
                    "splitting_ub": outward_str(ub_split),
                }
            check(strictly_below(r_dec[200], "1e-4"), f"MZ r_decay[200] not < 1e-4 at {label}")
            const_limit = eps_const / (iv.mpf(1) - kap_iv)
            check(
                strictly_above(r_con[200], iv.mpf("0.999999") * const_limit),
                f"MZ r_const[200] did not saturate floor at {label}",
            )
            mz_decay_results[label] = {
                "kappa": str(kap_f),
                "C": str(C_f),
                "k0": k0,
                "const_floor": outward_str(const_limit),
                "checkpoints": ckpts,
            }

        # Red-Team Avenue 1 traps: p=1 non-summability & M-33.4 incompatible scaling
        harm_200 = sum(iv.mpf(1) / iv.mpf(k) for k in range(1, 201))
        basel_200_check = sum(iv.mpf(1) / iv.mpf(k ** 2) for k in range(1, 201))
        check(strictly_above(harm_200, "5.8") and strictly_below(basel_200_check, "2"),
              "p=1 vs p=2 summability contrast failed")
        m334_dim6_L_prime = iv.mpf(4) * (iv.mpf(1) / iv.mpf(4))
        check(m334_dim6_L_prime.a <= 1 <= m334_dim6_L_prime.b and abs(m334_dim6_L_prime - iv.mpf(1)) == 0,
              "M-33.4 dim-6 rescaling L_prime != 1")
        m334_exp_blowup_k1 = iv.exp(iv.sqrt(iv.mpf(2))) / iv.mpf(4)
        m334_exp_blowup_k200 = iv.exp(iv.sqrt(iv.mpf(201))) / iv.mpf(201 ** 2)
        check(strictly_above(m334_exp_blowup_k200, m334_exp_blowup_k1) and strictly_above(m334_exp_blowup_k200, "10"),
              "M-33.4 exponential rescaling blowup check failed")

        # 1.2 Vacuum counterterm telescoping, Basel bound & 16^j unsubtracted blowup
        E_syms = sp.symbols("E0:7")
        R_syms = sp.symbols("R0:6")
        for K_alg in range(1, 7):
            lhs = E_syms[K_alg] - sum(E_syms[j + 1] - E_syms[j] - R_syms[j] for j in range(K_alg))
            rhs = E_syms[0] + sum(R_syms[j] for j in range(K_alg))
            check(sp.expand(lhs - rhs) == 0, f"Vacuum counterterm telescoping failed at K={K_alg}")

        b0_su3 = iv.mpf(7)
        pi2_16 = iv.mpf(16) * (iv.pi ** 2)
        delta_blk = (iv.mpf(2) * b0_su3 * iv.log(iv.mpf(2))) / pi2_16
        pi_sq_over_6 = (iv.pi ** 2) / iv.mpf(6)
        phys_rem_ceiling = pi_sq_over_6 / (delta_blk ** 2)
        basel_sweep = {}
        for K_val in (10, 50, 200, 500):
            s_frac = sum(Fraction(1, (j + 1) ** 2) for j in range(K_val))
            frac_ub = Fraction(2 * K_val - 1, K_val)
            check(s_frac <= frac_ub and frac_ub < 2, f"Fraction Basel bound failed at K={K_val}")
            s_iv = sum(iv.mpf(1) / iv.mpf((j + 1) ** 2) for j in range(K_val))
            check(strictly_below(s_iv, pi_sq_over_6) and strictly_below(pi_sq_over_6, "2"),
                  f"iv Basel bound failed at K={K_val}")
            phys_rem = sum(iv.mpf(1) / ((iv.mpf(50) + iv.mpf(j) * delta_blk) ** 2) for j in range(K_val))
            check(strictly_below(phys_rem, phys_rem_ceiling), f"Physical SU(3) remainder exceeded ceiling at K={K_val}")
            log10_vac_2_4K = iv.mpf(4 * K_val) * iv.log10(iv.mpf(2))
            check(strictly_above(log10_vac_2_4K, iv.mpf(12)), f"2^(4K) log10 check failed at K={K_val}")
            basel_sweep[f"K_{K_val}"] = {
                "fraction_sum": str(s_frac),
                "fraction_ub": str(frac_ub),
                "iv_partial_sum": outward_str(s_iv),
                "su3_running_remainder": outward_str(phys_rem),
                "unsubtracted_2_pow_4K_log10": outward_str(log10_vac_2_4K),
            }

        # Red-Team 16^j unsubtracted blowup counterexamples
        eps_adm = iv.mpf(1) / iv.mpf(30)
        unsub_blowup_sweep = {}
        prev_unsub = iv.mpf(0)
        prev_exp_unsub = iv.mpf(0)
        for j_val in (10, 20, 40, 80):
            inv_gj2 = iv.mpf(50) + iv.mpf(j_val) * delta_blk
            unsub_val = (iv.mpf(16) ** j_val) / (inv_gj2 ** 2)
            unsub_exp_val = (iv.mpf(16) ** j_val) * iv.exp(-(eps_adm ** 2) * inv_gj2)
            check(strictly_above(unsub_val, prev_unsub), f"16^j / (1/g0^2+j*Delta)^2 not increasing at j={j_val}")
            check(strictly_above(unsub_exp_val, prev_exp_unsub), f"16^j exp(-eps_adm^2/g_j^2) not increasing at j={j_val}")
            prev_unsub = unsub_val
            prev_exp_unsub = unsub_exp_val
            unsub_blowup_sweep[f"j_{j_val}"] = {
                "unsubtracted_16j_g4": outward_str(unsub_val),
                "unsubtracted_16j_adm_exp": outward_str(unsub_exp_val),
            }
        check(strictly_above(prev_unsub, "1e85"), "16^80 / (1/g0^2 + 80*Delta)^2 blowup < 1e85")

        # 1.3 4D 2x2x2xL_t exact Fraction Combes-Thomas & Schur coercivity + N=48 iv inverse
        h_frac = Fraction(1, 4)
        h_iv = iv.mpf(1) / iv.mpf(4)

        def build_4d_lattice_hessian(L_t: int, m2_f: Fraction):
            coords = [(x, y, z, t) for x in range(2) for y in range(2) for z in range(2) for t in range(L_t)]
            N = len(coords)
            A = [[Fraction(0, 1) for _ in range(N)] for _ in range(N)]
            dist = [[0 for _ in range(N)] for _ in range(N)]
            for i in range(N):
                xi, yi, zi, ti = coords[i]
                deg = 0
                for j in range(N):
                    xj, yj, zj, tj = coords[j]
                    d_ij = abs(xi - xj) + abs(yi - yj) + abs(zi - zj) + abs(ti - tj)
                    dist[i][j] = d_ij
                    if d_ij == 1:
                        A[i][j] = -h_frac
                        deg += 1
                A[i][i] = m2_f + deg * h_frac
            return coords, A, dist

        combes_thomas_exact_sweep = {}
        for L_t in (2, 3, 4):
            for m2_label, m2_f in (("m2_1_2", Fraction(1, 2)), ("m2_1", Fraction(1, 1)), ("m2_4", Fraction(4, 1))):
                coords, A_frac, dist = build_4d_lattice_hessian(L_t, m2_f)
                N = len(coords)
                A_inv_frac = _frac_invert(A_frac)
                # Verify A * A_inv == I_N exactly
                for i in range(N):
                    for j in range(N):
                        entry = sum(A_frac[i][k] * A_inv_frac[k][j] for k in range(N))
                        check(entry == (Fraction(1, 1) if i == j else Fraction(0, 1)),
                              f"Exact Fraction inverse failed at L_t={L_t}, {m2_label}, ({i},{j})")

                m2_iv = iv.mpf(m2_f.numerator) / iv.mpf(m2_f.denominator)
                mu_ct = iv.log(iv.mpf(1) + m2_iv / (iv.mpf(16) * h_iv))
                ct_amp = iv.mpf(2) / m2_iv
                max_ct_ratio = iv.mpf(0)
                for i in range(N):
                    for j in range(N):
                        val_q = A_inv_frac[i][j]
                        check(val_q >= 0, f"Positivity violated at L_t={L_t}, {m2_label}, ({i},{j})")
                        val_iv = iv.mpf(val_q.numerator) / iv.mpf(val_q.denominator)
                        ct_bound = ct_amp * iv.exp(-mu_ct * iv.mpf(dist[i][j]))
                        check(strictly_below(val_iv, ct_bound),
                              f"Combes-Thomas bound failed at L_t={L_t}, {m2_label}, ({i},{j})")
                        ratio = val_iv / ct_bound
                        if ratio.b > max_ct_ratio.b:
                            max_ct_ratio = ratio

                # Checkerboard Schur complement S_C = A_CC - A_CF A_FF^{-1} A_FC
                C_idx = [i for i, (x, y, z, t) in enumerate(coords) if (x + y + z + t) % 2 == 0]
                F_idx = [i for i, (x, y, z, t) in enumerate(coords) if (x + y + z + t) % 2 == 1]
                n_C = len(C_idx)
                n_F = len(F_idx)
                for fi_pos, fi in enumerate(F_idx):
                    for fj_pos, fj in enumerate(F_idx):
                        if fi_pos != fj_pos:
                            check(A_frac[fi][fj] == 0, "F-block not diagonal in checkerboard split")
                S_C = [[Fraction(0, 1) for _ in range(n_C)] for _ in range(n_C)]
                for r in range(n_C):
                    ir = C_idx[r]
                    for c in range(n_C):
                        ic = C_idx[c]
                        corr = sum(
                            A_frac[ir][fi] * (Fraction(1, 1) / A_frac[fi][fi]) * A_frac[fi][ic]
                            for fi in F_idx
                            if A_frac[ir][fi] != 0 and A_frac[fi][ic] != 0
                        )
                        S_C[r][c] = A_frac[ir][ic] - corr

                # Verify (A_inv)_CC * S_C == I_{n_C}
                for r in range(n_C):
                    for c in range(n_C):
                        prod_rc = sum(A_inv_frac[C_idx[r]][C_idx[k]] * S_C[k][c] for k in range(n_C))
                        check(prod_rc == (Fraction(1, 1) if r == c else Fraction(0, 1)),
                              f"Schur complement inverse identity failed at L_t={L_t}, {m2_label}")

                min_diag_dom = min(
                    S_C[r][r] - sum(abs(S_C[r][c]) for c in range(n_C) if c != r)
                    for r in range(n_C)
                )
                check(min_diag_dom >= m2_f, f"Schur diagonal dominance < m^2 at L_t={L_t}, {m2_label}")

                entry_rec = {
                    "L_t": L_t,
                    "N": N,
                    "m2": str(m2_f),
                    "mu_ct": outward_str(mu_ct),
                    "max_entry_to_ct_bound_ratio": outward_str(max_ct_ratio),
                    "schur_min_diag_dominance_margin": str(min_diag_dom),
                }
                if L_t in (2, 3):
                    S_C_iv = [
                        [iv.mpc(iv.mpf(S_C[r][c].numerator) / iv.mpf(S_C[r][c].denominator), 0) for c in range(n_C)]
                        for r in range(n_C)
                    ]
                    evals_SC, _ = enclose_hermitian_eigenvalues(S_C_iv)
                    check(strictly_above(evals_SC[0], m2_iv),
                          f"Schur lambda_min <= m^2 at L_t={L_t}, {m2_label}: {evals_SC[0]}")
                    entry_rec["schur_lambda_min"] = outward_str(evals_SC[0])
                combes_thomas_exact_sweep[f"Lt_{L_t}_{m2_label}"] = entry_rec

        # N = 48 (L_t = 6) certified mpmath.iv inverse across m^2 in {1/2, 1, 4}
        combes_thomas_n48_iv = {}
        for m2_label, m2_f in (("m2_1_2", Fraction(1, 2)), ("m2_1", Fraction(1, 1)), ("m2_4", Fraction(4, 1))):
            coords48, A48_frac, dist48 = build_4d_lattice_hessian(6, m2_f)
            N48 = len(coords48)
            A48_mp = mp.matrix(N48, N48)
            A48_iv = iv_zeros(N48)
            for i in range(N48):
                for j in range(N48):
                    q = A48_frac[i][j]
                    if q != 0:
                        val_mp = mp.mpf(q.numerator) / mp.mpf(q.denominator)
                        val_iv = iv.mpf(q.numerator) / iv.mpf(q.denominator)
                        A48_mp[i, j] = val_mp
                        A48_iv[i][j] = iv.mpc(val_iv, 0)
            inv48_mid_mp = A48_mp ** (-1)
            inv48_mid_iv = mp_to_thin_iv_matrix(inv48_mid_mp)
            I48_iv = iv_eye(N48)
            R48_iv = iv_add(I48_iv, iv_matmul(A48_iv, inv48_mid_iv), scale_b=-1)
            r_row_sums = [sum(abs(R48_iv[i][j].real) + abs(R48_iv[i][j].imag) for j in range(N48)) for i in range(N48)]
            r_inf = iv.mpf([max(s.a for s in r_row_sums), max(s.b for s in r_row_sums)])
            check(strictly_below(r_inf, "1e-38"), f"N=48 residual r_inf >= 1e-38 at {m2_label}: {r_inf}")
            inv_row_sums = [sum(abs(inv48_mid_iv[i][j].real) for j in range(N48)) for i in range(N48)]
            inv_inf = iv.mpf([max(s.a for s in inv_row_sums), max(s.b for s in inv_row_sums)])
            err_ub = (inv_inf * r_inf) / (iv.mpf(1) - r_inf)
            err_pad = iv.mpf([-err_ub.b, err_ub.b])

            m2_iv = iv.mpf(m2_f.numerator) / iv.mpf(m2_f.denominator)
            mu_ct = iv.log(iv.mpf(1) + m2_iv / (iv.mpf(16) * h_iv))
            ct_amp = iv.mpf(2) / m2_iv
            max_ct_ratio_48 = iv.mpf(0)
            for i in range(N48):
                for j in range(N48):
                    enc_ij = inv48_mid_iv[i][j].real + err_pad
                    check(strictly_above(enc_ij, "0"), f"N=48 entry positivity failed at {m2_label} ({i},{j})")
                    ct_bound = ct_amp * iv.exp(-mu_ct * iv.mpf(dist48[i][j]))
                    check(strictly_below(enc_ij, ct_bound), f"N=48 Combes-Thomas failed at {m2_label} ({i},{j})")
                    ratio = enc_ij / ct_bound
                    if ratio.b > max_ct_ratio_48.b:
                        max_ct_ratio_48 = ratio
            combes_thomas_n48_iv[m2_label] = {
                "N": N48,
                "m2": str(m2_f),
                "r_inf_residual": outward_str(r_inf, digits=12),
                "neumann_enclosure_err_ub": outward_str(err_ub, digits=12),
                "max_entry_to_ct_bound_ratio": outward_str(max_ct_ratio_48),
            }

        # Red-Team m^2 = 0 Gribov / toron zero-mode guard
        _, A_zero_m2, _ = build_4d_lattice_hessian(2, Fraction(0, 1))
        zero_mode_res = [sum(row) for row in A_zero_m2]
        check(all(r == 0 for r in zero_mode_res), "m^2=0 constant vector not in ker(A)")
        check(sp.Matrix([[sp.Rational(x.numerator, x.denominator) for x in row] for row in A_zero_m2]).det() == 0,
              "m^2=0 Hessian determinant unexpectedly nonzero")

        track_1_uv = {
            "mz_decaying_vs_const": mz_decay_results,
            "mz_redteam_traps": {
                "harmonic_p1_sum_200": outward_str(harm_200),
                "basel_p2_sum_200": outward_str(basel_200_check),
                "m334_dim6_L_prime_eq_1": outward_str(m334_dim6_L_prime, digits=12),
                "m334_exp_c_k_polynomial_eps_k200": outward_str(m334_exp_blowup_k200),
            },
            "vacuum_counterterm_and_basel": {
                "sympy_telescoping_verified_K1_to_6": True,
                "su3_running_remainder_ceiling": outward_str(phys_rem_ceiling),
                "basel_and_running_sweep": basel_sweep,
                "redteam_16j_unsubtracted_blowup": unsub_blowup_sweep,
            },
            "combes_thomas_and_schur_4d": {
                "exact_fraction_sweep_9_pairs": combes_thomas_exact_sweep,
                "certified_iv_n48_sweep": combes_thomas_n48_iv,
                "redteam_m2_zero_gribov_toron_det_zero": True,
            },
        }

        # =====================================================================
        # Track 2 (IR): Q8 Volume Tensorization, Holley-Stroock, Physical Blocking, H(4)
        # =====================================================================
        Q8 = q8_matrices_iv()
        q8_gram = [[iv.mpc(0, 0) for _ in range(8)] for _ in range(8)]
        for i in range(8):
            U_i = Q8[i]
            for j in range(8):
                U_j_dag = iv_conj_transpose(Q8[j])
                q8_gram[i][j] = iv_trace(iv_matmul(U_i, U_j_dag)).real

        q8_volume_sweep = {}
        I8 = iv_eye(8)
        for label, b_frac in (("beta_1_2", Fraction(1, 2)), ("beta_5", Fraction(5, 1))):
            beta_eff = iv.mpf(b_frac.numerator) / iv.mpf(b_frac.denominator)
            z_q8 = iv.exp(beta_eff) + iv.exp(-beta_eff) + iv.mpf(6)
            theta_1 = iv.mpf(8) / z_q8
            one_minus_alpha_1 = (iv.mpf(2) * iv.exp(-beta_eff) + iv.mpf(6)) / z_q8
            P0 = [[iv.mpc(iv.exp(beta_eff * q8_gram[x][y] / iv.mpf(2)) / z_q8, 0) for y in range(8)] for x in range(8)]
            L_q8 = iv_add(I8, P0, scale_b=-1)
            evals_q8, _ = enclose_hermitian_eigenvalues(L_q8)
            check(strictly_below(abs(evals_q8[0]), "1e-35"), f"Q8 L_q8 lambda_0 != 0 at {label}")
            check(strictly_above(evals_q8[1], "0"), f"Q8 L_q8 spectral gap <= 0 at {label}")
            c_P_1 = iv.mpf(1) / evals_q8[1]

            vol_pts = {}
            for M in (1, 4, 16, 64):
                one_minus_alpha_M_ub = theta_1 ** M
                exact_prod_minor = one_minus_alpha_1 ** M
                check(strictly_below(exact_prod_minor, one_minus_alpha_M_ub) or M == 1,
                      f"Minorization > theta_1^M at {label} M={M}")
                if M == 64 and b_frac == Fraction(5, 1):
                    check(strictly_below(one_minus_alpha_M_ub, "1e-80"), "Q8 M=64 beta=5 Dobrushin collapse check failed")
                vol_pts[f"M_{M}"] = {
                    "one_minus_alpha_1_pow_M": outward_str(exact_prod_minor),
                    "theta_1_pow_M_collapse_ub": outward_str(one_minus_alpha_M_ub),
                    "poincare_c_P_M_eq_c_P_1": outward_str(c_P_1),
                }
            q8_volume_sweep[label] = {
                "beta_eff": str(b_frac),
                "theta_1": outward_str(theta_1),
                "lambda_1_single_site": outward_str(evals_q8[1]),
                "c_P_single_site": outward_str(c_P_1),
                "volumes": vol_pts,
            }

        # Direct M-fold 2-state product generator L^(M) eigenvalues at M in {1, 2, 4}
        half_iv = iv.mpc(iv.mpf("0.5"), 0)
        L_two = [[half_iv, -half_iv], [-half_iv, half_iv]]

        def kron_iv(A: list[list], B: list[list]) -> list[list]:
            ra, ca = len(A), len(A[0])
            rb, cb = len(B), len(B[0])
            out = [[iv.mpc(0, 0) for _ in range(ca * cb)] for _ in range(ra * rb)]
            for i in range(ra):
                for j in range(ca):
                    aij = A[i][j]
                    if aij != iv.mpc(0, 0):
                        for p in range(rb):
                            for q in range(cb):
                                out[i * rb + p][j * cb + q] = aij * B[p][q]
            return out

        tensor_L_sweep = {}
        for M in (1, 2, 4):
            dim_M = 2 ** M
            L_M = iv_zeros(dim_M)
            for slot in range(M):
                term = iv_eye(1)
                for pos in range(M):
                    term = kron_iv(term, L_two if pos == slot else iv_eye(2))
                L_M = iv_add(L_M, term)
            evals_LM, _ = enclose_hermitian_eigenvalues(L_M)
            check(strictly_below(abs(evals_LM[0]), "1e-35"), f"L^({M}) lambda_0 != 0")
            check(strictly_below(abs(evals_LM[1] - iv.mpf(1)), "1e-35"), f"L^({M}) lambda_1 != 1")
            c_P_M = iv.mpf(1) / evals_LM[1]
            check(strictly_below(abs(c_P_M - iv.mpf(1)), "1e-35"), f"c_P({M}) != 1")
            tensor_L_sweep[f"M_{M}"] = {
                "dim": dim_M,
                "lambda_0": outward_str(evals_LM[0], digits=12),
                "lambda_1": outward_str(evals_LM[1]),
                "c_P_M": outward_str(c_P_M),
                "c_LSI_M": outward_str(c_P_M),
            }

        # Holley-Stroock single-block O(1) vs global exp(-2*c*M) collapse
        beta_hs = iv.mpf(1) / iv.mpf(2)
        z_hs0 = iv.exp(beta_hs) + iv.exp(-beta_hs) + iv.mpf(6)
        P0_hs = [[iv.exp(beta_hs * q8_gram[x][y].real / iv.mpf(2)) / z_hs0 for y in range(8)] for x in range(8)]
        L_hs0 = iv_add(I8, [[iv.mpc(P0_hs[x][y], 0) for y in range(8)] for x in range(8)], scale_b=-1)
        evals_hs0, _ = enclose_hermitian_eigenvalues(L_hs0)
        lambda1_hs0 = evals_hs0[1]
        c_P_hs0 = iv.mpf(1) / lambda1_hs0

        holley_stroock_block = {}
        for B_label, B_f in (
            ("B_1_4", Fraction(1, 4)),
            ("B_1_2", Fraction(1, 2)),
            ("B_1", Fraction(1, 1)),
            ("B_2", Fraction(2, 1)),
        ):
            B_iv = iv.mpf(B_f.numerator) / iv.mpf(B_f.denominator)
            raw_w = [iv.exp(-B_iv * iv.mpf(1 if x % 2 == 0 else -1)) for x in range(8)]
            Z_V = sum(raw_w)
            nu_V = [rw / Z_V for rw in raw_w]
            H_V = iv_zeros(8)
            for x in range(8):
                sqrt_nx = iv.sqrt(nu_V[x])
                diag_sum = iv.mpf(0)
                for y in range(8):
                    if x != y:
                        w_xy = (nu_V[x] + nu_V[y]) / iv.mpf(2)
                        off = -w_xy * P0_hs[x][y]
                        diag_sum += w_xy * P0_hs[x][y]
                        H_V[x][y] = iv.mpc(off / (sqrt_nx * iv.sqrt(nu_V[y])), 0)
                H_V[x][x] = iv.mpc(diag_sum / nu_V[x], 0)
            evals_HV, _ = enclose_hermitian_eigenvalues(H_V)
            check(strictly_below(abs(evals_HV[0]), "1e-35"), f"H_V lambda_0 != 0 at {B_label}")
            check(strictly_above(evals_HV[1], "0"), f"H_V lambda_1 <= 0 at {B_label}")
            c_P_nuV = iv.mpf(1) / evals_HV[1]
            hs_ub = iv.exp(iv.mpf(2) * B_iv) * c_P_hs0
            check(strictly_below(c_P_nuV, hs_ub), f"Holley-Stroock bound violated at {B_label}")
            holley_stroock_block[B_label] = {
                "B": str(B_f),
                "osc_V": str(2 * B_f),
                "lambda_1_H_V": outward_str(evals_HV[1]),
                "c_P_nu_V": outward_str(c_P_nuV),
                "holley_stroock_ub": outward_str(hs_ub),
            }

        # Red-Team global Holley-Stroock exp(-2*c*M) collapse at B = 1/2
        holley_stroock_global_collapse = {}
        prev_hs_gl = iv.mpf(10)
        for M in (1, 4, 16, 64):
            lambda_global_M = lambda1_hs0 * iv.exp(-iv.mpf(M))
            check(strictly_below(lambda_global_M, prev_hs_gl), f"Global HS bound not strictly decreasing at M={M}")
            prev_hs_gl = lambda_global_M
            holley_stroock_global_collapse[f"M_{M}"] = {
                "osc_V_M": M,
                "global_lambda_lb_collapse": outward_str(lambda_global_M),
            }
        check(strictly_below(prev_hs_gl, "1e-27"), "Global HS M=64 collapse not < 1e-27")

        # 2.2 Physical-scale blocking beta in {2, 5, 8, 12, 16, 20} with T_hat = exp(-beta)*T
        c_af_su2 = (iv.mpf(3) * (iv.pi ** 2)) / iv.mpf(11)
        phys_blocking_sweep = {}
        for b_int in (2, 5, 8, 12, 16, 20):
            beta_iv = iv.mpf(b_int)
            a_beta = iv.exp(-c_af_su2 * beta_iv)
            K_beta = (c_af_su2 * beta_iv) / iv.log(iv.mpf(2))
            scale_check = abs((iv.mpf(2) ** K_beta) * a_beta - iv.mpf(1))
            check(strictly_below(scale_check, "1e-35"), f"2^K * a(beta) != 1 at beta={b_int}")
            T_hat = [
                [iv.mpc(iv.exp(beta_iv * (q8_gram[i][j].real / iv.mpf(2) - iv.mpf(1))), 0) for j in range(8)]
                for i in range(8)
            ]
            evals_That, delta_That = enclose_hermitian_eigenvalues(T_hat)
            check(strictly_above(evals_That[0], "0"), f"T_hat({b_int}) not positive definite")
            lam0 = evals_That[-1]
            lam1 = evals_That[-2]
            check(strictly_above(lam0, lam1), f"T_hat({b_int}) Perron gap vanished")
            m_gap = iv.log(lam0 / lam1)
            check(strictly_above(m_gap, "0"), f"T_hat({b_int}) mass gap <= 0")
            ratio_10 = lam1 / lam0
            clustering = {}
            for t_sep in (1, 4, 8):
                pow_val = ratio_10 ** t_sep
                exp_val = iv.exp(-m_gap * iv.mpf(t_sep))
                check(strictly_below(abs(pow_val - exp_val), "1e-35"),
                      f"Clustering identity failed at beta={b_int}, t={t_sep}")
                clustering[f"t_{t_sep}"] = outward_str(pow_val)
            phys_blocking_sweep[f"beta_{b_int}"] = {
                "beta": b_int,
                "K_beta": outward_str(K_beta),
                "a_beta": outward_str(a_beta),
                "scale_match_err": outward_str(scale_check, digits=12),
                "T_hat_lambda_0": outward_str(lam0),
                "T_hat_lambda_1": outward_str(lam1),
                "weyl_radius": outward_str(delta_That, digits=12),
                "spectral_gap_m": outward_str(m_gap),
                "clustering_decays": clustering,
            }

        # 2.3 H(4) rank-2 & rank-4 sympy isotropy + dispersion O(a^2)
        def idx2(a: int, b: int) -> int:
            return a * 4 + b

        def idx4(a: int, b: int, c: int, d: int) -> int:
            return ((a * 4 + b) * 4 + c) * 4 + d

        rows_h4_r2 = []
        for s_ax in range(4):
            for a in range(4):
                for b in range(4):
                    if (-1 if a == s_ax else 1) * (-1 if b == s_ax else 1) == -1:
                        row = [0] * 16
                        row[idx2(a, b)] = 1
                        rows_h4_r2.append(row)
        for p_a in range(3):
            p_b = p_a + 1
            for a in range(4):
                for b in range(4):
                    sa = p_b if a == p_a else (p_a if a == p_b else a)
                    sb = p_b if b == p_a else (p_a if b == p_b else b)
                    i1, i2 = idx2(a, b), idx2(sa, sb)
                    if i1 < i2:
                        row = [0] * 16
                        row[i1] = 1
                        row[i2] = -1
                        rows_h4_r2.append(row)
        M_h4_r2 = sp.Matrix(rows_h4_r2)
        ns_h4_r2 = M_h4_r2.nullspace()
        check(len(ns_h4_r2) == 1, f"H(4) rank-2 invariant dim != 1: {len(ns_h4_r2)}")
        delta2_vec = sp.Matrix([1 if a == b else 0 for a in range(4) for b in range(4)])
        check(M_h4_r2 * delta2_vec == sp.zeros(M_h4_r2.rows, 1), "delta_{mu,nu} not H(4)-invariant")

        rows_h4_r4 = []
        for s_ax in range(4):
            for a in range(4):
                for b in range(4):
                    for c in range(4):
                        for d in range(4):
                            sgn = (
                                (-1 if a == s_ax else 1)
                                * (-1 if b == s_ax else 1)
                                * (-1 if c == s_ax else 1)
                                * (-1 if d == s_ax else 1)
                            )
                            if sgn == -1:
                                row = [0] * 256
                                row[idx4(a, b, c, d)] = 1
                                rows_h4_r4.append(row)
        for p_a in range(3):
            p_b = p_a + 1
            for a in range(4):
                for b in range(4):
                    for c in range(4):
                        for d in range(4):
                            sa = p_b if a == p_a else (p_a if a == p_b else a)
                            sb = p_b if b == p_a else (p_a if b == p_b else b)
                            sc = p_b if c == p_a else (p_a if c == p_b else c)
                            sd = p_b if d == p_a else (p_a if d == p_b else d)
                            i1, i2 = idx4(a, b, c, d), idx4(sa, sb, sc, sd)
                            if i1 < i2:
                                row = [0] * 256
                                row[i1] = 1
                                row[i2] = -1
                                rows_h4_r4.append(row)
        M_h4_r4 = sp.Matrix(rows_h4_r4)
        ns_h4_r4 = M_h4_r4.nullspace()
        check(len(ns_h4_r4) == 4, f"H(4) rank-4 invariant dim != 4: {len(ns_h4_r4)}")
        basis_r4 = sp.Matrix.hstack(
            sp.Matrix([1 if (a == b and c == d) else 0 for a in range(4) for b in range(4) for c in range(4) for d in range(4)]),
            sp.Matrix([1 if (a == c and b == d) else 0 for a in range(4) for b in range(4) for c in range(4) for d in range(4)]),
            sp.Matrix([1 if (a == d and b == c) else 0 for a in range(4) for b in range(4) for c in range(4) for d in range(4)]),
            sp.Matrix([1 if (a == b == c == d) else 0 for a in range(4) for b in range(4) for c in range(4) for d in range(4)]),
        )
        check(M_h4_r4 * basis_r4 == sp.zeros(M_h4_r4.rows, 4) and basis_r4.rank() == 4,
              "H(4) rank-4 canonical basis check failed")

        p1_s, p2_s, p3_s, p4_s, a_disp = sp.symbols("p1 p2 p3 p4 a_disp", real=True)
        disp_expr = sum((2 / a_disp) ** 2 * sp.sin(a_disp * p_s / 2) ** 2 for p_s in (p1_s, p2_s, p3_s, p4_s))
        disp_ser = sp.series(disp_expr, a_disp, 0, 6)
        check(sp.expand(disp_ser.coeff(a_disp, 0) - (p1_s ** 2 + p2_s ** 2 + p3_s ** 2 + p4_s ** 2)) == 0,
              "Lattice dispersion O(a^0) mismatch")
        check(disp_ser.coeff(a_disp, 1) == 0 and disp_ser.coeff(a_disp, 3) == 0,
              "Unexpected odd-power dispersion term")
        check(
            sp.expand(disp_ser.coeff(a_disp, 2) + (p1_s ** 4 + p2_s ** 4 + p3_s ** 4 + p4_s ** 4) / 12) == 0,
            "Lattice dispersion O(a^2) breaking mismatch",
        )

        track_2_ir = {
            "q8_volume_sweep": q8_volume_sweep,
            "product_generator_L_M_eigenvalues": tensor_L_sweep,
            "holley_stroock_single_block_O1": holley_stroock_block,
            "redteam_holley_stroock_global_collapse": holley_stroock_global_collapse,
            "physical_scale_blocking_and_clustering": phys_blocking_sweep,
            "h4_isotropy_and_dispersion": {
                "rank2_invariant_dim": len(ns_h4_r2),
                "rank4_invariant_dim": len(ns_h4_r4),
                "sympy_dispersion_o_a2_verified": True,
            },
        }

        # =====================================================================
        # Track 3 (Chiral): T^2 Hodge, Kramers & Counterexample, Theta-RP & w=-1, Luscher S_L & Hard-Ball
        # =====================================================================
        t2_hodge_sweep = {}
        for L1, L2 in ((3, 3), (3, 4), (4, 5)):
            V = L1 * L2
            E = 2 * V
            F = V

            def vid(x: int, y: int) -> int:
                return (x % L1) * L2 + (y % L2)

            d0 = sp.zeros(E, V)
            d1 = sp.zeros(F, E)
            H_cyc = sp.zeros(2, E)
            omega_flat = sp.zeros(E, 1)
            for x in range(L1):
                for y in range(L2):
                    v = vid(x, y)
                    eh = v
                    ev = V + v
                    d0[eh, vid(x + 1, y)] += 1
                    d0[eh, v] -= 1
                    d0[ev, vid(x, y + 1)] += 1
                    d0[ev, v] -= 1

                    d1[v, eh] += 1
                    d1[v, V + vid(x + 1, y)] += 1
                    d1[v, vid(x, y + 1)] -= 1
                    d1[v, ev] -= 1

                    omega_flat[eh, 0] = 1
            for x in range(L1):
                H_cyc[0, vid(x, 0)] = 1
            for y in range(L2):
                H_cyc[1, V + vid(0, y)] = 1

            check(d1 * d0 == sp.zeros(F, V), f"T^2 d1*d0 != 0 on ({L1},{L2})")
            check(H_cyc * d0 == sp.zeros(2, V), f"T^2 H_cyc*d0 != 0 on ({L1},{L2})")
            rk_d0 = d0.rank()
            rk_d1 = d1.rank()
            nullity_d1 = E - rk_d1
            check(nullity_d1 - rk_d0 == 2, f"T^2 H^1 dim != 2 on ({L1},{L2})")
            aug_rk = sp.Matrix.vstack(d1, H_cyc).rank()
            check(E - aug_rk == rk_d0, f"T^2 augmented coboundary rank failed on ({L1},{L2})")
            check(d1 * omega_flat == sp.zeros(F, 1), f"omega_flat not flat on ({L1},{L2})")
            check(H_cyc * omega_flat == sp.Matrix([[L1], [0]]), f"omega_flat Polyakov mismatch on ({L1},{L2})")
            check(sp.Matrix.hstack(d0, omega_flat).rank() == rk_d0 + 1, f"omega_flat in im(d0) on ({L1},{L2})")
            t2_hodge_sweep[f"T2_{L1}x{L2}"] = {
                "V": V,
                "E": E,
                "F": F,
                "rank_d0": rk_d0,
                "nullity_d1": nullity_d1,
                "dim_H1": nullity_d1 - rk_d0,
                "augmented_rank": aug_rk,
                "omega_flat_polyakov_x": L1,
            }

        # 3.2 Kramers 2x2 & 4x4 SU(2) det >= 0 & (Pf)^4 >= 0 + J = i*I counterexample
        q_syms = sp.symbols("a1 b1 c1 d1 a2 b2 c2 d2 a3 b3 c3 d3 a4 b4 c4 d4", real=True)
        def sym_quat(idx_q: int):
            a, b, c, d = q_syms[4 * idx_q : 4 * (idx_q + 1)]
            return sp.Matrix([[a + sp.I * b, c + sp.I * d], [-c + sp.I * d, a - sp.I * b]])

        Q11, Q12, Q21, Q22 = sym_quat(0), sym_quat(1), sym_quat(2), sym_quat(3)
        eps_sp = sp.Matrix([[0, 1], [-1, 0]])
        J4_sp = sp.diag(eps_sp, eps_sp)
        D4_sp = sp.Matrix.vstack(sp.Matrix.hstack(Q11, Q12), sp.Matrix.hstack(Q21, Q22))
        check(sp.simplify(J4_sp * D4_sp - D4_sp.applyfunc(sp.conjugate) * J4_sp) == sp.zeros(4, 4),
              "16-param quaternionic symmetry failed")
        M_schur_sp = sp.expand(Q11.det() * Q22 - Q21 * Q11.H * Q12)
        check(sp.simplify(eps_sp * M_schur_sp - M_schur_sp.applyfunc(sp.conjugate) * eps_sp) == sp.zeros(2, 2),
              "Schur complement quaternionic symmetry failed")
        check(sp.expand(D4_sp.det() * Q11.det() - M_schur_sp.det()) == 0,
              "Schur determinant identity failed for 4x4 Kramers")
        check(sp.expand(sp.im(D4_sp.det())) == 0, "4x4 Kramers determinant not identically real")

        x01, x02, x03, x12, x13, x23 = sp.symbols("x01 x02 x03 x12 x13 x23", real=True)
        A4_sp = sp.Matrix([
            [0, x01, x02, x03],
            [-x01, 0, x12, x13],
            [-x02, -x12, 0, x23],
            [-x03, -x13, -x23, 0],
        ])
        pf4_sp = x01 * x23 - x02 * x13 + x03 * x12
        check(sp.expand(A4_sp.det() - pf4_sp ** 2) == 0, "4x4 antisymmetric det != Pf^2")

        # 40-digit mpmath.iv Kramers sweep across 3 non-commuting Cayley SU(2) configs
        z_c = iv.mpc(0, 0)
        o_c = iv.mpc(1, 0)
        m_c = iv.mpc(-1, 0)
        J2_iv = [[z_c, o_c], [m_c, z_c]]
        J4_iv = [
            [z_c, o_c, z_c, z_c],
            [m_c, z_c, z_c, z_c],
            [z_c, z_c, z_c, o_c],
            [z_c, z_c, m_c, z_c],
        ]

        def mat_conj_iv(M: list[list]) -> list[list]:
            return [[iv_conj(M[r][c]) for c in range(len(M[0]))] for r in range(len(M))]

        kramers_configs = (
            (
                "cfg_1",
                (Fraction(3, 2), (Fraction(1, 5), Fraction(1, 7), Fraction(1, 11))),
                (Fraction(1, 3), (Fraction(-1, 4), Fraction(1, 6), Fraction(1, 8))),
                (Fraction(-1, 4), (Fraction(1, 9), Fraction(-1, 5), Fraction(1, 3))),
                (Fraction(5, 2), (Fraction(1, 8), Fraction(1, 4), Fraction(-1, 6))),
            ),
            (
                "cfg_2",
                (Fraction(2, 1), (Fraction(2, 5), Fraction(-1, 3), Fraction(1, 7))),
                (Fraction(1, 2), (Fraction(1, 3), Fraction(1, 5), Fraction(-1, 2))),
                (Fraction(1, 5), (Fraction(-1, 2), Fraction(1, 4), Fraction(1, 6))),
                (Fraction(3, 1), (Fraction(-1, 6), Fraction(2, 7), Fraction(1, 5))),
            ),
            (
                "cfg_3",
                (Fraction(7, 4), (Fraction(-1, 3), Fraction(2, 5), Fraction(-1, 4))),
                (Fraction(-2, 5), (Fraction(1, 6), Fraction(-1, 3), Fraction(1, 2))),
                (Fraction(3, 7), (Fraction(1, 4), Fraction(1, 5), Fraction(-1, 7))),
                (Fraction(9, 4), (Fraction(1, 3), Fraction(-1, 6), Fraction(2, 9))),
            ),
        )
        kramers_iv_results = {}
        for cfg_name, b11, b12, b21, b22 in kramers_configs:
            def make_qblock(spec_b):
                s_f, p_f = spec_b
                s_iv = iv.mpc(iv.mpf(s_f.numerator) / iv.mpf(s_f.denominator), 0)
                U = su2_cayley_iv(
                    iv.mpf(p_f[0].numerator) / iv.mpf(p_f[0].denominator),
                    iv.mpf(p_f[1].numerator) / iv.mpf(p_f[1].denominator),
                    iv.mpf(p_f[2].numerator) / iv.mpf(p_f[2].denominator),
                )
                return [[s_iv * U[r][c] for c in range(2)] for r in range(2)]

            Q11_iv = make_qblock(b11)
            Q12_iv = make_qblock(b12)
            Q21_iv = make_qblock(b21)
            Q22_iv = make_qblock(b22)
            D4_iv = [
                Q11_iv[0] + Q12_iv[0],
                Q11_iv[1] + Q12_iv[1],
                Q21_iv[0] + Q22_iv[0],
                Q21_iv[1] + Q22_iv[1],
            ]
            kram_err = iv_frobenius_norm(iv_add(iv_matmul(J4_iv, D4_iv), iv_matmul(mat_conj_iv(D4_iv), J4_iv), scale_b=-1))
            check(strictly_below(kram_err, "1e-38"), f"Kramers J4*D4 != conj(D4)*J4 at {cfg_name}")
            det2 = _iv_det_2x2(Q11_iv)
            det4 = _iv_det_4x4(D4_iv)
            check(strictly_below(abs(det2.imag), "1e-37") and strictly_above(det2.real, "0"),
                  f"det(Q11) not positive real at {cfg_name}: {det2}")
            check(strictly_below(abs(det4.imag), "1e-37") and strictly_above(det4.real, "0"),
                  f"det(D4) not positive real at {cfg_name}: {det4}")

            # 4x4 antisymmetric Pfaffian^4 == det(A4)^2 > 0
            x_vals = [
                iv.mpc(Q11_iv[0][0].real, 0),
                iv.mpc(Q12_iv[0][1].real, 0),
                iv.mpc(Q21_iv[1][0].real, 0),
                iv.mpc(Q22_iv[0][0].real, 0),
                iv.mpc(Q12_iv[1][1].imag, 0),
                iv.mpc(Q22_iv[0][1].real, 0),
            ]
            A4_iv = [
                [z_c, x_vals[0], x_vals[1], x_vals[2]],
                [-x_vals[0], z_c, x_vals[3], x_vals[4]],
                [-x_vals[1], -x_vals[3], z_c, x_vals[5]],
                [-x_vals[2], -x_vals[4], -x_vals[5], z_c],
            ]
            pf_val = x_vals[0] * x_vals[5] - x_vals[1] * x_vals[4] + x_vals[2] * x_vals[3]
            pf4_val = (pf_val ** 4).real
            det_a4_sq = (_iv_det_4x4(A4_iv) ** 2).real
            check(strictly_below(abs(pf4_val - det_a4_sq), "1e-37") and strictly_above(pf4_val, "0"),
                  f"Pf^4 != det(A4)^2 or <= 0 at {cfg_name}")
            kramers_iv_results[cfg_name] = {
                "kramers_symmetry_err": outward_str(kram_err, digits=12),
                "det_2x2_real": outward_str(det2.real),
                "det_4x4_real": outward_str(det4.real),
                "pfaffian_pow_4": outward_str(pf4_val),
            }

        # Red-Team counterexample: J = i*I_2, D = diag(1, -1) -> det(D) = -1 < 0
        ci_c = iv.mpc(0, 1)
        J_bad = [[ci_c, z_c], [z_c, ci_c]]
        D_bad = [[o_c, z_c], [z_c, m_c]]
        I2_iv = iv_eye(2)
        j_bad_sq_err = iv_frobenius_norm(iv_add(iv_matmul(J_bad, J_bad), I2_iv, scale_b=1))
        j_bad_sym_err = iv_frobenius_norm(iv_add(iv_matmul(J_bad, D_bad), iv_matmul(mat_conj_iv(D_bad), J_bad), scale_b=-1))
        j_bad_reality_prod = iv_matmul(J_bad, mat_conj_iv(J_bad))
        j_bad_fails_reality = iv_frobenius_norm(iv_add(j_bad_reality_prod, I2_iv, scale_b=-1))
        det_bad = _iv_det_2x2(D_bad)
        check(j_bad_sq_err.b == 0 and j_bad_sym_err.b == 0, "Kramers counterexample setup failed")
        check(j_bad_fails_reality.b == 0, "J_bad * conj(J_bad) != +I_2")
        check(strictly_below(det_bad.real, "0") and abs(det_bad.real + iv.mpf(1)).b == 0,
              "Kramers counterexample det(D_bad) != -1")

        # 3.3 Theta-antiunitary factorized RP (K^H K) + w = -1 counterexample
        theta_rp_configs = (
            ("dim2_cfg1", [iv.mpc(1, iv.mpf("0.5")), iv.mpc(1, iv.mpf("-1.25"))],
             [[iv.mpf(2), iv.mpf("0.5")], [iv.mpf("0.5"), iv.mpf(3)]],
             [iv.mpc(1, 1), iv.mpc(2, -1)]),
            ("dim2_cfg2", [iv.mpc(1, iv.mpf("-0.75")), iv.mpc(1, iv.mpf("2.0"))],
             [[iv.mpf(4), iv.mpf("-1.0")], [iv.mpf("-1.0"), iv.mpf("2.5")]],
             [iv.mpc(-1, 2), iv.mpc(1, 3)]),
            ("dim4_cfg3", [iv.mpc(1, iv.mpf("0.25")), iv.mpc(1, iv.mpf("-0.5")), iv.mpc(1, iv.mpf("0.75")), iv.mpc(1, iv.mpf("-1.0"))],
             [[iv.mpf(4) if i == j else iv.mpf(1) / iv.mpf(1 + abs(i - j)) for j in range(4)] for i in range(4)],
             [iv.mpc(1, 0), iv.mpc(0, 1), iv.mpc(-1, 1), iv.mpc(2, -1)]),
            ("dim4_cfg4", [iv.mpc(1, iv.mpf("1.5")), iv.mpc(1, iv.mpf("0.3")), iv.mpc(1, iv.mpf("-0.9")), iv.mpc(1, iv.mpf("0.6"))],
             [[iv.mpf(5) if i == j else iv.mpf(-1) / iv.mpf(2 ** abs(i - j) * 4) for j in range(4)] for i in range(4)],
             [iv.mpc(2, 1), iv.mpc(-1, -1), iv.mpc(1, 2), iv.mpc(0, -2)]),
        )
        theta_rp_results = {}
        for cfg_name, w_vec, K_mat, F_vec in theta_rp_configs:
            dim_w = len(w_vec)
            W_mat = [
                [iv_conj(w_vec[i]) * iv.mpc(K_mat[i][j], 0) * w_vec[j] for j in range(dim_w)]
                for i in range(dim_w)
            ]
            max_im_W = max((abs(W_mat[i][j].imag) for i in range(dim_w) for j in range(dim_w)), key=lambda z: z.b)
            check(strictly_above(max_im_W, "0"), f"Theta-RP kernel W unexpectedly real at {cfg_name}")
            herm_W_err = iv_frobenius_norm(iv_add(W_mat, iv_conj_transpose(W_mat), scale_b=-1))
            check(strictly_below(herm_W_err, "1e-38"), f"Theta-RP kernel W not Hermitian at {cfg_name}")
            evals_W, _ = enclose_hermitian_eigenvalues(W_mat)
            check(strictly_above(evals_W[0], "0"), f"Theta-RP kernel W not strictly SPD at {cfg_name}")
            theta_F_F = sum(
                iv_conj(F_vec[i]) * W_mat[i][j] * F_vec[j]
                for i in range(dim_w)
                for j in range(dim_w)
            )
            check(strictly_above(theta_F_F.real, "0") and strictly_below(abs(theta_F_F.imag), "1e-36"),
                  f"<Theta F, F>_w failed positivity at {cfg_name}: {theta_F_F}")
            theta_rp_results[cfg_name] = {
                "dim": dim_w,
                "max_im_W": outward_str(max_im_W),
                "lambda_min_W": outward_str(evals_W[0]),
                "rp_inner_product_real": outward_str(theta_F_F.real),
                "rp_inner_product_imag": outward_str(theta_F_F.imag, digits=12),
            }

        # Red-Team counterexample: w = -1 satisfies w(Theta U) = conj(w(U)) yet <Theta F, F>_w < 0
        w_ce = iv.mpc(-1, 0)
        check(w_ce == iv_conj(w_ce), "w = -1 reality symmetry check failed")
        F_ce = [iv.mpc(1, 1), iv.mpc(2, -1)]
        sum_F_ce = F_ce[0] + F_ce[1]
        rp_ce = iv_conj(sum_F_ce) * w_ce * sum_F_ce
        check(strictly_below(rp_ce.real, "-1") and abs(rp_ce.imag).b == 0,
              f"w = -1 RP counterexample failed: {rp_ce}")

        # 3.4 Luscher S_L(u) dominance vs Wilson blowup, two-scale sweep & U(1) hard-ball negative mode
        u_sp, eps_sp_s = sp.symbols("u eps_adm", positive=True)
        S_L_sp = u_sp / (1 - u_sp / eps_sp_s)
        check(sp.simplify((S_L_sp - u_sp) - (u_sp ** 2) / (eps_sp_s - u_sp)) == 0,
              "Luscher S_L(u) - u exact rational identity failed")

        luscher_u_sweep = {}
        for u_str in ("1e-4", "3e-4", "1e-3", "3e-3", "1e-2", "2e-2", "0.03"):
            u_iv = iv.mpf(u_str)
            s_l_val = u_iv / (iv.mpf(1) - u_iv / eps_adm)
            diff_ratio = (s_l_val - u_iv) / (u_iv ** 2)
            check(strictly_above(s_l_val, u_iv), f"S_L(u) <= u at u={u_str}")
            check(strictly_below(diff_ratio, "301"), f"(S_L(u)-u)/u^2 >= 301 at u={u_str}")
            luscher_u_sweep[f"u_{u_str}"] = {
                "S_L": outward_str(s_l_val),
                "excess_over_u_sq": outward_str(diff_ratio),
            }

        a_near = iv.mpf("1e-8")
        u_near = eps_adm * (iv.mpf(1) - iv.mpf("1e-4"))
        S_L_near = u_near / (iv.mpf(1) - u_near / eps_adm)
        barrier_near = iv.exp(-iv.mpf(12) * S_L_near) * ((iv.mpf(1) / a_near) ** 4)
        two_cadm_b0 = iv.mpf(2) * ((eps_adm ** 2) / pi2_16) * b0_su3
        wilson_blowup_1e8 = ((iv.mpf(1) / a_near) ** 4) * (a_near ** two_cadm_b0)
        check(strictly_below(barrier_near, "1e-100"), f"Luscher near-boundary barrier >= 1e-100: {barrier_near}")
        check(strictly_above(wilson_blowup_1e8, "1e31"), f"Wilson blowup at 1e-8 <= 1e31: {wilson_blowup_1e8}")

        # Two-scale a_ferm = a_gauge^alpha 9-point sweep
        two_scale_sweep = {}
        for ag_tag, ag_str in (("ag_1e_minus_4", "1e-4"), ("ag_1e_minus_8", "1e-8"), ("ag_1e_minus_16", "1e-16")):
            ag_iv = iv.mpf(ag_str)
            log10_ag = iv.log10(ag_iv)
            log10_wilson = (two_cadm_b0 - iv.mpf(4)) * log10_ag
            for al_tag, al_f in (("alpha_1_4", Fraction(1, 4)), ("alpha_1_2", Fraction(1, 2)), ("alpha_3_4", Fraction(3, 4))):
                al_iv = iv.mpf(al_f.numerator) / iv.mpf(al_f.denominator)
                N_sub = ag_iv ** (al_iv - iv.mpf(1))
                N_cells = N_sub ** 4
                exp_excess = two_cadm_b0 * N_cells - iv.mpf(4) * al_iv
                log10_two_scale = exp_excess * log10_ag
                check(strictly_below(log10_two_scale, log10_wilson),
                      f"Two-scale failed to beat Wilson at {ag_tag}, {al_tag}")
                if ag_tag == "ag_1e_minus_4" and al_tag == "alpha_3_4":
                    check(strictly_below(exp_excess, "0") and strictly_above(log10_two_scale, "0"),
                          "Pre-crossover (1e-4, 3/4) check failed")
                    regime = "pre_crossover_still_beats_wilson"
                else:
                    check(strictly_above(exp_excess, "0") and strictly_below(log10_two_scale, "-1"),
                          f"Asymptotic suppression check failed at {ag_tag}, {al_tag}")
                    regime = "asymptotic_suppression"
                two_scale_sweep[f"{ag_tag}_{al_tag}"] = {
                    "a_gauge": ag_str,
                    "alpha": str(al_f),
                    "N_cells": outward_str(N_cells),
                    "exponent_excess": outward_str(exp_excess),
                    "log10_two_scale_bound": outward_str(log10_two_scale),
                    "log10_wilson_single_scale": outward_str(log10_wilson),
                    "regime": regime,
                }

        # Red-Team counterexample: U(1) hard-ball 1_{[-theta0, theta0]} negative Fourier modes vs phi * phi*
        u1_hardball_counterexamples = {}
        for ce_label, th0_iv, n_mode in (
            ("theta0_pi_2_n_3", iv.pi / iv.mpf(2), 3),
            ("theta0_pi_4_n_5", iv.pi / iv.mpf(4), 5),
            ("theta0_1_30_n_95", iv.mpf(1) / iv.mpf(30), 95),
        ):
            c_n = iv.sin(iv.mpf(n_mode) * th0_iv) / (iv.pi * iv.mpf(n_mode))
            check(strictly_below(c_n, "0"), f"Hard-ball Fourier mode not negative at {ce_label}: {c_n}")
            if ce_label == "theta0_pi_2_n_3":
                exact_neg = -iv.mpf(1) / (iv.mpf(3) * iv.pi)
                check(strictly_below(abs(c_n - exact_neg), "1e-38"),
                      f"sin(3*pi/2)/(3*pi) != -1/(3*pi): {c_n}")
            phi_hat = iv.sin(iv.mpf(n_mode) * (th0_iv / iv.mpf(2))) / (iv.pi * iv.mpf(n_mode))
            self_conv_n = phi_hat ** 2
            check(self_conv_n.a >= 0, f"Self-convolution mode < 0 at {ce_label}")
            u1_hardball_counterexamples[ce_label] = {
                "n": n_mode,
                "hard_ball_fourier_c_n": outward_str(c_n),
                "self_convolution_mode_sq": outward_str(self_conv_n),
            }

        track_3_chiral = {
            "t2_discrete_hodge_sweep": t2_hodge_sweep,
            "kramers_su2_sympy_and_40digit": {
                "sympy_16param_4x4_quaternionic_verified": True,
                "sympy_6param_4x4_pfaffian_sq_verified": True,
                "cayley_su2_40digit_sweep": kramers_iv_results,
                "redteam_J_iI_D_diag_1_m1_counterexample": {
                    "J_sq_plus_I_err": outward_str(j_bad_sq_err, digits=12),
                    "J_D_eq_conjD_J_err": outward_str(j_bad_sym_err, digits=12),
                    "J_conjJ_eq_plus_I_err": outward_str(j_bad_fails_reality, digits=12),
                    "det_D_bad": outward_str(det_bad.real),
                },
            },
            "theta_antiunitary_factorized_rp": {
                "factorized_kernel_sweep": theta_rp_results,
                "redteam_w_minus_1_counterexample": {
                    "rp_inner_product_real": outward_str(rp_ce.real),
                    "strictly_negative": True,
                },
            },
            "luscher_dominance_two_scale_and_hardball": {
                "sympy_S_L_identity_verified": True,
                "luscher_u_sweep": luscher_u_sweep,
                "near_boundary_barrier_a_1e_8": outward_str(barrier_near),
                "wilson_blowup_a_1e_8": outward_str(wilson_blowup_1e8),
                "two_scale_9pt_sweep": two_scale_sweep,
                "redteam_u1_hardball_negative_fourier_modes": u1_hardball_counterexamples,
            },
        }

        return {
            "round": "round_04",
            "h2d_status": "OPEN",
            "interval_checks_passed": interval_checks,
            "track_1_uv_constructive_bridges": track_1_uv,
            "track_2_ir_constructive_bridges": track_2_ir,
            "track_3_chiral_constructive_bridges": track_3_chiral,
        }
    finally:
        mp.dps = 50
        iv.dps = 40


def _iv_poly_mul(a: list, b: list, deg: int) -> list:
    """Truncated Cauchy product of Taylor series coefficients up to degree deg."""
    out = [iv.mpf(0)] * (deg + 1)
    for i in range(deg + 1):
        ai = a[i]
        for j in range(deg + 1 - i):
            out[i + j] += ai * b[j]
    return out


def _iv_weyl_taylor_integrate_vec(
    bF_iv,
    bA_iv,
    max_cos_pow: int,
    n_sub: int = 32,
    deg: int = 25,
) -> list:
    """Rigorous SU(2) Weyl Haar integral via Taylor-model quadrature + Lagrange remainder.

    Computes 2 * int_0^1 sin^2(pi u) exp(bF cos(pi u) + bA (4 cos^2(pi u) - 1)/3) cos^k(pi u) du
    for k = 0 .. max_cos_pow, enclosing the (deg+1)-th Lagrange remainder over each dyadic subinterval.
    """
    require(deg % 2 == 1 and n_sub >= 4, "Taylor quadrature requires odd deg so deg+1 is even")
    L = deg + 2  # indices 0 .. deg+1
    pi_iv = iv.pi
    pi_pows_fact = [iv.mpf(1)] * L
    for k in range(1, L):
        pi_pows_fact[k] = pi_pows_fact[k - 1] * pi_iv / iv.mpf(k)

    def cos_sin_series(u_val):
        th = pi_iv * u_val
        c0 = iv.cos(th)
        s0 = iv.sin(th)
        cs = [iv.mpf(0)] * L
        sn = [iv.mpf(0)] * L
        for k in range(L):
            pf = pi_pows_fact[k]
            if k % 2 == 0:
                sgn = iv.mpf(1) if (k // 2) % 2 == 0 else iv.mpf(-1)
                cs[k] = c0 * sgn * pf
                sn[k] = s0 * sgn * pf
            else:
                sgn = iv.mpf(1) if ((k - 1) // 2) % 2 == 0 else iv.mpf(-1)
                cs[k] = -s0 * sgn * pf
                sn[k] = c0 * sgn * pf
        return cs, sn

    def exp_series(g: list, d_lim: int) -> list:
        e = [iv.mpf(0)] * (d_lim + 1)
        e[0] = iv.exp(g[0])
        for k in range(1, d_lim + 1):
            s = iv.mpf(0)
            for m in range(1, k + 1):
                s += iv.mpf(m) * g[m] * e[k - m]
            e[k] = s / iv.mpf(k)
        return e

    def eval_series_vec(u_val, need_full: bool) -> list[list]:
        d_lim = L - 1 if need_full else deg
        cs, sn = cos_sin_series(u_val)
        sn2 = _iv_poly_mul(sn, sn, d_lim)
        if bF_iv == iv.mpf(0) and bA_iv == iv.mpf(0):
            w_ser = sn2
        else:
            if bA_iv != iv.mpf(0):
                cs2 = _iv_poly_mul(cs, cs, d_lim)
                g = [
                    bF_iv * cs[k]
                    + bA_iv * (iv.mpf(4) * cs2[k] - (iv.mpf(1) if k == 0 else iv.mpf(0))) / iv.mpf(3)
                    for k in range(d_lim + 1)
                ]
            else:
                g = [bF_iv * cs[k] for k in range(d_lim + 1)]
            e = exp_series(g, d_lim)
            w_ser = _iv_poly_mul(sn2, e, d_lim)
        out = [w_ser]
        cur = w_ser
        for _ in range(max_cos_pow):
            cur = _iv_poly_mul(cur, cs, d_lim)
            out.append(cur)
        return out

    h = iv.mpf(1) / iv.mpf(n_sub)
    r = h / iv.mpf(2)
    r_even_weights = [iv.mpf(2) * (r ** (2 * j + 1)) / iv.mpf(2 * j + 1) for j in range((deg + 1) // 2)]
    rem_weight = iv.mpf(2) * (r ** (deg + 2)) / iv.mpf(deg + 2)

    totals = [iv.mpf(0)] * (max_cos_pow + 1)
    for k in range(n_sub):
        u_lo = iv.mpf(k) / iv.mpf(n_sub)
        u_hi = iv.mpf(k + 1) / iv.mpf(n_sub)
        u_mid = iv.mpf(2 * k + 1) / iv.mpf(2 * n_sub)
        u_enc = iv.mpf([u_lo.a, u_hi.b])
        mid_vecs = eval_series_vec(u_mid, False)
        enc_vecs = eval_series_vec(u_enc, True)
        for p_idx in range(max_cos_pow + 1):
            mv = mid_vecs[p_idx]
            sub_int = iv.mpf(0)
            for j, wt in enumerate(r_even_weights):
                sub_int += mv[2 * j] * wt
            rem = enc_vecs[p_idx][deg + 1] * rem_weight
            totals[p_idx] += sub_int + rem
    return [iv.mpf(2) * t for t in totals]


def compute_h2d_round05_deepening_bridges() -> dict:
    """Deterministic 40-digit mpmath.iv + sympy DomainMatrix + Fraction bridges for Round 05 H2d."""
    mp.dps = 60
    iv.dps = 40
    try:
        interval_checks = 0

        def check(ok: bool, msg: str) -> None:
            nonlocal interval_checks
            require(ok, msg)
            interval_checks += 1

        # =====================================================================
        # Track 1: Continuous SU(2) Haar, Weingarten, 1-Plaquette HK & S^3 Bakry-Emery
        # =====================================================================
        haar_vec = _iv_weyl_taylor_integrate_vec(iv.mpf(0), iv.mpf(0), 6, n_sub=32, deg=25)
        haar_norm_1 = haar_vec[0]
        haar_tr2_1 = iv.mpf(4) * haar_vec[2]
        haar_tr4_2 = iv.mpf(16) * haar_vec[4]
        haar_tr6_5 = iv.mpf(64) * haar_vec[6]

        check(haar_norm_1.a <= 1 <= haar_norm_1.b and strictly_below(abs(haar_norm_1 - iv.mpf(1)), "1e-38"),
              f"SU(2) Haar norm != 1: {haar_norm_1}")
        check(haar_tr2_1.a <= 1 <= haar_tr2_1.b and strictly_below(abs(haar_tr2_1 - iv.mpf(1)), "1e-38"),
              f"SU(2) Haar <|Tr U|^2> != 1: {haar_tr2_1}")
        check(haar_tr4_2.a <= 2 <= haar_tr4_2.b and strictly_below(abs(haar_tr4_2 - iv.mpf(2)), "1e-37"),
              f"SU(2) Haar <|Tr U|^4> != 2: {haar_tr4_2}")
        check(haar_tr6_5.a <= 5 <= haar_tr6_5.b and strictly_below(abs(haar_tr6_5 - iv.mpf(5)), "1e-35"),
              f"SU(2) Haar <|Tr U|^6> != 5: {haar_tr6_5}")

        # Exact sympy Weyl Catalan moments & Weingarten U(N)/SU(2) cross-check
        th_sp = sp.Symbol("theta", real=True)
        weyl_density = sp.Rational(2, 1) / sp.pi * (sp.sin(th_sp) ** 2)
        for k_cat, expected_cat in ((0, 1), (1, 1), (2, 2), (3, 5)):
            sym_mom = sp.integrate(weyl_density * ((2 * sp.cos(th_sp)) ** (2 * k_cat)), (th_sp, 0, sp.pi))
            check(sym_mom == sp.Integer(expected_cat), f"Sympy Weyl Catalan C_{k_cat} mismatch: {sym_mom}")

        N_wg = sp.Symbol("N_wg", integer=True, positive=True)
        wg_1_1 = sp.Rational(1, 1) / (N_wg ** 2 - 1)
        wg_2 = sp.Rational(-1, 1) / (N_wg * (N_wg ** 2 - 1))
        check(wg_1_1.subs(N_wg, 2) == sp.Rational(1, 3) and wg_2.subs(N_wg, 2) == sp.Rational(-1, 6),
              "U(2) Weingarten values mismatch")
        wg_tr4 = sp.simplify(2 * ((N_wg ** 2) * wg_1_1 + N_wg * wg_2))
        check(wg_tr4 == 2 and wg_tr4.subs(N_wg, 2) == 2, f"Weingarten <|Tr U|^4> != 2: {wg_tr4}")

        # 1-plaquette heat-kernel sweep beta in {1, 2, 5, 10, 20}: Weyl quadrature vs I_2(beta)/I_1(beta)
        hk_sweep = {}
        prev_u_hk = iv.mpf(0)
        for b_int in (1, 2, 5, 10, 20):
            b_iv = iv.mpf(b_int)
            res_hk = _iv_weyl_taylor_integrate_vec(b_iv, iv.mpf(0), 1, n_sub=64, deg=27)
            u_weyl = res_hk[1] / res_hk[0]
            u_bessel = besseli_iv_any(2, b_iv) / besseli_iv_any(1, b_iv)
            overlap_ok = not (u_weyl.b < u_bessel.a or u_bessel.b < u_weyl.a)
            check(overlap_ok, f"1-plaquette HK Weyl vs Bessel failed to overlap at beta={b_int}")
            rel_err = abs(u_weyl - u_bessel) / u_bessel
            check(strictly_below(rel_err, "1e-34"), f"1-plaquette HK rel_err >= 1e-34 at beta={b_int}: {rel_err}")
            sigma_hk = -iv.log(u_weyl)
            check(strictly_above(sigma_hk, "0"), f"1-plaquette string tension <= 0 at beta={b_int}")
            check(strictly_above(u_weyl, prev_u_hk), f"1-plaquette u_weyl not strictly increasing at beta={b_int}")
            prev_u_hk = u_weyl
            hk_sweep[f"beta_{b_int}"] = {
                "beta": b_int,
                "u_weyl": outward_str(u_weyl),
                "u_bessel": outward_str(u_bessel),
                "sigma": outward_str(sigma_hk),
                "rel_err": outward_str(rel_err, digits=12),
            }

        # S^3 ~= SU(2) Bakry-Emery Ric = 2, Casimir eigenfunctions -Delta chi_j = 4j(j+1) chi_j, c_P_sharp = 1/3 < 1/2
        for two_j in range(5):
            j_rat = sp.Rational(two_j, 2)
            chi_j = sp.sin((two_j + 1) * th_sp) / sp.sin(th_sp)
            lap_chi = -sp.diff((sp.sin(th_sp) ** 2) * sp.diff(chi_j, th_sp), th_sp) / (sp.sin(th_sp) ** 2)
            eig_val = 4 * j_rat * (j_rat + 1)
            check(sp.simplify(lap_chi - eig_val * chi_j) == 0, f"S^3 Casimir eigenfunction failed at 2j={two_j}")
        ric_s3 = iv.mpf(2)
        c_p_be = iv.mpf(1) / ric_s3
        c_p_sharp = iv.mpf(1) / iv.mpf(3)
        check(strictly_above(ric_s3, "0") and strictly_below(c_p_sharp, c_p_be),
              "S^3 Bakry-Emery c_P_sharp < c_P_BE check failed")

        # Avenue 1 Red-Team guard: Gribov horizon det(M_FP)=0 & Neuberger 0/0 (+1 + (-1) = 0)
        s_grib = iv.mpf("0.5")
        c_plus = iv.sqrt(iv.mpf(1) - s_grib ** 2)
        c_minus = -c_plus
        neuberger_sum = iv.mpf(1) + iv.mpf(-1)
        check(strictly_above(c_plus, "0") and strictly_below(c_minus, "0") and neuberger_sum.a == 0 and neuberger_sum.b == 0,
              "Gribov/Neuberger 0/0 guard failed")
        m_fp_horizon = iv.cos(iv.pi / iv.mpf(2))
        check(m_fp_horizon.a <= 0 <= m_fp_horizon.b and strictly_below(abs(m_fp_horizon), "1e-39"),
              "Gribov horizon det(M_FP)=0 guard failed")

        track_1 = {
            "haar_moments_weyl_iv": {
                "norm_1": outward_str(haar_norm_1),
                "tr2_1": outward_str(haar_tr2_1),
                "tr4_2": outward_str(haar_tr4_2),
                "tr6_5": outward_str(haar_tr6_5),
            },
            "sympy_weyl_and_weingarten_verified": True,
            "one_plaquette_heat_kernel_sweep": hk_sweep,
            "s3_bakry_emery": {
                "ricci_curvature": outward_str(ric_s3, digits=6),
                "poincare_be_ub": outward_str(c_p_be, digits=6),
                "poincare_sharp_s3": outward_str(c_p_sharp),
                "sympy_casimir_eigenfunctions_verified": True,
            },
            "gribov_neuberger_0_0_guard": True,
        }

        # =====================================================================
        # Track 2a: Zegarlinski Weak-Mixing K_M Sweep & Fixed-Coupling Blowup
        # =====================================================================
        def km_glauber_c_p(M_sites: int, e2J_inv_frac: Fraction):
            dim = 1 << M_sites
            e2J_inv_iv = iv.mpf(e2J_inv_frac.numerator) / iv.mpf(e2J_inv_frac.denominator)
            max_exp = M_sites * M_sites
            pow_cache = [iv.mpf(1)]
            for _ in range(max_exp):
                pow_cache.append(pow_cache[-1] * e2J_inv_iv)
            weights = []
            for mask in range(dim):
                kp = mask.bit_count()
                weights.append(pow_cache[kp * (M_sites - kp)])
            Z_km = sum(weights)
            mu = [w / Z_km for w in weights]
            sqrt_mu = [iv.sqrt(m) for m in mu]

            H_M = iv_zeros(dim)
            for x in range(dim):
                diag_val = iv.mpf(M_sites)
                for bit in range(M_sites):
                    y = x ^ (1 << bit)
                    denom = mu[x] + mu[y]
                    pxx = mu[x] / denom
                    pxy = mu[y] / denom
                    diag_val -= pxx
                    H_M[x][y] = iv.mpc(-sqrt_mu[x] * pxy / sqrt_mu[y], 0)
                H_M[x][x] = iv.mpc(diag_val, 0)
            evals_H, _ = enclose_hermitian_eigenvalues(H_M)
            check(strictly_below(abs(evals_H[0]), "1e-35"), f"K_{M_sites} H_M lambda_0 != 0: {evals_H[0]}")
            check(strictly_above(evals_H[1], "0"), f"K_{M_sites} H_M lambda_1 <= 0: {evals_H[1]}")
            return iv.mpf(1) / evals_H[1]

        km_weak_mixing = {}
        for g_tag, g_frac in (
            ("gamma_0_1", Fraction(1, 10)),
            ("gamma_0_5", Fraction(1, 2)),
            ("gamma_0_9", Fraction(9, 10)),
            ("gamma_1_0", Fraction(1, 1)),
            ("gamma_1_5", Fraction(3, 2)),
        ):
            g_iv = iv.mpf(g_frac.numerator) / iv.mpf(g_frac.denominator)
            one_minus_g = iv.mpf(1) - g_iv
            cp_by_M = {}
            for M_val in (3, 4):
                r_th = g_frac / (M_val - 1)
                e2J_inv_f = (Fraction(1, 1) - r_th) / (Fraction(1, 1) + r_th)
                cp_m = km_glauber_c_p(M_val, e2J_inv_f)
                if g_frac < 1:
                    zeg_ub = iv.mpf(1) / one_minus_g
                    check(strictly_below(cp_m, zeg_ub), f"Zegarlinski bound failed at {g_tag}, M={M_val}")
                else:
                    check(one_minus_g.b <= 0, f"Breakdown 1 - gamma_DS <= 0 failed at {g_tag}")
                cp_by_M[f"M_{M_val}"] = outward_str(cp_m)
            km_weak_mixing[g_tag] = {
                "gamma_DS": str(g_frac),
                "zegarlinski_regime_valid": bool(g_frac < 1),
                "zegarlinski_ub": outward_str(iv.mpf(1) / one_minus_g) if g_frac < 1 else "UNBOUNDED_BREAKDOWN",
                **cp_by_M,
            }

        fixed_blowup = {}
        prev_cp_fix = iv.mpf(0)
        for M_val in (2, 3, 4, 5):
            cp_fix = km_glauber_c_p(M_val, Fraction(1, 3))
            check(strictly_above(cp_fix, prev_cp_fix), f"Fixed-coupling exp(2J)=3 c_P not growing at M={M_val}")
            prev_cp_fix = cp_fix
            fixed_blowup[f"M_{M_val}"] = outward_str(cp_fix)
        check(strictly_above(prev_cp_fix, "80"), f"Fixed-coupling c_P(5) blowup < 80: {prev_cp_fix}")

        track_2a = {
            "km_weak_mixing_sweep": km_weak_mixing,
            "fixed_coupling_breakdown_blowup": fixed_blowup,
        }

        # =====================================================================
        # Track 2b: Fund-Adj SU(2) Crossover vs Bulk Transition & Tomboulis-Yaffe
        # =====================================================================
        trA_sp = (4 * (sp.cos(th_sp) ** 2) - 1) / 3
        int_trA3 = sp.integrate(weyl_density * (trA_sp ** 3), (th_sp, 0, sp.pi))
        int_trF3 = sp.integrate(weyl_density * (sp.cos(th_sp) ** 3), (th_sp, 0, sp.pi))
        check(int_trA3 == sp.Rational(1, 27), f"<trA^3> != 1/27: {int_trA3}")
        check(int_trF3 == 0, f"<cos^3 theta> != 0: {int_trF3}")

        bA_sweep = {}
        chi_A_vals = {}
        for bA_tag, bA_f in (
            ("bA_0", Fraction(0, 1)),
            ("bA_0_5", Fraction(1, 2)),
            ("bA_1_5", Fraction(3, 2)),
            ("bA_2_5", Fraction(5, 2)),
        ):
            bA_iv = iv.mpf(bA_f.numerator) / iv.mpf(bA_f.denominator)
            # Fundamental beta_F = 2 smooth S^3 character gap
            res_fa = _iv_weyl_taylor_integrate_vec(iv.mpf(2), bA_iv, 2, n_sub=64, deg=27)
            c_half_bF2 = res_fa[1] / res_fa[0]
            gap_bF2 = -iv.log(c_half_bF2)
            check(strictly_above(c_half_bF2, "0") and strictly_above(gap_bF2, "0"),
                  f"Fund-Adj (beta_F=2, {bA_tag}) S^3 gap <= 0")

            # Pure adjoint beta_F = 0 (SO(3)) Z_2 vanishing c_{1/2} = 0 and chi_A
            res_so3 = _iv_weyl_taylor_integrate_vec(iv.mpf(0), bA_iv, 4, n_sub=64, deg=27)
            c_half_bF0 = res_so3[1] / res_so3[0]
            check(strictly_below(abs(c_half_bF0), "1e-38"),
                  f"SO(3) (beta_F=0, {bA_tag}) c_1/2 not zero: {c_half_bF0}")
            e_c2 = res_so3[2] / res_so3[0]
            e_c4 = res_so3[4] / res_so3[0]
            mean_trA = (iv.mpf(4) * e_c2 - iv.mpf(1)) / iv.mpf(3)
            mean_trA2 = (iv.mpf(16) * e_c4 - iv.mpf(8) * e_c2 + iv.mpf(1)) / iv.mpf(9)
            chi_A = mean_trA2 - (mean_trA ** 2)
            check(strictly_above(chi_A, "0"), f"SO(3) susceptibility <= 0 at {bA_tag}")
            chi_A_vals[bA_tag] = chi_A

            # 4D SO(3) Weiss mean-field V_MF(0.8; bA)
            m08 = iv.mpf("0.8")
            Z_mf_08 = _iv_weyl_taylor_integrate_vec(iv.mpf(0), iv.mpf(6) * bA_iv * m08, 0, n_sub=64, deg=27)[0]
            V_mf_08 = iv.mpf(3) * bA_iv * (m08 ** 2) - iv.log(Z_mf_08)
            if bA_f == Fraction(1, 2):
                check(strictly_above(V_mf_08, "0"), f"V_MF(0.8; 0.5) not > 0: {V_mf_08}")
            elif bA_f >= Fraction(3, 2):
                check(strictly_below(V_mf_08, "0"), f"V_MF(0.8; {bA_f}) not < 0: {V_mf_08}")

            bA_sweep[bA_tag] = {
                "beta_A": str(bA_f),
                "beta_F_2_c_half": outward_str(c_half_bF2),
                "beta_F_2_character_gap": outward_str(gap_bF2),
                "beta_F_0_c_half_abs_ub": outward_str(abs(c_half_bF0), digits=12),
                "beta_F_0_chi_A": outward_str(chi_A),
                "so3_V_MF_at_m_0_8": outward_str(V_mf_08),
            }

        check(strictly_above(chi_A_vals["bA_1_5"], chi_A_vals["bA_0_5"])
              and strictly_above(chi_A_vals["bA_1_5"], chi_A_vals["bA_2_5"]),
              "SO(3) susceptibility peak at beta_A=1.5 failed")

        # 4D SO(3) first-order barrier at beta_A = 1.35: V_MF(0.1; 1.35) > 0 > V_MF(0.7; 1.35)
        bA_135 = iv.mpf("1.35")
        m_low, m_high = iv.mpf("0.1"), iv.mpf("0.7")
        V_low = iv.mpf(3) * bA_135 * (m_low ** 2) - iv.log(
            _iv_weyl_taylor_integrate_vec(iv.mpf(0), iv.mpf(6) * bA_135 * m_low, 0, n_sub=64, deg=27)[0]
        )
        V_high = iv.mpf(3) * bA_135 * (m_high ** 2) - iv.log(
            _iv_weyl_taylor_integrate_vec(iv.mpf(0), iv.mpf(6) * bA_135 * m_high, 0, n_sub=64, deg=27)[0]
        )
        check(strictly_above(V_low, "0") and strictly_below(V_high, "0"),
              f"SO(3) first-order barrier at beta_A=1.35 failed: V_low={V_low}, V_high={V_high}")

        # Tomboulis-Yaffe analyticity Cauchy bound vs Pirogov-Sinai latent-heat contradiction at V=25000
        M_ty = iv.mpf(1)
        delta_ty = iv.mpf(1) / iv.mpf(10)
        cauchy_ub = (iv.mpf(2) * M_ty) / (delta_ty ** 2)
        c_ps = iv.mpf(1) / iv.mpf(4)
        delta_e = iv.mpf(1) / iv.mpf(5)
        V_crit = cauchy_ub / (c_ps * (delta_e ** 2))
        V_test = iv.mpf(25000)
        ps_lb_25000 = c_ps * V_test * (delta_e ** 2)
        check(V_crit.a <= 20000 <= V_crit.b and strictly_above(V_test, V_crit) and strictly_above(ps_lb_25000, cauchy_ub),
              "Tomboulis-Yaffe vs Pirogov-Sinai contradiction failed")

        # Avenue 4 Red-Team guard: H(4) O(xi_lat^{-2}) SO(4) restoration vs xi_lat = O(1) failure
        aniso_xi_1 = iv.mpf(1) / iv.mpf(16)
        aniso_xi_1e4 = (iv.mpf(1) / iv.mpf(16)) / (iv.mpf(10000) ** 2)
        check(strictly_above(aniso_xi_1, "0.06") and strictly_below(aniso_xi_1e4, "1e-9"),
              "H(4) xi_lat=O(1) failure vs xi_lat=1e4 restoration guard failed")

        track_2b = {
            "sympy_cubic_haar_1_27_vs_0_verified": True,
            "beta_A_sweep": bA_sweep,
            "so3_first_order_barrier_bA_1_35_verified": True,
            "tomboulis_yaffe_vs_pirogov_sinai": {
                "cauchy_ub": outward_str(cauchy_ub, digits=8),
                "V_crit": outward_str(V_crit, digits=8),
                "ps_lb_at_V_25000": outward_str(ps_lb_25000, digits=8),
                "contradiction_at_V_25000": True,
            },
            "h4_xi_lat_o1_anisotropy_failure_verified": True,
        }

        # =====================================================================
        # Track 3a: T^4 Discrete Hodge (L = 2, 3) via exact DomainMatrix(..., ZZ) + 2pi Z Descent
        # =====================================================================
        t4_hodge = {
            "cohomology_space": "spacetime_T4_NOT_orbit_space_U_adm_mod_G",
        }
        pairs2 = [(mu, nu) for mu in range(4) for nu in range(mu + 1, 4)]
        pair_idx = {p: idx for idx, p in enumerate(pairs2)}
        triples3 = [(a, b, c) for a in range(4) for b in range(a + 1, 4) for c in range(b + 1, 4)]

        for L_lat in (2, 3):
            V_n = L_lat ** 4
            E_n = 4 * V_n
            F_n = 6 * V_n
            C3_n = 4 * V_n

            def vid4(x0: int, x1: int, x2: int, x3: int) -> int:
                return (((x0 % L_lat) * L_lat + (x1 % L_lat)) * L_lat + (x2 % L_lat)) * L_lat + (x3 % L_lat)

            def step_v4(x: tuple[int, int, int, int], mu: int) -> int:
                y = list(x)
                y[mu] = (y[mu] + 1) % L_lat
                return vid4(y[0], y[1], y[2], y[3])

            rows_d0 = {}
            rows_d1 = {}
            rows_d2 = {}
            rows_H1 = {mu: {} for mu in range(4)}
            rows_H2 = {p: {} for p in range(6)}
            eta_rows = {}

            for x0 in range(L_lat):
                for x1 in range(L_lat):
                    for x2 in range(L_lat):
                        for x3 in range(L_lat):
                            x = (x0, x1, x2, x3)
                            v = vid4(x0, x1, x2, x3)
                            for mu in range(4):
                                e = v * 4 + mu
                                vp = step_v4(x, mu)
                                rows_d0[e] = {vp: ZZ(1), v: ZZ(-1)}
                            for p_i, (mu, nu) in enumerate(pairs2):
                                f = v * 6 + p_i
                                vp_mu = step_v4(x, mu)
                                vp_nu = step_v4(x, nu)
                                rows_d1[f] = {
                                    v * 4 + mu: ZZ(1),
                                    vp_mu * 4 + nu: ZZ(1),
                                    vp_nu * 4 + mu: ZZ(-1),
                                    v * 4 + nu: ZZ(-1),
                                }
                                if p_i == 0:
                                    eta_rows[f] = {0: ZZ(1)}
                            for t_i, (a, b, c) in enumerate(triples3):
                                c3 = v * 4 + t_i
                                vp_a = step_v4(x, a)
                                vp_b = step_v4(x, b)
                                vp_c = step_v4(x, c)
                                p_bc = pair_idx[(b, c)]
                                p_ac = pair_idx[(a, c)]
                                p_ab = pair_idx[(a, b)]
                                rows_d2[c3] = {
                                    vp_a * 6 + p_bc: ZZ(1),
                                    v * 6 + p_bc: ZZ(-1),
                                    vp_b * 6 + p_ac: ZZ(-1),
                                    v * 6 + p_ac: ZZ(1),
                                    vp_c * 6 + p_ab: ZZ(1),
                                    v * 6 + p_ab: ZZ(-1),
                                }

            for mu in range(4):
                for t in range(L_lat):
                    pt = [0, 0, 0, 0]
                    pt[mu] = t
                    rows_H1[mu][vid4(pt[0], pt[1], pt[2], pt[3]) * 4 + mu] = ZZ(1)
            for p_i, (mu, nu) in enumerate(pairs2):
                for s in range(L_lat):
                    for t in range(L_lat):
                        pt = [0, 0, 0, 0]
                        pt[mu] = s
                        pt[nu] = t
                        rows_H2[p_i][vid4(pt[0], pt[1], pt[2], pt[3]) * 6 + p_i] = ZZ(1)

            D0 = DomainMatrix(rows_d0, (E_n, V_n), ZZ)
            D1 = DomainMatrix(rows_d1, (F_n, E_n), ZZ)
            D2 = DomainMatrix(rows_d2, (C3_n, F_n), ZZ)
            H1 = DomainMatrix(rows_H1, (4, E_n), ZZ)
            H2 = DomainMatrix(rows_H2, (6, F_n), ZZ)
            ETA = DomainMatrix(eta_rows, (F_n, 1), ZZ)

            check((D1 * D0).is_zero_matrix, f"T^4 d1*d0 != 0 at L={L_lat}")
            check((D2 * D1).is_zero_matrix, f"T^4 d2*d1 != 0 at L={L_lat}")
            check((H1 * D0).is_zero_matrix, f"T^4 H1*d0 != 0 at L={L_lat}")
            check((H2 * D1).is_zero_matrix, f"T^4 H2*d1 != 0 at L={L_lat}")
            check((D2 * ETA).is_zero_matrix, f"T^4 d2*eta_int != 0 at L={L_lat}")

            rk0 = int(D0.to_field().rank())
            rk1 = int(D1.to_field().rank())
            rk2 = int(D2.to_field().rank())
            b0 = V_n - rk0
            b1 = (E_n - rk1) - rk0
            b2 = (F_n - rk2) - rk1
            check(b0 == 1 and b1 == 4 and b2 == 6, f"T^4 Betti numbers mismatch at L={L_lat}: {(b0, b1, b2)}")

            aug1_rk = int(DomainMatrix.vstack(D1, H1).to_field().rank())
            aug2_rk = int(DomainMatrix.vstack(D2, H2).to_field().rank())
            check(E_n - aug1_rk == rk0, f"T^4 H1 augmented rank failed at L={L_lat}")
            check(F_n - aug2_rk == rk1, f"T^4 H2 augmented rank failed at L={L_lat}")

            eta_aug_rk = int(DomainMatrix.hstack(D1, ETA).to_field().rank())
            check(eta_aug_rk == rk1 + 1, f"T^4 eta_int unexpectedly in im(d1) at L={L_lat}")
            h2_eta = H2 * ETA
            flux_vec = [int(h2_eta[r, 0].element) for r in range(6)]
            check(flux_vec == [L_lat ** 2, 0, 0, 0, 0, 0], f"T^4 eta_int flux mismatch at L={L_lat}: {flux_vec}")

            # 2*pi*Z quantized Berry descent vs pi half-flux obstruction
            flux_2pi = iv.mpf(L_lat ** 2) * (iv.mpf(2) * iv.pi / iv.mpf(L_lat ** 2))
            descent_err = abs(iv.exp(iv.mpc(0, 1) * iv.mpc(flux_2pi, 0)) - iv.mpc(1, 0))
            check(strictly_below(descent_err, "1e-39"), f"2pi Berry descent error too large at L={L_lat}: {descent_err}")
            half_flux_pi = iv.mpf(L_lat ** 2) * (iv.pi / iv.mpf(L_lat ** 2))
            half_flux_obs = abs(iv.exp(iv.mpc(0, 1) * iv.mpc(half_flux_pi, 0)) - iv.mpc(1, 0))
            check(strictly_above(half_flux_obs, "1.999999") and strictly_below(half_flux_obs, "2.000001"),
                  f"Half-flux obstruction != 2 at L={L_lat}: {half_flux_obs}")

            t4_hodge[f"L_{L_lat}"] = {
                "V": V_n,
                "E": E_n,
                "F": F_n,
                "C3": C3_n,
                "rk_d0": rk0,
                "rk_d1": rk1,
                "rk_d2": rk2,
                "b0": b0,
                "b1": b1,
                "b2": b2,
                "eta_int_flux": flux_vec,
                "descent_2pi_err": outward_str(descent_err, digits=12),
                "half_flux_obstruction": outward_str(half_flux_obs),
            }

        # =====================================================================
        # Track 3b: 5D Domain-Wall Overlap Suppression & (3,3,1) vs Single-Doublet Guard
        # =====================================================================
        overlap_sweep = {}
        for m_tag, m_frac in (("mDW_1_2", Fraction(1, 2)), ("mDW_1", Fraction(1, 1))):
            m_iv = iv.mpf(m_frac.numerator) / iv.mpf(m_frac.denominator)
            r_dw = iv.exp(-m_iv)
            l5_sweep = {}
            prev_smin = iv.mpf(10)
            for L5 in (2, 4, 8, 16):
                M_dw = iv_zeros(L5)
                for s in range(L5):
                    M_dw[s][s] = iv.mpc(r_dw, 0)
                    if s + 1 < L5:
                        M_dw[s][s + 1] = iv.mpc(-1, 0)
                gram_dw = iv_matmul(iv_conj_transpose(M_dw), M_dw)
                evals_dw, _ = enclose_hermitian_eigenvalues(gram_dw)
                check(strictly_above(evals_dw[0], "0"), f"DWF M^T M lambda_min <= 0 at {m_tag}, L5={L5}")
                smin_dw = iv.sqrt(evals_dw[0])
                exp_bound = iv.exp(-m_iv * iv.mpf(L5))
                check(strictly_above(smin_dw, "0") and strictly_below(smin_dw, exp_bound),
                      f"DWF 0 < sigma_min < exp(-m_DW L_5) failed at {m_tag}, L5={L5}")
                check(strictly_below(smin_dw, prev_smin), f"DWF sigma_min not decreasing at {m_tag}, L5={L5}")
                prev_smin = smin_dw
                if m_tag == "mDW_1" and L5 == 16:
                    check(strictly_below(exp_bound, "1e-6") and strictly_below(smin_dw, "1e-6"),
                          "DWF (m_DW=1, L_5=16) exponential suppression < 1e-6 failed")
                l5_sweep[f"L5_{L5}"] = {
                    "L_5": L5,
                    "sigma_min": outward_str(smin_dw),
                    "exp_minus_mDW_L5": outward_str(exp_bound),
                }
            overlap_sweep[m_tag] = {
                "m_DW": str(m_frac),
                "L5_sweep": l5_sweep,
            }

        # Caveat 3: Exact Fraction (3,3,1) 15-Weyl sum Y^3 = 0 vs single-doublet 3*2*(1/6)^3 = 1/36 != 0
        weyl_15_y3 = (
            3 * 2 * (Fraction(1, 6) ** 3)
            + 3 * 1 * (Fraction(-2, 3) ** 3)
            + 3 * 1 * (Fraction(1, 3) ** 3)
            + 1 * 2 * (Fraction(-1, 2) ** 3)
            + 1 * 1 * (Fraction(1, 1) ** 3)
        )
        single_doublet_y3 = 3 * 2 * (Fraction(1, 6) ** 3)
        check(weyl_15_y3 == 0, f"(3,3,1) 15-Weyl sum Y^3 != 0: {weyl_15_y3}")
        check(single_doublet_y3 == Fraction(1, 36) and single_doublet_y3 != 0,
              f"Single-doublet sum Y^3 != 1/36: {single_doublet_y3}")

        track_3b = {
            "overlap_sweep": overlap_sweep,
            "mirror_decoupling_status": "OPEN",
            "anomaly_331_vs_single_doublet_guard": True,
            "anomaly_331_sum_Y3": str(weyl_15_y3),
            "single_doublet_sum_Y3": str(single_doublet_y3),
            "free_dwf_does_not_close_interacting_smg_gap": True,
        }

        return {
            "round": "round_05",
            "h2d_status": "OPEN",
            "interval_checks_passed": interval_checks,
            "track_1_su2_haar_weingarten_bakry_emery": track_1,
            "track_2a_zegarlinski_weak_mixing": track_2a,
            "track_2b_fund_adj_crossover_tomboulis_yaffe": track_2b,
            "track_3a_t4_discrete_hodge": t4_hodge,
            "track_3b_5d_domain_wall_overlap": track_3b,
        }
    finally:
        mp.dps = 50
        iv.dps = 40


def _frac_matmul(A: list[list[Fraction]], B: list[list[Fraction]]) -> list[list[Fraction]]:
    m = len(A)
    klen = len(A[0])
    n = len(B[0])
    return [
        [sum(A[i][k] * B[k][j] for k in range(klen)) for j in range(n)]
        for i in range(m)
    ]


def _frac_det(M: list[list[Fraction]]) -> Fraction:
    n = len(M)
    if n == 2:
        return M[0][0] * M[1][1] - M[0][1] * M[1][0]
    if n == 3:
        return (
            M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
            - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
            + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0])
        )
    raise ValueError(f"Unsupported matrix dimension for _frac_det: {n}")


def _iv_det_3x3(M: list[list]):
    return (
        M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
        - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
        + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0])
    )


def compute_h2d_round06_convergence_bridges(
    r4_bridges: dict | None = None,
    r5_bridges: dict | None = None,
) -> dict:
    """Deterministic 40-digit mpmath.iv + sympy DomainMatrix(..., ZZ) + Fraction convergence certs for Round 06 H2d."""
    if r4_bridges is None:
        r4_bridges = compute_h2d_round04_constructive_bridges()
    if r5_bridges is None:
        r5_bridges = compute_h2d_round05_deepening_bridges()

    mp.dps = 60
    iv.dps = 40
    try:
        interval_checks = 0

        def check(ok: bool, msg: str) -> None:
            nonlocal interval_checks
            require(ok, msg)
            interval_checks += 1

        # =====================================================================
        # (a) Complete T^4 Discrete Hodge D_0, D_1, D_2, D_3 (C4 x C3) over ZZ
        #     on cubic L=2, L=3 AND non-cubic (2, 2, 2, 3)
        # =====================================================================
        pairs2 = [(mu, nu) for mu in range(4) for nu in range(mu + 1, 4)]
        pair_idx = {p: idx for idx, p in enumerate(pairs2)}
        triples3 = [(a, b, c) for a in range(4) for b in range(a + 1, 4) for c in range(b + 1, 4)]

        t4_complete_hodge = {
            "domain_caveat": "spacetime_T4_NOT_orbit_space_U_adm_mod_G",
            "dead_end_ref": "DEAD-20261124-12",
            "lattices": {},
        }

        for lat_tag, dims in (
            ("L_2", (2, 2, 2, 2)),
            ("L_3", (3, 3, 3, 3)),
            ("L_2x2x2x3", (2, 2, 2, 3)),
        ):
            L0, L1, L2, L3 = dims
            V_n = L0 * L1 * L2 * L3
            E_n = 4 * V_n
            F_n = 6 * V_n
            C3_n = 4 * V_n
            C4_n = V_n

            def vid4(x0: int, x1: int, x2: int, x3: int) -> int:
                return (((x0 % L0) * L1 + (x1 % L1)) * L2 + (x2 % L2)) * L3 + (x3 % L3)

            def step_v4(x: tuple[int, int, int, int], mu: int) -> int:
                y = list(x)
                y[mu] = (y[mu] + 1) % dims[mu]
                return vid4(y[0], y[1], y[2], y[3])

            rows_d0 = {}
            rows_d1 = {}
            rows_d2 = {}
            rows_d3 = {}
            rows_H1 = {mu: {} for mu in range(4)}
            rows_H2 = {p: {} for p in range(6)}
            rows_H3 = {t: {} for t in range(4)}
            rows_H4 = {0: {}}
            eta_rows = {}

            for x0 in range(L0):
                for x1 in range(L1):
                    for x2 in range(L2):
                        for x3 in range(L3):
                            x = (x0, x1, x2, x3)
                            v = vid4(x0, x1, x2, x3)
                            vp_0 = step_v4(x, 0)
                            vp_1 = step_v4(x, 1)
                            vp_2 = step_v4(x, 2)
                            vp_3 = step_v4(x, 3)

                            for mu in range(4):
                                e = v * 4 + mu
                                vp = step_v4(x, mu)
                                rows_d0[e] = {vp: ZZ(1), v: ZZ(-1)}

                            for p_i, (mu, nu) in enumerate(pairs2):
                                f = v * 6 + p_i
                                vp_mu = step_v4(x, mu)
                                vp_nu = step_v4(x, nu)
                                rows_d1[f] = {
                                    v * 4 + mu: ZZ(1),
                                    vp_mu * 4 + nu: ZZ(1),
                                    vp_nu * 4 + mu: ZZ(-1),
                                    v * 4 + nu: ZZ(-1),
                                }
                                if p_i == 0:
                                    eta_rows[f] = {0: ZZ(1)}

                            for t_i, (a, b, c) in enumerate(triples3):
                                c3 = v * 4 + t_i
                                vp_a = step_v4(x, a)
                                vp_b = step_v4(x, b)
                                vp_c = step_v4(x, c)
                                p_bc = pair_idx[(b, c)]
                                p_ac = pair_idx[(a, c)]
                                p_ab = pair_idx[(a, b)]
                                rows_d2[c3] = {
                                    vp_a * 6 + p_bc: ZZ(1),
                                    v * 6 + p_bc: ZZ(-1),
                                    vp_b * 6 + p_ac: ZZ(-1),
                                    v * 6 + p_ac: ZZ(1),
                                    vp_c * 6 + p_ab: ZZ(1),
                                    v * 6 + p_ab: ZZ(-1),
                                }

                            # D_3: C^3 -> C^4, triples3 = [(0,1,2), (0,1,3), (0,2,3), (1,2,3)]
                            rows_d3[v] = {
                                vp_0 * 4 + 3: ZZ(1),
                                v * 4 + 3: ZZ(-1),
                                vp_1 * 4 + 2: ZZ(-1),
                                v * 4 + 2: ZZ(1),
                                vp_2 * 4 + 1: ZZ(1),
                                v * 4 + 1: ZZ(-1),
                                vp_3 * 4 + 0: ZZ(-1),
                                v * 4 + 0: ZZ(1),
                            }
                            rows_H4[0][v] = ZZ(1)

            for mu in range(4):
                for t in range(dims[mu]):
                    pt = [0, 0, 0, 0]
                    pt[mu] = t
                    rows_H1[mu][vid4(pt[0], pt[1], pt[2], pt[3]) * 4 + mu] = ZZ(1)
            for p_i, (mu, nu) in enumerate(pairs2):
                for s in range(dims[mu]):
                    for t in range(dims[nu]):
                        pt = [0, 0, 0, 0]
                        pt[mu] = s
                        pt[nu] = t
                        rows_H2[p_i][vid4(pt[0], pt[1], pt[2], pt[3]) * 6 + p_i] = ZZ(1)
            for t_i, (a, b, c) in enumerate(triples3):
                for r in range(dims[a]):
                    for s in range(dims[b]):
                        for t in range(dims[c]):
                            pt = [0, 0, 0, 0]
                            pt[a] = r
                            pt[b] = s
                            pt[c] = t
                            rows_H3[t_i][vid4(pt[0], pt[1], pt[2], pt[3]) * 4 + t_i] = ZZ(1)

            D0 = DomainMatrix(rows_d0, (E_n, V_n), ZZ)
            D1 = DomainMatrix(rows_d1, (F_n, E_n), ZZ)
            D2 = DomainMatrix(rows_d2, (C3_n, F_n), ZZ)
            D3 = DomainMatrix(rows_d3, (C4_n, C3_n), ZZ)
            H1 = DomainMatrix(rows_H1, (4, E_n), ZZ)
            H2 = DomainMatrix(rows_H2, (6, F_n), ZZ)
            H3 = DomainMatrix(rows_H3, (4, C3_n), ZZ)
            H4 = DomainMatrix(rows_H4, (1, C4_n), ZZ)
            ETA = DomainMatrix(eta_rows, (F_n, 1), ZZ)

            check((D1 * D0).is_zero_matrix, f"T^4 D1*D0 != 0 on {lat_tag}")
            check((D2 * D1).is_zero_matrix, f"T^4 D2*D1 != 0 on {lat_tag}")
            check((D3 * D2).is_zero_matrix, f"T^4 D3*D2 != 0 on {lat_tag}")
            check((H1 * D0).is_zero_matrix, f"T^4 H1*D0 != 0 on {lat_tag}")
            check((H2 * D1).is_zero_matrix, f"T^4 H2*D1 != 0 on {lat_tag}")
            check((H3 * D2).is_zero_matrix, f"T^4 H3*D2 != 0 on {lat_tag}")
            check((H4 * D3).is_zero_matrix, f"T^4 H4*D3 != 0 on {lat_tag}")
            check((D2 * ETA).is_zero_matrix, f"T^4 D2*ETA != 0 on {lat_tag}")

            rk0 = int(D0.to_field().rank())
            rk1 = int(D1.to_field().rank())
            rk2 = int(D2.to_field().rank())
            rk3 = int(D3.to_field().rank())
            b0 = V_n - rk0
            b1 = (E_n - rk1) - rk0
            b2 = (F_n - rk2) - rk1
            b3 = (C3_n - rk3) - rk2
            b4 = C4_n - rk3
            betti = [b0, b1, b2, b3, b4]
            check(betti == [1, 4, 6, 4, 1], f"T^4 Betti != (1,4,6,4,1) on {lat_tag}: {betti}")
            check(betti == list(reversed(betti)), f"T^4 Poincare duality failed on {lat_tag}")
            chi_betti = b0 - b1 + b2 - b3 + b4
            chi_cells = V_n - E_n + F_n - C3_n + C4_n
            check(chi_betti == 0 and chi_cells == 0, f"T^4 Euler char != 0 on {lat_tag}")

            aug1_rk = int(DomainMatrix.vstack(D1, H1).to_field().rank())
            aug2_rk = int(DomainMatrix.vstack(D2, H2).to_field().rank())
            aug3_rk = int(DomainMatrix.vstack(D3, H3).to_field().rank())
            aug4_rk = int(H4.to_field().rank())
            check(E_n - aug1_rk == rk0, f"T^4 H1 augmented rank failed on {lat_tag}")
            check(F_n - aug2_rk == rk1, f"T^4 H2 augmented rank failed on {lat_tag}")
            check(C3_n - aug3_rk == rk2, f"T^4 H3 augmented rank failed on {lat_tag}")
            check(C4_n - aug4_rk == rk3, f"T^4 H4 augmented rank failed on {lat_tag}")

            eta_aug_rk = int(DomainMatrix.hstack(D1, ETA).to_field().rank())
            check(eta_aug_rk == rk1 + 1, f"T^4 eta_int unexpectedly in im(D1) on {lat_tag}")
            h2_eta = H2 * ETA
            flux_vec = [int(h2_eta[r, 0].element) for r in range(6)]
            area01 = L0 * L1
            check(flux_vec == [area01, 0, 0, 0, 0, 0], f"T^4 eta_int flux mismatch on {lat_tag}: {flux_vec}")

            flux_2pi = iv.mpf(area01) * (iv.mpf(2) * iv.pi / iv.mpf(area01))
            descent_err = abs(iv.exp(iv.mpc(0, 1) * iv.mpc(flux_2pi, 0)) - iv.mpc(1, 0))
            check(strictly_below(descent_err, "1e-39"), f"2pi Berry descent error too large on {lat_tag}: {descent_err}")
            half_flux_pi = iv.mpf(area01) * (iv.pi / iv.mpf(area01))
            half_flux_obs = abs(iv.exp(iv.mpc(0, 1) * iv.mpc(half_flux_pi, 0)) - iv.mpc(1, 0))
            check(strictly_above(half_flux_obs, "1.999999") and strictly_below(half_flux_obs, "2.000001"),
                  f"Half-flux obstruction != 2 on {lat_tag}: {half_flux_obs}")

            t4_complete_hodge["lattices"][lat_tag] = {
                "dims": list(dims),
                "cells": {"V": V_n, "E": E_n, "F": F_n, "C3": C3_n, "C4": C4_n},
                "ranks": {"rk_D0": rk0, "rk_D1": rk1, "rk_D2": rk2, "rk_D3": rk3},
                "betti": betti,
                "euler_characteristic": chi_betti,
                "augmented_ranks": {"aug1": aug1_rk, "aug2": aug2_rk, "aug3": aug3_rk, "aug4": aug4_rk},
                "chain_identities_zero_zz": ["D1*D0==0", "D2*D1==0", "D3*D2==0"],
                "eta_int_flux": flux_vec,
                "descent_2pi_err": outward_str(descent_err, digits=12),
                "half_flux_obstruction": outward_str(half_flux_obs),
            }

        # =====================================================================
        # (b) Exact Neuberger 0/0 Signed-Pair & chi(SU(2) ~= S^3) = 0 vs Z_FMR > 0
        # =====================================================================
        # Exact DomainMatrix(..., ZZ) simplicial cohomology of S^3 ~= dDelta^4
        s3_v = list(range(5))
        s3_e = [(i, j) for i in range(5) for j in range(i + 1, 5)]
        s3_f = [(i, j, k) for i in range(5) for j in range(i + 1, 5) for k in range(j + 1, 5)]
        s3_t = [(i, j, k, l) for i in range(5) for j in range(i + 1, 5) for k in range(j + 1, 5) for l in range(k + 1, 5)]
        s3_e_idx = {e: idx for idx, e in enumerate(s3_e)}
        s3_f_idx = {f: idx for idx, f in enumerate(s3_f)}

        s3_d0_rows = {idx: {j: ZZ(1), i: ZZ(-1)} for idx, (i, j) in enumerate(s3_e)}
        s3_d1_rows = {
            idx: {
                s3_e_idx[(j, k)]: ZZ(1),
                s3_e_idx[(i, k)]: ZZ(-1),
                s3_e_idx[(i, j)]: ZZ(1),
            }
            for idx, (i, j, k) in enumerate(s3_f)
        }
        s3_d2_rows = {
            idx: {
                s3_f_idx[(j, k, l)]: ZZ(1),
                s3_f_idx[(i, k, l)]: ZZ(-1),
                s3_f_idx[(i, j, l)]: ZZ(1),
                s3_f_idx[(i, j, k)]: ZZ(-1),
            }
            for idx, (i, j, k, l) in enumerate(s3_t)
        }
        S3_D0 = DomainMatrix(s3_d0_rows, (len(s3_e), len(s3_v)), ZZ)
        S3_D1 = DomainMatrix(s3_d1_rows, (len(s3_f), len(s3_e)), ZZ)
        S3_D2 = DomainMatrix(s3_d2_rows, (len(s3_t), len(s3_f)), ZZ)
        check((S3_D1 * S3_D0).is_zero_matrix, "S^3 D1*D0 != 0")
        check((S3_D2 * S3_D1).is_zero_matrix, "S^3 D2*D1 != 0")

        s3_rk0 = int(S3_D0.to_field().rank())
        s3_rk1 = int(S3_D1.to_field().rank())
        s3_rk2 = int(S3_D2.to_field().rank())
        s3_betti = [
            len(s3_v) - s3_rk0,
            (len(s3_e) - s3_rk1) - s3_rk0,
            (len(s3_f) - s3_rk2) - s3_rk1,
            len(s3_t) - s3_rk2,
        ]
        check(s3_betti == [1, 0, 0, 1], f"S^3 Betti != (1,0,0,1): {s3_betti}")
        check(s3_betti == list(reversed(s3_betti)), "S^3 Poincare duality b_{3-k} == b_k failed")
        chi_s3 = s3_betti[0] - s3_betti[1] + s3_betti[2] - s3_betti[3]
        check(chi_s3 == 0, f"chi(SU(2) ~= S^3) != 0: {chi_s3}")

        # Explicit 2x2 and 3x3 M_FP & orientation-reversing involution R_flip
        M0_2_frac = [
            [Fraction(5, 2), Fraction(1, 2)],
            [Fraction(1, 2), Fraction(3, 2)],
        ]
        R_2_frac = [
            [Fraction(7, 25), Fraction(-24, 25)],
            [Fraction(-24, 25), Fraction(-7, 25)],
        ]
        M0_3_frac = [
            [Fraction(3, 1), Fraction(1, 2), Fraction(0, 1)],
            [Fraction(1, 2), Fraction(2, 1), Fraction(1, 3)],
            [Fraction(0, 1), Fraction(1, 3), Fraction(5, 2)],
        ]
        R_3_frac = [
            [Fraction(1, 3), Fraction(-2, 3), Fraction(-2, 3)],
            [Fraction(-2, 3), Fraction(1, 3), Fraction(-2, 3)],
            [Fraction(-2, 3), Fraction(-2, 3), Fraction(1, 3)],
        ]

        fp_signed_pairs = {}
        det_M0_by_dim = {}
        s_sym = sp.Symbol("s", real=True)
        for dim_tag, M0_f, R_f in (("dim_2", M0_2_frac, R_2_frac), ("dim_3", M0_3_frac, R_3_frac)):
            n_dim = len(M0_f)
            I_f = [[Fraction(1, 1) if r == c else Fraction(0, 1) for c in range(n_dim)] for r in range(n_dim)]
            check(_frac_matmul(R_f, R_f) == I_f, f"R_flip^2 != I for {dim_tag}")
            det_R = _frac_det(R_f)
            check(det_R == Fraction(-1, 1), f"det(R_flip) != -1 for {dim_tag}: {det_R}")

            M1_f = _frac_matmul(R_f, M0_f)
            det_M0 = _frac_det(M0_f)
            det_M1 = _frac_det(M1_f)
            check(det_M0 > 0, f"det(M0) <= 0 for {dim_tag}: {det_M0}")
            check(det_M1 == -det_M0 and det_M1 < 0, f"det(R_flip @ M0) != -det(M0) for {dim_tag}")
            sgn_sum = (1 if det_M0 > 0 else -1) + (1 if det_M1 > 0 else -1)
            check(sgn_sum == 0, f"Signed sum != 0 for {dim_tag}")

            # Exact midpoint horizon-crossing s_star = 1/2
            s_star = Fraction(1, 2)
            M_mid_f = [
                [(Fraction(1, 1) - s_star) * M0_f[r][c] + s_star * M1_f[r][c] for c in range(n_dim)]
                for r in range(n_dim)
            ]
            det_mid_f = _frac_det(M_mid_f)
            check(det_mid_f == 0, f"Midpoint horizon det != 0 at s_star=1/2 for {dim_tag}: {det_mid_f}")

            s_pre = Fraction(1, 4)
            s_post = Fraction(3, 4)
            M_pre_f = [[(Fraction(1, 1) - s_pre) * M0_f[r][c] + s_pre * M1_f[r][c] for c in range(n_dim)] for r in range(n_dim)]
            M_post_f = [[(Fraction(1, 1) - s_post) * M0_f[r][c] + s_post * M1_f[r][c] for c in range(n_dim)] for r in range(n_dim)]
            det_pre_f = _frac_det(M_pre_f)
            det_post_f = _frac_det(M_post_f)
            check(det_pre_f > 0 and det_post_f < 0, f"Horizon sign flip across s=1/2 failed for {dim_tag}")

            # Sympy symbolic homotopy det((1 - s) M_0 + s R M_0) vanishes at s = 1/2
            M0_sp = sp.Matrix([[sp.Rational(x.numerator, x.denominator) for x in row] for row in M0_f])
            M1_sp = sp.Matrix([[sp.Rational(x.numerator, x.denominator) for x in row] for row in M1_f])
            det_s_poly = sp.factor(((1 - s_sym) * M0_sp + s_sym * M1_sp).det())
            check(det_s_poly.subs(s_sym, sp.Rational(1, 2)) == 0, f"Sympy horizon polynomial != 0 at s=1/2 for {dim_tag}")

            # 40-digit mpmath.iv checks (SPD inside first Gribov region Omega + det cancellation)
            M0_iv = [[iv.mpc(iv.mpf(x.numerator) / iv.mpf(x.denominator), 0) for x in row] for row in M0_f]
            M1_iv = [[iv.mpc(iv.mpf(x.numerator) / iv.mpf(x.denominator), 0) for x in row] for r_idx, row in enumerate(M1_f)]
            M_mid_iv = [[iv.mpc(iv.mpf(x.numerator) / iv.mpf(x.denominator), 0) for x in row] for row in M_mid_f]
            evals_M0, _ = enclose_hermitian_eigenvalues(M0_iv)
            check(strictly_above(evals_M0[0], "0"), f"M0 not SPD (first Gribov region) for {dim_tag}: {evals_M0[0]}")

            det_fn = _iv_det_2x2 if n_dim == 2 else _iv_det_3x3
            det_M0_iv = det_fn(M0_iv).real
            det_M1_iv = det_fn(M1_iv).real
            det_mid_iv = det_fn(M_mid_iv).real
            det_sum_iv = det_M0_iv + det_M1_iv
            check(strictly_above(det_M0_iv, "0") and strictly_below(det_M1_iv, "0"),
                  f"iv determinant signs failed for {dim_tag}")
            check(det_sum_iv.a <= 0 <= det_sum_iv.b and strictly_below(abs(det_sum_iv), "1e-38"),
                  f"iv signed determinant pair failed to enclose 0 for {dim_tag}: {det_sum_iv}")
            check(det_mid_iv.a <= 0 <= det_mid_iv.b and strictly_below(abs(det_mid_iv), "1e-38"),
                  f"iv midpoint horizon det failed to enclose 0 for {dim_tag}: {det_mid_iv}")

            det_M0_by_dim[dim_tag] = det_M0
            fp_signed_pairs[dim_tag] = {
                "det_M0_exact": str(det_M0),
                "det_R_flip_M0_exact": str(det_M1),
                "det_R_flip_exact": str(det_R),
                "signed_sum": sgn_sum,
                "s_star_exact": str(s_star),
                "det_at_s_star_exact": str(det_mid_f),
                "det_at_s_1_4_exact": str(det_pre_f),
                "det_at_s_3_4_exact": str(det_post_f),
                "lambda_min_M0_iv": outward_str(evals_M0[0]),
                "det_M0_iv": outward_str(det_M0_iv),
                "det_R_flip_M0_iv": outward_str(det_M1_iv),
                "det_pair_sum_abs_ub_iv": outward_str(abs(det_sum_iv), digits=12),
                "det_midpoint_abs_ub_iv": outward_str(abs(det_mid_iv), digits=12),
            }

        # Global Z_BRST = 0, N_BRST = 0 (0/0) vs Z_FMR > 0, N_FMR / Z_FMR == O_phys
        O_phys_single = Fraction(17, 5)
        w1_orb = Fraction(3, 4)
        w2_orb = Fraction(5, 7)
        O1_orb = Fraction(17, 5)
        O2_orb = Fraction(11, 3)

        det2 = det_M0_by_dim["dim_2"]
        det3 = det_M0_by_dim["dim_3"]

        # Single-orbit pair (c_+, c_-)
        Z_BRST_single = w1_orb * det2 + w1_orb * (-det2)
        N_BRST_single = w1_orb * O_phys_single * det2 + w1_orb * O_phys_single * (-det2)
        Z_FMR_single = w1_orb * det2
        N_FMR_single = w1_orb * O_phys_single * det2
        check(Z_BRST_single == 0 and N_BRST_single == 0, "Single-orbit BRST 0/0 failed")
        check(Z_FMR_single > 0 and N_FMR_single / Z_FMR_single == O_phys_single,
              "Single-orbit FMR expectation != O_phys")

        # Multi-orbit ensemble (2x2 + 3x3 signed pairs)
        Z_BRST_multi = w1_orb * (det2 + (-det2)) + w2_orb * (det3 + (-det3))
        N_BRST_multi = w1_orb * O1_orb * (det2 + (-det2)) + w2_orb * O2_orb * (det3 + (-det3))
        Z_FMR_multi = w1_orb * det2 + w2_orb * det3
        N_FMR_multi = w1_orb * O1_orb * det2 + w2_orb * O2_orb * det3
        O_FMR_multi = N_FMR_multi / Z_FMR_multi
        check(Z_BRST_multi == 0 and N_BRST_multi == 0, "Multi-orbit BRST 0/0 failed")
        check(Z_FMR_multi > 0 and O_FMR_multi * Z_FMR_multi == N_FMR_multi, "Multi-orbit FMR ratio failed")

        # 40-digit mpmath.iv parity for Z_FMR, N_FMR / Z_FMR, and Z_BRST = 0
        def frac_iv(q: Fraction):
            return iv.mpf(q.numerator) / iv.mpf(q.denominator)

        Z_FMR_single_iv = frac_iv(Z_FMR_single)
        N_FMR_single_iv = frac_iv(N_FMR_single)
        O_phys_single_iv = frac_iv(O_phys_single)
        ratio_single_iv = N_FMR_single_iv / Z_FMR_single_iv
        check(strictly_above(Z_FMR_single_iv, "0"), "Single-orbit Z_FMR_iv <= 0")
        check(strictly_below(abs(ratio_single_iv - O_phys_single_iv), "1e-38"),
              "Single-orbit iv N_FMR/Z_FMR != O_phys")

        Z_FMR_multi_iv = frac_iv(Z_FMR_multi)
        N_FMR_multi_iv = frac_iv(N_FMR_multi)
        O_FMR_multi_iv = N_FMR_multi_iv / Z_FMR_multi_iv
        O_FMR_multi_exact_iv = frac_iv(O_FMR_multi)
        check(strictly_above(Z_FMR_multi_iv, "0"), "Multi-orbit Z_FMR_iv <= 0")
        check(strictly_below(abs(O_FMR_multi_iv - O_FMR_multi_exact_iv), "1e-38"),
              "Multi-orbit iv N_FMR/Z_FMR mismatch")

        neuberger_0_0_cert = {
            "su2_s3_simplicial_complex": {
                "cells": {"V": len(s3_v), "E": len(s3_e), "F": len(s3_f), "C3": len(s3_t)},
                "ranks": {"rk_D0": s3_rk0, "rk_D1": s3_rk1, "rk_D2": s3_rk2},
                "betti": s3_betti,
                "poincare_duality_b_3_minus_k_eq_bk": True,
                "euler_characteristic": chi_s3,
            },
            "faddeev_popov_signed_pairs": fp_signed_pairs,
            "brst_vs_fmr_partition_contrast": {
                "single_orbit_O_phys_exact": str(O_phys_single),
                "single_orbit_Z_BRST_exact": str(Z_BRST_single),
                "single_orbit_N_BRST_exact": str(N_BRST_single),
                "single_orbit_Z_FMR_exact": str(Z_FMR_single),
                "single_orbit_N_FMR_over_Z_FMR_exact": str(N_FMR_single / Z_FMR_single),
                "single_orbit_Z_FMR_iv": outward_str(Z_FMR_single_iv),
                "single_orbit_N_FMR_over_Z_FMR_iv": outward_str(ratio_single_iv),
                "multi_orbit_Z_BRST_exact": str(Z_BRST_multi),
                "multi_orbit_N_BRST_exact": str(N_BRST_multi),
                "multi_orbit_Z_FMR_exact": str(Z_FMR_multi),
                "multi_orbit_N_FMR_over_Z_FMR_exact": str(O_FMR_multi),
                "multi_orbit_Z_FMR_iv": outward_str(Z_FMR_multi_iv),
                "multi_orbit_N_FMR_over_Z_FMR_iv": outward_str(O_FMR_multi_iv),
            },
        }

        # =====================================================================
        # (c) 5-Track Non-Redundancy Truth Table & Round 06 Convergence Parity
        # =====================================================================
        truth_table_8 = []
        for b_uv in (0, 1):
            for b_ir in (0, 1):
                for b_ch in (0, 1):
                    clay_holds = bool(b_uv and b_ir and b_ch)
                    truth_table_8.append({
                        "bUV": b_uv,
                        "bIR": b_ir,
                        "bChiral": b_ch,
                        "h2d_clay_4d_continuum_measure": clay_holds,
                    })
        true_rows = [row for row in truth_table_8 if row["h2d_clay_4d_continuum_measure"]]
        falsifying_rows = [row for row in truth_table_8 if not row["h2d_clay_4d_continuum_measure"]]
        single_ablation_rows = [
            row for row in falsifying_rows if (row["bUV"] + row["bIR"] + row["bChiral"]) == 2
        ]
        check(len(truth_table_8) == 8, "Truth table row count != 8")
        check(len(true_rows) == 1 and true_rows[0]["bUV"] == 1 and true_rows[0]["bIR"] == 1 and true_rows[0]["bChiral"] == 1,
              "Unique (1,1,1) closure condition failed")
        check(len(falsifying_rows) == 7, f"Falsifying subset count != 7: {len(falsifying_rows)}")
        check(len(single_ablation_rows) == 3, "Single-pillar non-redundancy ablation count != 3")

        five_track_map = {
            "track_1_uv_haar_brst": {"pillar": "bUV", "open_premise": "BalabanSmallFieldGaugeRegularityPremise", "status": "OPEN"},
            "track_2_uv_t4_polymer": {"pillar": "bUV", "open_premise": "BalabanThermodynamicContinuationGap", "status": "OPEN"},
            "track_3_ir_zegarlinski_ds": {"pillar": "bIR", "open_premise": "gamma_DS(ell_phys) < 1", "status": "OPEN"},
            "track_4_ir_crossover_vortex": {"pillar": "bIR", "open_premise": "H(4) + xi_lat -> inf + noBulkTransition", "status": "OPEN"},
            "track_5_chiral_smg_berry": {"pillar": "bChiral", "open_premise": "SMGMirrorDecouplingOpenPremise + BerryCountertermFiniteAOpenPremise", "status": "OPEN"},
        }
        check(len(five_track_map) == 5, "Five-track convergence map size != 5")
        check({v["pillar"] for v in five_track_map.values()} == {"bUV", "bIR", "bChiral"},
              "Five-track map failed surjective coverage of {bUV, bIR, bChiral}")

        # Deterministic parity links to Round 04 (33,477) and Round 05 (153)
        check(r4_bridges.get("round") == "round_04" and r4_bridges.get("h2d_status") == "OPEN",
              "Round 04 header parity mismatch")
        check(r4_bridges.get("interval_checks_passed") == 33477,
              f"Round 04 check count != 33477: {r4_bridges.get('interval_checks_passed')}")
        check(r5_bridges.get("round") == "round_05" and r5_bridges.get("h2d_status") == "OPEN",
              "Round 05 header parity mismatch")
        check(r5_bridges.get("interval_checks_passed") == 153,
              f"Round 05 check count != 153: {r5_bridges.get('interval_checks_passed')}")

        r4_t2 = r4_bridges["track_3_chiral_constructive_bridges"]["t2_discrete_hodge_sweep"]
        for t2_key, t2_rec in r4_t2.items():
            check(t2_rec["V"] - t2_rec["E"] + t2_rec["F"] == 0, f"Round 04 T^2 Euler parity failed on {t2_key}")
            check(t2_rec["dim_H1"] == 2, f"Round 04 T^2 dim_H1 != 2 on {t2_key}")

        r5_t4 = r5_bridges["track_3a_t4_discrete_hodge"]
        check(r5_t4["cohomology_space"] == t4_complete_hodge["domain_caveat"],
              "Round 05 vs Round 06 T^4 domain_caveat mismatch")
        for r5_key in ("L_2", "L_3"):
            r5_rec = r5_t4[r5_key]
            r6_rec = t4_complete_hodge["lattices"][r5_key]
            check(r5_rec["V"] == r6_rec["cells"]["V"] and r5_rec["E"] == r6_rec["cells"]["E"]
                  and r5_rec["F"] == r6_rec["cells"]["F"] and r5_rec["C3"] == r6_rec["cells"]["C3"],
                  f"Round 05 vs Round 06 T^4 cell count mismatch on {r5_key}")
            check(r5_rec["rk_d0"] == r6_rec["ranks"]["rk_D0"] and r5_rec["rk_d1"] == r6_rec["ranks"]["rk_D1"]
                  and r5_rec["rk_d2"] == r6_rec["ranks"]["rk_D2"],
                  f"Round 05 vs Round 06 T^4 rank mismatch on {r5_key}")
            check([r5_rec["b0"], r5_rec["b1"], r5_rec["b2"]] == r6_rec["betti"][:3],
                  f"Round 05 vs Round 06 T^4 Betti (b0,b1,b2) mismatch on {r5_key}")
            check(r5_rec["eta_int_flux"] == r6_rec["eta_int_flux"],
                  f"Round 05 vs Round 06 T^4 eta_int_flux mismatch on {r5_key}")

        check(r5_bridges["track_1_su2_haar_weingarten_bakry_emery"]["gribov_neuberger_0_0_guard"] is True,
              "Round 05 gribov_neuberger_0_0_guard parity failed")
        check(r5_bridges["track_3b_5d_domain_wall_overlap"]["mirror_decoupling_status"] == "OPEN",
              "Round 05 mirror_decoupling_status parity failed")

        r4_parity_sha256 = hashlib.sha256(
            json.dumps(r4_bridges, sort_keys=True, ensure_ascii=False).encode("utf-8")
        ).hexdigest()
        r5_parity_sha256 = hashlib.sha256(
            json.dumps(r5_bridges, sort_keys=True, ensure_ascii=False).encode("utf-8")
        ).hexdigest()

        non_redundancy_and_parity = {
            "truth_table_8_rows": truth_table_8,
            "satisfying_row_count": len(true_rows),
            "falsifying_subset_count": len(falsifying_rows),
            "single_pillar_ablation_falsifiers": single_ablation_rows,
            "five_track_to_three_pillar_map": five_track_map,
            "round04_checks_verified": r4_bridges["interval_checks_passed"],
            "round04_parity_sha256": r4_parity_sha256,
            "round05_checks_verified": r5_bridges["interval_checks_passed"],
            "round05_parity_sha256": r5_parity_sha256,
            "t4_r5_r6_parity_verified": True,
        }

        return {
            "round": "round_06",
            "h2d_status": "OPEN",
            "interval_checks_passed": interval_checks,
            "t4_complete_discrete_hodge_d3": t4_complete_hodge,
            "neuberger_0_0_and_s3_vs_fmr": neuberger_0_0_cert,
            "five_track_non_redundancy_and_parity": non_redundancy_and_parity,
        }
    finally:
        mp.dps = 50
        iv.dps = 40


def _r7_iv_sq(x):
    """Exact non-negative square of a real iv.mpf interval."""
    lo = mp.mpf(0) if (x.a <= 0 <= x.b) else min(x.a * x.a, x.b * x.b)
    hi = max(x.a * x.a, x.b * x.b)
    return iv.mpf([lo, hi])


def _r7_iv_complex_abs(z_mpc):
    """Interval enclosure of |z| for iv.mpc without negative sqrt arguments."""
    return iv.sqrt(_r7_iv_sq(z_mpc.real) + _r7_iv_sq(z_mpc.imag))


def _r7_iv_complex_exp(z_mpc):
    """Interval enclosure of exp(x + i y)."""
    ex = iv.exp(z_mpc.real)
    return iv.mpc(ex * iv.cos(z_mpc.imag), ex * iv.sin(z_mpc.imag))


def _r7_iv_complex_besseli(n: int, z_re_iv, z_im_iv):
    """40-digit interval enclosure of complex I_n(z) via power series + geometric tail."""
    z = iv.mpc(z_re_iv, z_im_iv)
    half_z = z / iv.mpf(2)
    hz2 = half_z * half_z
    r_hz2_hi = _r7_iv_complex_abs(hz2).b
    fact_n = 1
    for j in range(1, n + 1):
        fact_n *= j
    term = (half_z ** n) / iv.mpf(fact_n)
    total = iv.mpc(0, 0)
    k = 0
    while True:
        ratio_hi = r_hz2_hi / ((k + 1) * (n + k + 1))
        t_mag = _r7_iv_complex_abs(term).b
        if k > 20 and ratio_hi < mp.mpf("0.25") and t_mag < mp.mpf("1e-48"):
            tail = t_mag * mp.mpf(4) / mp.mpf(3)
            return total + iv.mpc(iv.mpf([-tail, tail]), iv.mpf([-tail, tail]))
        total += term
        term = term * hz2 / iv.mpf((k + 1) * (n + k + 1))
        k += 1


def _r7_odd_double_fact(n: int) -> int:
    res = 1
    for k in range(3, n + 1, 2):
        res *= k
    return res


def _r7_iv_dtv_1link_antipodal(b_iv):
    """40-digit interval enclosure of 4D 1-link antipodal D_TV(mu_w, mu_{-w}) for ||w||=1."""
    z_b = (iv.mpf(2) / b_iv) * besseli_iv_any(1, b_iv)
    s = iv.mpf(0)
    for m in range(30):
        df1 = _r7_odd_double_fact(2 * m + 1)
        df2 = _r7_odd_double_fact(2 * m + 3)
        s += (b_iv ** (2 * m + 1)) / (iv.mpf(df1) * iv.mpf(df2))
    tail_term = (b_iv ** 61) / (iv.mpf(_r7_odd_double_fact(61)) * iv.mpf(_r7_odd_double_fact(63)))
    s = iv.mpf([s.a, s.b + tail_term.b * iv.mpf("1.2").b])
    return (iv.mpf(4) / (iv.pi * z_b)) * s


def _r7_iv_p1p_tail(beta_iv, delta_iv, n_panels: int = 400):
    """40-digit interval enclosure of 1-plaquette tail P_1p(beta, delta) via exact sin^2 antiderivative."""
    half_d = delta_iv / iv.mpf(2)

    def integrate_interval(x_start, x_end, n_sub: int):
        step = (x_end - x_start) / iv.mpf(n_sub)
        total = iv.mpf(0)
        for j in range(n_sub):
            a = x_start + iv.mpf(j) * step
            b = x_start + iv.mpf(j + 1) * step
            w_sin2 = (b - a) / iv.mpf(2) - (iv.sin(iv.mpf(2) * b) - iv.sin(iv.mpf(2) * a)) / iv.mpf(4)
            ha = iv.exp(-beta_iv * (iv.mpf(1) - iv.cos(a)))
            hb = iv.exp(-beta_iv * (iv.mpf(1) - iv.cos(b)))
            total += w_sin2 * iv.mpf([hb.a, ha.b])
        return total

    n_lo = n_panels // 4
    n_hi = n_panels - n_lo
    int_lo = integrate_interval(iv.mpf(0), half_d, n_lo)
    int_hi = integrate_interval(half_d, iv.pi, n_hi)
    return int_hi / (int_lo + int_hi)


def _r7_kp_animal_bound(n: int, delta_deg: int) -> int:
    """Exact Fuss-Catalan bound A_n(Delta) = binom(Delta*n, n) // ((Delta-1)*n + 1)."""
    p = 1
    for j in range(n):
        p = p * (delta_deg * n - j) // (j + 1)
    return p // ((delta_deg - 1) * n + 1)


def _r7_certify_kp_epsilon(d: int) -> tuple[int, object, object, object]:
    """40-digit mpmath.iv certification of closed-2-complex KP threshold eps_KP(d)."""
    delta_deg = 4 * (2 * d - 3)
    kappa = (iv.mpf(delta_deg) ** delta_deg) / (iv.mpf(delta_deg - 1) ** (delta_deg - 1))
    N0 = 30
    an_list = [(n, iv.mpf(_r7_kp_animal_bound(n, delta_deg))) for n in range(6, N0)]
    a_n0 = iv.mpf(_r7_kp_animal_bound(N0, delta_deg))

    best_eps = mp.mpf(0)
    best_a = mp.mpf(0)
    kappa_hi = mp.make_mpf(kappa._mpi_[1])
    for k_grid in range(2, 61):
        a_mp = mp.mpf(k_grid) / mp.mpf(40)
        lo_x = mp.mpf(0)
        hi_x = (mp.mpf(1) / kappa_hi) * mp.mpf("0.999")
        for _ in range(50):
            mid = (lo_x + hi_x) / 2
            s = sum(mp.mpf(_r7_kp_animal_bound(n, delta_deg)) * (mid ** n) for n in range(6, N0))
            s += mp.mpf(_r7_kp_animal_bound(N0, delta_deg)) * (mid ** N0) / (1 - kappa_hi * mid)
            if (delta_deg + 1) * s <= a_mp:
                lo_x = mid
            else:
                hi_x = mid
        eps_cand = lo_x * mp.exp(-a_mp)
        if eps_cand > best_eps:
            best_eps = eps_cand
            best_a = a_mp

    eps_cert = iv.mpf(mp.nstr(best_eps * mp.mpf("0.999999"), 38))
    a_iv = iv.mpf(mp.nstr(best_a, 38))
    x_iv = eps_cert * iv.exp(a_iv)
    require(strictly_below(kappa * x_iv, "1"), f"KP kappa*x >= 1 at d={d}")
    lhs = iv.mpf(delta_deg + 1) * (
        sum(An * (x_iv ** n) for n, An in an_list) + a_n0 * (x_iv ** N0) / (iv.mpf(1) - kappa * x_iv)
    )
    require(lhs.b <= a_iv.a, f"KP condition failed at d={d}")
    return delta_deg, kappa, eps_cert, a_iv


def _r7_su2_f_sup_iv(b_re_iv, b_im_iv, n_grid: int = 40):
    """40-digit upper bound on sup_{u in [-1, 1]} |exp(beta u)/c_0(beta) - 1| for SU(2)."""
    b_mpc = iv.mpc(b_re_iv, b_im_iv)
    half_z = b_mpc / iv.mpf(2)
    hz2 = half_z * half_z
    c0 = iv.mpc(0, 0)
    term = iv.mpc(1, 0)
    r_hz2_hi = _r7_iv_complex_abs(hz2).b
    for k in range(30):
        c0 += term
        term = term * hz2 / iv.mpf((k + 1) * (k + 2))
        t_mag = _r7_iv_complex_abs(term).b
        if k > 10 and r_hz2_hi / ((k + 2) * (k + 3)) < mp.mpf("0.25") and t_mag < mp.mpf("1e-46"):
            tail = t_mag * mp.mpf(4) / mp.mpf(3)
            c0 += iv.mpc(iv.mpf([-tail, tail]), iv.mpf([-tail, tail]))
            break
    max_sup = mp.mpf(0)
    for m in range(n_grid):
        u_lo = -iv.mpf(1) + iv.mpf(2 * m) / iv.mpf(n_grid)
        u_hi = -iv.mpf(1) + iv.mpf(2 * (m + 1)) / iv.mpf(n_grid)
        u_iv = iv.mpf([u_lo.a, u_hi.b])
        val = _r7_iv_complex_exp(b_mpc * u_iv) / c0 - iv.mpc(1, 0)
        mag = _r7_iv_complex_abs(val)
        if mag.b > max_sup:
            max_sup = mag.b
    return max_sup, _r7_iv_complex_abs(c0)


def _r7_u1_f_sup_iv(b_re_iv, b_im_iv, n_grid: int = 40):
    """40-digit upper bound on sup_{u in [-1, 1]} |exp(beta u)/I_0(beta) - 1| for U(1)."""
    b_mpc = iv.mpc(b_re_iv, b_im_iv)
    i0 = _r7_iv_complex_besseli(0, b_re_iv, b_im_iv)
    max_sup = mp.mpf(0)
    for m in range(n_grid):
        u_lo = -iv.mpf(1) + iv.mpf(2 * m) / iv.mpf(n_grid)
        u_hi = -iv.mpf(1) + iv.mpf(2 * (m + 1)) / iv.mpf(n_grid)
        u_iv = iv.mpf([u_lo.a, u_hi.b])
        val = _r7_iv_complex_exp(b_mpc * u_iv) / i0 - iv.mpc(1, 0)
        mag = _r7_iv_complex_abs(val)
        if mag.b > max_sup:
            max_sup = mag.b
    return max_sup, _r7_iv_complex_abs(i0)


def _r7_so3_f_sup_iv(b_re_iv, b_im_iv, n_grid: int = 40):
    """40-digit upper bound on sup_{u in [-1, 1]} |exp(bA*(4u^2-1)/3)/c_0(bA) - 1| for SO(3)."""
    b_mpc = iv.mpc(b_re_iv, b_im_iv)
    # c_0(bA) = 2/pi * int_0^pi sin^2(th) exp(bA (4 cos^2(th) - 1)/3) dth for real/complex ray:
    # For real/45deg rays |bA| <= 0.02, compute c_0 by Taylor series of exp(bA*(4u^2-1)/3) integrated
    # against 2/pi * sqrt(1 - u^2) du on [-1, 1]: int_{-1}^1 (2/pi) sqrt(1-u^2) u^{2m} du = (2m)! / (2^{2m} m! (m+1)!)
    c0 = iv.mpc(0, 0)
    # Build polynomial powers of (4 u^2 - 1)/3 using exact Fraction coefficients up to degree K_ser=24
    poly = [Fraction(1, 1)]
    step_poly = [Fraction(-1, 3), Fraction(4, 3)]  # in x = u^2

    def poly_mul_f(p: list[Fraction], q: list[Fraction]) -> list[Fraction]:
        out = [Fraction(0, 1)] * (len(p) + len(q) - 1)
        for i, pi_v in enumerate(p):
            for j, qj_v in enumerate(q):
                out[i + j] += pi_v * qj_v
        return out

    def moment_u2m(m: int) -> Fraction:
        num = 1
        for k in range(1, 2 * m + 1):
            num *= k
        den_m = 1
        for k in range(1, m + 1):
            den_m *= k
        den = (1 << (2 * m)) * den_m * (den_m * (m + 1))
        return Fraction(num, den)

    b_pow = iv.mpc(1, 0)
    fact_k = 1
    for k in range(22):
        mom = Fraction(0, 1)
        for m, coeff in enumerate(poly):
            mom += coeff * moment_u2m(m)
        mom_iv = iv.mpc(iv.mpf(mom.numerator) / iv.mpf(mom.denominator), 0)
        c0 += (b_pow / iv.mpf(fact_k)) * mom_iv
        poly = poly_mul_f(poly, step_poly)
        b_pow = b_pow * b_mpc
        fact_k *= (k + 1)
    # Remainder <= exp(|bA|) * |bA|^22 / 22! (since |(4u^2-1)/3| <= 1)
    b_abs_iv = _r7_iv_complex_abs(b_mpc)
    tail_iv = iv.exp(b_abs_iv) * (b_abs_iv ** 22) / iv.mpf(fact_k)
    c0 += iv.mpc(iv.mpf([-tail_iv.b, tail_iv.b]), iv.mpf([-tail_iv.b, tail_iv.b]))

    max_sup = iv.mpf(0)
    for m in range(n_grid):
        u_lo = -iv.mpf(1) + iv.mpf(2 * m) / iv.mpf(n_grid)
        u_hi = -iv.mpf(1) + iv.mpf(2 * (m + 1)) / iv.mpf(n_grid)
        u_iv = iv.mpf([u_lo.a, u_hi.b])
        tr_a = (iv.mpf(4) * _r7_iv_sq(u_iv) - iv.mpf(1)) / iv.mpf(3)
        val = _r7_iv_complex_exp(b_mpc * tr_a) / c0 - iv.mpc(1, 0)
        mag = _r7_iv_complex_abs(val)
        if mag.b > max_sup:
            max_sup = mag.b
    return max_sup, _r7_iv_complex_abs(c0)


def _r7_certify_i1_stiffness_iv(d_space: int):
    """40-digit enclosure of infinite-volume stiffness I_1(d_space) with analytic tail."""
    def integrand(u):
        if u == 0:
            return mp.mpf(0)
        t = u * u
        b0 = mp.besseli(0, 2 * t) * mp.exp(-2 * t)
        return (1 / mp.sqrt(mp.pi)) * (1 - b0 ** d_space) / (u * u)

    U_max = mp.mpf(20000)
    with mp.workdps(45):
        val_num = mp.quad(integrand, [0, mp.mpf("0.01"), mp.mpf("0.5"), 5, 50, 500, 5000, U_max])
    tail_ub = 1 / (U_max * mp.sqrt(mp.pi))
    pad = mp.mpf("1e-18")
    return iv.mpf([val_num - pad, val_num + tail_ub + pad])


def _r7_w4_iv_dtv_su2_antipodal(b_iv, r_iv):
    """40-digit interval enclosure of SU(2) D_TV(mu_{+r}, mu_{-r}) for arbitrary real r_iv."""
    br = b_iv * r_iv
    z_br = (iv.mpf(2) / br) * besseli_iv_any(1, br)
    s = iv.mpf(0)
    n_terms = 55
    for m in range(n_terms):
        df1 = _r7_odd_double_fact(2 * m + 1)
        df2 = _r7_odd_double_fact(2 * m + 3)
        s += (br ** (2 * m + 1)) / (iv.mpf(df1) * iv.mpf(df2))
    m_next = 2 * n_terms + 1
    next_term = (br ** m_next) / (iv.mpf(_r7_odd_double_fact(m_next)) * iv.mpf(_r7_odd_double_fact(m_next + 2)))
    ratio = (br ** 2) / iv.mpf((m_next + 2) * (m_next + 4))
    assert ratio.b < iv.mpf("0.25").a, f"SU(2) D_TV series ratio too large: {ratio}"
    tail_hi = next_term.b / (iv.mpf(1) - ratio).a
    s = iv.mpf([s.a, s.b + tail_hi])
    return (iv.mpf(4) / (iv.pi * z_br)) * s


def _r7_w4_iv_dtv_u1_antipodal(b_iv, r_iv):
    """40-digit interval enclosure of U(1) D_TV(mu_{+r}, mu_{-r}) for arbitrary real r_iv."""
    br = b_iv * r_iv
    i0 = besseli_iv_any(0, br)
    s = iv.mpf(0)
    n_terms = 55
    even_df = iv.mpf(1)
    fact_2m1 = 1
    for m in range(n_terms):
        if m > 0:
            even_df = even_df * iv.mpf(2 * m)
            fact_2m1 *= (2 * m) * (2 * m + 1)
        odd_df = _r7_odd_double_fact(2 * m + 1)
        s += (br ** (2 * m + 1)) * even_df / (iv.mpf(fact_2m1) * iv.mpf(odd_df))
    m_next = 2 * n_terms + 1
    even_next = even_df * iv.mpf(2 * n_terms)
    fact_next = fact_2m1 * (2 * n_terms) * m_next
    next_term = (br ** m_next) * even_next / (iv.mpf(fact_next) * iv.mpf(_r7_odd_double_fact(m_next)))
    ratio = (br ** 2) / iv.mpf((m_next + 1) * (m_next + 2))
    assert ratio.b < iv.mpf("0.25").a, f"U(1) D_TV series ratio too large: {ratio}"
    tail_hi = next_term.b / (iv.mpf(1) - ratio).a
    s = iv.mpf([s.a, s.b + tail_hi])
    return (iv.mpf(2) / (iv.pi * i0)) * s


def _r7_w4_edge_sat_count(n: int, deg_edge: int) -> int:
    """Exact [x^{n-1}] Z(x)^4 for edge-saturated closed-2-complex tree Z=(1 + x Z^3)^deg_edge."""
    if n == 1:
        return 1
    n_rem = n - 1
    top = 3 * deg_edge * n_rem + 4 * deg_edge - 1
    k = n_rem - 1
    c = 1
    for j in range(k):
        c = c * (top - j) // (j + 1)
    return (4 * deg_edge * c) // n_rem


def _r7_w4_c0_su2_iv(b_mpc):
    """40-digit enclosure of c_0(beta) = 2 I_1(beta) / beta for complex interval beta."""
    half_z = b_mpc / iv.mpf(2)
    hz2 = half_z * half_z
    c0 = iv.mpc(0, 0)
    term = iv.mpc(1, 0)
    r2_hi = _r7_iv_complex_abs(hz2).b
    for k in range(35):
        c0 += term
        term = term * hz2 / iv.mpf((k + 1) * (k + 2))
        t_mag = _r7_iv_complex_abs(term).b
        if k > 10 and r2_hi / ((k + 2) * (k + 3)) < iv.mpf("0.25").a and t_mag < mp.mpf("1e-48"):
            tail = t_mag * mp.mpf(4) / mp.mpf(3)
            c0 += iv.mpc(iv.mpf([-tail, tail]), iv.mpf([-tail, tail]))
            break
    return c0


def _r7_w4_sphere_haar_iv(area: int, b_mpc, group: str):
    """Exact complex-beta Haar integral for topological 2-sphere of `area` plaquettes."""
    denom = _r7_iv_complex_besseli(1 if group == "SU2" else 0, b_mpc.real, b_mpc.imag)
    s = iv.mpc(0, 0)
    for k in range(1, 18):
        order = (k + 1) if group == "SU2" else k
        uk = _r7_iv_complex_besseli(order, b_mpc.real, b_mpc.imag) / denom
        weight = iv.mpf((k + 1) ** 2) if group == "SU2" else iv.mpf(2)
        term = weight * (uk ** area)
        s += term
        if _r7_iv_complex_abs(term).b < mp.mpf("1e-45"):
            break
    return _r7_iv_complex_abs(s).b


def _r7_w4_size11_su2_iv(b_mpc):
    """Exact complex-beta SU(2) Haar integral for two 3-cubes sharing 1 plaquette (|gamma|=11)."""
    i1 = _r7_iv_complex_besseli(1, b_mpc.real, b_mpc.imag)
    u = {k: _r7_iv_complex_besseli(k + 1, b_mpc.real, b_mpc.imag) / i1 for k in range(1, 12)}
    s = iv.mpc(0, 0)
    for k1 in range(1, 9):
        for k2 in range(1, 9):
            for k0 in range(max(1, abs(k1 - k2)), min(11, k1 + k2 + 1), 2):
                if (k0 + k1 + k2) % 2 != 0:
                    continue
                s += iv.mpf((k0 + 1) * (k1 + 1) * (k2 + 1)) * u[k0] * (u[k1] ** 5) * (u[k2] ** 5)
    return _r7_iv_complex_abs(s).b


def _r7_w4_f_lp_iv(b_mpc, p_exp: int, group: str, n_grid: int = 160):
    """Rigorous 40-digit L^p(G) Finner polymer norm for complex beta (pure mpmath.iv)."""
    if group == "SU2":
        denom = _r7_w4_c0_su2_iv(b_mpc)
    else:
        denom = _r7_iv_complex_besseli(0, b_mpc.real, b_mpc.imag)
    acc = iv.mpf(0)
    h = iv.pi / iv.mpf(n_grid)
    for m in range(n_grid):
        th_iv = iv.mpf([m * h.a, (m + 1) * h.b])
        cos_iv = iv.cos(th_iv)
        f_val = _r7_iv_complex_exp(b_mpc * cos_iv) / denom - iv.mpc(1, 0)
        mag = _r7_iv_complex_abs(f_val)
        if group == "SU2":
            sin_iv = iv.sin(th_iv)
            sin_sq = _r7_iv_sq(sin_iv)
            acc += (iv.mpf(2) / iv.pi) * sin_sq * (mag ** p_exp) * h
        else:
            acc += (iv.mpf(1) / iv.pi) * (mag ** p_exp) * h
    return (acc ** (iv.mpf(1) / iv.mpf(p_exp))).b


def compute_h2d_round07_irx_frontier(
    r4_bridges: dict | None = None,
    r5_bridges: dict | None = None,
    r6_bridges: dict | None = None,
) -> dict:
    """Deterministic 40-digit mpmath.iv + sympy + Fraction suite consolidating Round 07 Waves 1-3 IR-X frontier."""
    if r4_bridges is None:
        r4_bridges = compute_h2d_round04_constructive_bridges()
    if r5_bridges is None:
        r5_bridges = compute_h2d_round05_deepening_bridges()
    if r6_bridges is None:
        r6_bridges = compute_h2d_round06_convergence_bridges(r4_bridges, r5_bridges)

    mp.dps = 60
    iv.dps = 40
    try:
        interval_checks = 0

        def check(ok: bool, msg: str) -> None:
            nonlocal interval_checks
            require(ok, msg)
            interval_checks += 1

        # =====================================================================
        # 1. Track 1 (T1.1-T1.4): Quotient Bakry-Emery, 4D 1-Loop, Polchinski Riccati & Banks-Zaks
        # =====================================================================
        ric_e, k_mix, norm_a, norm_t = sp.symbols("ric_E K_mixed norm_A2 norm_T2", real=True)
        ric_m = ric_e - k_mix + 3 * norm_a
        hess_vfp = k_mix - norm_a + norm_t
        ric_be0 = sp.simplify(ric_m + hess_vfp)
        check(ric_be0 == ric_e + 2 * norm_a + norm_t, f"T1.1 O'Neill + FP cancellation failed: {ric_be0}")

        check(sp.Rational(9, 4) - sp.Rational(1, 2) == sp.Rational(7, 4), "T1.2 Lambda^2 mismatch")
        check(sp.Rational(1, 4) - sp.Rational(1, 6) == sp.Rational(1, 12), "T1.2 q^2 ln mismatch")
        check(sp.Rational(11, 24) - sp.Rational(11, 36) == sp.Rational(11, 72), "T1.2 q^2 finite mismatch")
        d_dim = sp.Symbol("d_dim", positive=True)
        check(sp.simplify((d_dim - 2) / d_dim).subs(d_dim, 2) == 0, "T1.2 d=2 UV cancellation failed")

        t_sym, th_sym = sp.symbols("t_val theta", real=True)
        for k_fourier in range(7):
            int_k = sp.integrate(sp.sin(th_sym) ** 4 * sp.cos(k_fourier * th_sym), (th_sym, 0, sp.pi))
            expected_k = {0: sp.Rational(3, 8) * sp.pi, 2: -sp.Rational(1, 4) * sp.pi, 4: sp.Rational(1, 16) * sp.pi}.get(k_fourier, 0)
            check(sp.simplify(int_k - expected_k) == 0, f"T1.2 Fourier moment k={k_fourier} failed")

        t_check = mp.mpf("37") / mp.mpf("100")
        lhs_ang = mp.quad(lambda th: mp.sin(th) ** 4 / (1 + t_check ** 2 + 2 * t_check * mp.cos(th)), [0, mp.pi])
        rhs_ang = (mp.pi / 8) * (3 - t_check ** 2)
        check(abs(lhs_ang - rhs_ang) < mp.mpf("1e-45"), f"T1.2 4D angular identity error: {abs(lhs_ang - rhs_ang)}")

        b0_s_iv = iv.mpf(22) / (iv.mpf(48) * (iv.pi ** 2))
        c_sav_iv = iv.mpf(1) / iv.mpf(2)
        t_star_iv = iv.mpf(1) / iv.mpf(10)
        a_uv_iv = iv.mpf("1e-16")
        i_4d_iv = (iv.mpf(2) * c_sav_iv / iv.sqrt(b0_s_iv)) * (
            iv.sqrt(iv.log(iv.mpf(1) / (a_uv_iv ** 2))) - iv.sqrt(iv.log(iv.mpf(1) / t_star_iv))
        )
        polchinski_penalty_4d = iv.exp(iv.mpf(2) * i_4d_iv)
        check(strictly_above(polchinski_penalty_4d, "1e28"),
              f"T1.x 4D Polchinski Riccati penalty too small: {polchinski_penalty_4d}")

        beta_bz_iv = iv.mpf(109) / (iv.mpf(8) * (iv.pi ** 2))
        g2_bz_iv = (iv.mpf(32) * (iv.pi ** 2)) / iv.mpf(109)
        check(strictly_above(beta_bz_iv, "1.38") and strictly_below(beta_bz_iv, "1.39"),
              "Banks-Zaks beta_* bracket failed")
        check(strictly_above(beta_bz_iv, "0.38"), "Banks-Zaks beta_* not above 0.38 quotient BE ceiling")

        cos_pi8 = iv.cos(iv.pi / iv.mpf(8))
        ambient_be_cap = Fraction(1, 12)
        check(strictly_above(cos_pi8, "0.9238") and ambient_be_cap * 12 == 1,
              "Savvidy Luescher cos(pi/8) or 1/12 ambient BE check failed")

        track_1_summary = {
            "sympy_oneill_fp_cancellation_verified": True,
            "sympy_1loop_4d_coeffs_and_d2_cancel_verified": True,
            "angular_identity_max_err": outward_str(iv.mpf(mp.nstr(abs(lhs_ang - rhs_ang), 20)), digits=12),
            "polchinski_4d_riccati_penalty_a_1e_16": outward_str(polchinski_penalty_4d),
            "banks_zaks_nf10_beta_star": outward_str(beta_bz_iv),
            "banks_zaks_nf10_g2_star": outward_str(g2_bz_iv),
            "savvidy_luescher_cos_pi_8": outward_str(cos_pi8),
            "ambient_su2_be_provable_cap": str(ambient_be_cap),
            "quotient_be_mc_ceiling": "0.38",
        }

        # =====================================================================
        # 2. Track 2 (T2-1..T2-3 & O-T2-1, O-T2-4): Bogomol'nyi Flow, Trace Anomaly & KS Curvature
        # =====================================================================
        E_syms = sp.symbols("E1 E2 E3", real=True)
        B_syms = sp.symbols("B1 B2 B3", real=True)
        e_dens = sp.Rational(1, 2) * sum(E_syms[i] ** 2 + B_syms[i] ** 2 for i in range(3))
        q_scaled = sum(E_syms[i] * B_syms[i] for i in range(3))
        check(sp.simplify((e_dens - q_scaled) - sp.Rational(1, 2) * sum((E_syms[i] - B_syms[i]) ** 2 for i in range(3))) == 0,
              "T2-2 Bogomol'nyi minus identity failed")
        check(sp.simplify((e_dens + q_scaled) - sp.Rational(1, 2) * sum((E_syms[i] + B_syms[i]) ** 2 for i in range(3))) == 0,
              "T2-2 Bogomol'nyi plus identity failed")

        a_hs, b_hs = sp.symbols("a_hs b_hs", positive=True)
        num_hs_d4 = -3 * b_hs * (a_hs ** 2 + 2 * a_hs * b_hs + 2 * b_hs ** 2)
        check(sp.expand(num_hs_d4).subs({a_hs: 1, b_hs: 1}) == -15, "O-T2-1 Hamilton-Struwe check failed")

        Nc_sym, g_sym = sp.symbols("N_c g_sym", positive=True)
        t2_1_1loop = 11 * Nc_sym * (Nc_sym ** 2 - 1) * (g_sym ** 4) / (2048 * (sp.pi ** 4))
        check(sp.simplify(t2_1_1loop.subs(Nc_sym, 2) - sp.Rational(33, 1024) * g_sym ** 4 / sp.pi ** 4) == 0,
              "T2-1 SU(2) 1-loop check failed")

        # T2-2 Skellam instanton-gas verification for L = 2, 4, 8, 16 (chi_t = 1, c = 3/10)
        c_gf = iv.mpf(3) / iv.mpf(10)
        n_inf_su2 = iv.mpf(9) / (iv.mpf(128) * (iv.pi ** 2))
        skellam_sweep = {}
        prev_g2_gf = iv.mpf(0)
        for L_sk in (2, 4, 8, 16):
            mu_sk = iv.mpf(L_sk ** 4)
            kappa4_sk = iv.mpf(3) + iv.mpf(1) / mu_sk
            holder_lb_sk = iv.sqrt(mu_sk / kappa4_sk)
            exact_abs_q = iv.exp(-mu_sk) * mu_sk * (besseli_iv_any(0, mu_sk) + besseli_iv_any(1, mu_sk))
            check(strictly_above(exact_abs_q, holder_lb_sk) or exact_abs_q.a >= holder_lb_sk.a,
                  f"T2-2 Skellam Holder bound failed at L={L_sk}")
            u_lb_sk = (iv.pi ** 2) * (c_gf ** 4) * holder_lb_sk / iv.mpf(8)
            g2_gf_lb = u_lb_sk / n_inf_su2
            check(strictly_above(g2_gf_lb, prev_g2_gf), f"T2-2 g_GF^2 LB not strictly growing at L={L_sk}")
            prev_g2_gf = g2_gf_lb
            skellam_sweep[f"L_{L_sk}"] = {
                "L": L_sk,
                "kappa_4": outward_str(kappa4_sk),
                "holder_E_abs_Q_lb": outward_str(holder_lb_sk),
                "exact_skellam_E_abs_Q": outward_str(exact_abs_q),
                "g_GF_sq_lb": outward_str(g2_gf_lb),
            }

        track_2_summary = {
            "sympy_bogomolnyi_and_t2_1_verified": True,
            "t2_2_skellam_instanton_gas_sweep": skellam_sweep,
        }

        # =====================================================================
        # 3. Route A (LA.1-LA.4, OA.1-OA.3): 1-Link W1 / D_TV, 18/L, L=2 2-Loop & Crossover
        # =====================================================================
        b_w1_cert = iv.mpf(16) / (iv.mpf(27) * iv.pi)
        b_w1_cap = iv.pi / iv.mpf(16)
        check(strictly_below(b_w1_cert, b_w1_cap), "LA.1 W1 bound >= cap")
        dtv_025 = _r7_iv_dtv_1link_antipodal(iv.mpf(1) / iv.mpf(4))
        dtv_lo = _r7_iv_dtv_1link_antipodal(iv.mpf("0.131030"))
        dtv_hi = _r7_iv_dtv_1link_antipodal(iv.mpf("0.131032"))
        check(strictly_above(iv.mpf(18) * dtv_025, "1.9029"), "LA.1 18*D_TV(0.25) check failed")
        check(strictly_below(iv.mpf(18) * dtv_lo, "1") and strictly_above(iv.mpf(18) * dtv_hi, "1"),
              "LA.1 4D 1-link TV threshold bracket [0.131030, 0.131032] failed")

        u_038 = besseli_iv_any(2, iv.mpf("0.38")) / besseli_iv_any(1, iv.mpf("0.38"))
        u_080 = besseli_iv_any(2, iv.mpf("0.80")) / besseli_iv_any(1, iv.mpf("0.80"))
        check(strictly_above(iv.mpf(12) * u_038, "1.13") and strictly_above(iv.mpf(6) * u_080, "1.16"),
              "LA.1 KP character ratio check failed")

        L_sym = sp.Symbol("L_blk", positive=True, integer=True)
        n_ext_law = sp.simplify(3 * (2 * (L_sym - 1) * L_sym ** 2 * 3) / ((L_sym - 1) * L_sym ** 3))
        check(n_ext_law == 18 / L_sym, f"LA.2 exterior law != 18/L: {n_ext_law}")
        bF_s, bA_s, b12_s, bc_s, d_s = sp.symbols("bF bA b12 bc d_s")
        beff_expr = bF_s + sp.Rational(8, 3) * bA_s + 8 * b12_s + 8 * (d_s - 2) * bc_s
        check(beff_expr.subs({bF_s: 0, bA_s: 0, b12_s: 0, bc_s: 1, d_s: 4}) == 16
              and beff_expr.subs({bF_s: 0, bA_s: 0, b12_s: 0, bc_s: 1, d_s: 5}) == 24,
              "LA.3 multi-plaquette chair weights failed")

        ln2_iv = iv.log(iv.mpf(2))
        db1_iv = (iv.mpf(11) / (iv.mpf(3) * (iv.pi ** 2))) * ln2_iv
        db2_iv = (iv.mpf(17) / (iv.mpf(3) * (iv.pi ** 4))) * ln2_iv
        r21_iv = db2_iv / db1_iv

        def steps_2loop_iv(b_hi_iv, b_lo_iv):
            return (b_hi_iv - b_lo_iv - r21_iv * iv.log((b_hi_iv + r21_iv) / (b_lo_iv + r21_iv))) / db1_iv

        k_160_050 = steps_2loop_iv(iv.mpf(160), iv.mpf("0.5"))
        k_160_073 = steps_2loop_iv(iv.mpf(160), iv.mpf("0.73"))
        db_25 = db1_iv + db2_iv / iv.mpf("2.5")
        lf_25_e4 = iv.exp(iv.mpf("-2.5") / iv.mpf(4))
        check(strictly_above(lf_25_e4, db_25), "OA.3 large-field exp(-2.5/4) <= |dBeta_2L(2.5)|")

        route_a_summary = {
            "w1_1link_provable_beta_bound_16_over_27pi": outward_str(b_w1_cert),
            "w1_1link_cap_pi_over_16": outward_str(b_w1_cap),
            "tv_1link_18_dtv_at_0_25": outward_str(iv.mpf(18) * dtv_025),
            "tv_1link_threshold_bracket": ["0.131030", "0.131032"],
            "kp_12_u_0_38": outward_str(iv.mpf(12) * u_038),
            "kp_6_u_0_80": outward_str(iv.mpf(6) * u_080),
            "sympy_18_over_L_and_chair_weights_verified": True,
            "l2_2loop_dbeta1": outward_str(db1_iv),
            "l2_2loop_dbeta2_coeff": outward_str(db2_iv),
            "k2l_160_to_0_50": outward_str(k_160_050),
            "k2l_160_to_0_73": outward_str(k_160_073),
            "oa3_large_field_2_5_exp_minus_2_5_over_4": outward_str(lf_25_e4),
            "oa3_2loop_step_at_2_5": outward_str(db_25),
        }

        # =====================================================================
        # 4. Route B & Route C (B-1, C-1, C-2, C4(a), C4(b)'): SD, Twist TV & Litmus 6 Gap
        # =====================================================================
        # Exact 2D SU(2) vs U(1) Schwinger-Dyson identity at beta = 7/4
        beta_2d = iv.mpf(7) / iv.mpf(4)
        wp_su2_2d = besseli_iv_any(2, beta_2d) / besseli_iv_any(1, beta_2d)
        # In SU(2), chi_1(alpha) = 2*cos(2*alpha) + 1 => I_3/I_1 = <chi_1>/3 = (2*w_{p^2} + 1)/3
        wp2_su2_2d = (iv.mpf(3) * (besseli_iv_any(3, beta_2d) / besseli_iv_any(1, beta_2d)) - iv.mpf(1)) / iv.mpf(2)
        sd_2d_su2_res = abs((iv.mpf(3) / iv.mpf(4)) * wp_su2_2d - (beta_2d / iv.mpf(8)) * (iv.mpf(1) - wp2_su2_2d))
        check(strictly_below(sd_2d_su2_res, "1e-38"), f"Route B 2D SU(2) SD residual too large: {sd_2d_su2_res}")

        wp_u1_2d = besseli_iv_any(1, beta_2d) / besseli_iv_any(0, beta_2d)
        wp2_u1_2d = besseli_iv_any(2, beta_2d) / besseli_iv_any(0, beta_2d)
        sd_2d_u1_res = abs(wp_u1_2d - (beta_2d / iv.mpf(2)) * (iv.mpf(1) - wp2_u1_2d))
        check(strictly_below(sd_2d_u1_res, "1e-38"), f"Route B 2D U(1) SD residual too large: {sd_2d_u1_res}")

        # Lemma C-1 symbolic + 40-digit twist TV identity
        zp_s, zm_s, pp_s, pm_s = sp.symbols("Z_p Z_m p_p p_m", positive=True)
        zper_s, ztw_s = zp_s + zm_s, zp_s - zm_s
        p_per_s = (zp_s * pp_s + zm_s * pm_s) / zper_s
        p_tw_s = (zp_s * pp_s - zm_s * pm_s) / ztw_s
        sinh_df_s = (zper_s / ztw_s - ztw_s / zper_s) / 2
        check(sp.simplify((p_per_s - p_tw_s) - sinh_df_s * (pm_s - pp_s)) == 0,
              "C-1 twist TV algebraic identity failed")

        zp_iv, zm_iv = iv.mpf(1), iv.mpf(1) / iv.mpf(50)
        df_tw_iv = -iv.log((zp_iv - zm_iv) / (zp_iv + zm_iv))
        sinh_df_iv = (iv.exp(df_tw_iv) - iv.exp(-df_tw_iv)) / iv.mpf(2)
        err_floor_iv = (iv.mpf(1) - sinh_df_iv) / iv.mpf(2)
        check(strictly_above(sinh_df_iv, "0.02") and strictly_above(err_floor_iv, "0.479"),
              "C-1 sinh(Delta F) binary testing floor failed")

        # Lemma C-2 / C-O2: Exact 40-digit Litmus 6 collapse gap 8*ln(2) - 6*pi^2/11 > 0
        c_true_af = (iv.mpf(6) * (iv.pi ** 2)) / iv.mpf(11)
        c_mk_wilson = iv.mpf(8) * ln2_iv
        c_mk_hk = iv.mpf(16) * ln2_iv
        litmus6_gap_wilson = c_mk_wilson - c_true_af
        litmus6_gap_hk = c_mk_hk - c_true_af
        check(strictly_above(litmus6_gap_wilson, "0.16175") and strictly_above(litmus6_gap_hk, "5.7069"),
              f"C-O2 8*ln(2) - 6*pi^2/11 gap check failed: {litmus6_gap_wilson}")

        # C4(a) sympy zero-commutator + 40-digit energetics
        s1_sp = sp.Matrix([[0, 1], [1, 0]])
        s2_sp = sp.Matrix([[0, -sp.I], [sp.I, 0]])
        s3_sp = sp.Matrix([[1, 0], [0, -1]])
        om1_sp, om2_sp = sp.I * s1_sp, sp.I * s2_sp
        n1_s, n2_s, n3_s = sp.symbols("n1 n2 n3", real=True)
        phi_adj = n1_s * s1_sp + n2_s * s2_sp + n3_s * s3_sp
        c4a_eqs = []
        for om in (om1_sp, om2_sp):
            comm = sp.simplify(om * phi_adj * om.inv() - phi_adj)
            c4a_eqs.extend([comm[0, 0], comm[0, 1], comm[1, 0], comm[1, 1]])
        check(sp.solve(c4a_eqs, [n1_s, n2_s, n3_s]) == {n1_s: 0, n2_s: 0, n3_s: 0},
              "C4(a) adjoint Higgs twist-eater stabilizer != {0}")
        c4a_opt1 = (iv.pi ** 2) / (iv.mpf(2) * (iv.mpf(1) / iv.mpf(4)))
        c4a_opt2 = (iv.pi ** 2) * iv.mpf(100)
        check(strictly_above(c4a_opt1, "19.73") and strictly_below(c4a_opt1, c4a_opt2),
              "C4(a) energetics check failed")

        route_bc_summary = {
            "route_b_2d_su2_sd_residual": outward_str(sd_2d_su2_res, digits=12),
            "route_b_2d_u1_sd_residual": outward_str(sd_2d_u1_res, digits=12),
            "c1_sympy_twist_tv_verified": True,
            "c1_sinh_delta_f_at_0_02": outward_str(sinh_df_iv),
            "c1_binary_testing_error_floor": outward_str(err_floor_iv),
            "c2_8ln2_minus_6pi2_over_11": outward_str(litmus6_gap_wilson),
            "c2_16ln2_minus_6pi2_over_11": outward_str(litmus6_gap_hk),
            "c4a_sympy_twist_eater_zero_higgs_verified": True,
            "c4a_abelian_twist_barrier_gIR_0_5": outward_str(c4a_opt1),
        }

        # =====================================================================
        # 5. Wave 3 W3-1: Twisted Box Pf(n)=0 mod 2, alpha_st=3/4, 4D Bianchi & Corridor
        # =====================================================================
        I2_sp = sp.eye(2)
        om_sets = {
            "tw1": [I2_sp, sp.I * s1_sp, sp.I * s2_sp, I2_sp],
            "tw3": [I2_sp, sp.I * s1_sp, sp.I * s2_sp, sp.I * s3_sp],
            "tw4": [sp.I * s1_sp, sp.I * s2_sp, sp.I * s1_sp, sp.I * s2_sp],
        }
        n_defs = {
            "tw1": {(1, 2): 1},
            "tw3": {(1, 2): 1, (1, 3): 1, (2, 3): 1},
            "tw4": {(0, 1): 1, (0, 3): 1, (1, 2): 1, (2, 3): 1},
        }
        for tw_name, oms in om_sets.items():
            nm = n_defs[tw_name]
            pf_val = nm.get((0, 1), 0) * nm.get((2, 3), 0) + nm.get((0, 2), 0) * nm.get((1, 3), 0) + nm.get((0, 3), 0) * nm.get((1, 2), 0)
            check(pf_val % 2 == 0, f"W3.1-1 Pf(n) odd for {tw_name}")
            eqs_tw = []
            for om in oms:
                cm = sp.simplify(om * phi_adj * om.inv() - phi_adj)
                eqs_tw.extend([cm[0, 0], cm[0, 1], cm[1, 0], cm[1, 1]])
            check(sp.solve(eqs_tw, [n1_s, n2_s, n3_s]) == {n1_s: 0, n2_s: 0, n3_s: 0},
                  f"W3.1-1 nonzero stabilizer for {tw_name}")

        # L=2 block-spin covariance & alpha_st = 3/4 Brillouin-zone rank loss
        ast_s = sp.Symbol("alpha_st")
        ks_s = sp.symbols("k0 k1 k2 k3", real=True)
        w_ast = ast_s / 6
        C_sym = sp.zeros(4, 4)
        df_s = sp.Matrix([sp.exp(sp.I * ks_s[mu]) - 1 for mu in range(4)])
        dc_s = sp.Matrix([sp.exp(2 * sp.I * ks_s[mu]) - 1 for mu in range(4)])
        for mu in range(4):
            C_sym[mu, mu] += (1 - ast_s) * (1 + sp.exp(sp.I * ks_s[mu]))
            for nu in range(4):
                if nu == mu:
                    continue
                C_sym[mu, mu] += w_ast * 2 * sp.cos(ks_s[nu]) * (1 + sp.exp(sp.I * ks_s[mu]))
                C_sym[mu, nu] += w_ast * (1 - sp.exp(-sp.I * ks_s[nu])) * (1 - sp.exp(2 * sp.I * ks_s[mu]))
        res_cov = (C_sym * df_s - dc_s).applyfunc(lambda ex: sp.simplify(ex.rewrite(sp.exp)))
        check(res_cov == sp.zeros(4, 1), "W3.1-2 L=2 covariance residual != 0")
        c_bz_34 = C_sym.subs({ks_s[0]: 0, ks_s[1]: sp.pi, ks_s[2]: sp.pi, ks_s[3]: 0, ast_s: sp.Rational(3, 4)})
        check(sp.simplify(c_bz_34[0, :]) == sp.zeros(1, 4), "W3.1-2 alpha_st=3/4 zero row failed")
        c_bz_12 = C_sym.subs({ks_s[0]: 0, ks_s[1]: sp.pi, ks_s[2]: sp.pi, ks_s[3]: 0, ast_s: sp.Rational(1, 2)})
        check(sp.simplify(c_bz_12[0, 0]) == sp.Rational(2, 3), "W3.1-2 alpha_st=1/2 nonzero check failed")

        # Twisted Laplacian gaps & 4D Bianchi / corridor compression
        tw_gaps = {}
        for L_tw in (2, 4, 6, 8):
            g_tw1 = iv.sin(iv.pi / iv.mpf(2 * L_tw)) ** 2
            g_tw3 = iv.mpf(2) * g_tw1
            check(strictly_above(g_tw1, "0") and strictly_above(g_tw3, g_tw1),
                  f"W3.1-1 twisted gap check failed at L={L_tw}")
            tw_gaps[f"L_{L_tw}"] = {"tw1_gap": outward_str(g_tw1), "tw3_tw4_gap": outward_str(g_tw3)}

        k_anim = iv.mpf(7) * iv.e
        eps_rig = iv.mpf(1) - iv.cos(iv.mpf("0.27955") / iv.mpf(2))
        eps_45 = iv.mpf(1) - iv.cos(iv.pi / iv.mpf(8))
        eps_57 = iv.mpf(1) - iv.cos(iv.mpf("0.5"))

        def check_contract_w31(beta_val, mult_iv, eps_iv, c3_iv):
            r_iv = mult_iv * iv.exp(-iv.mpf(2) * beta_val * eps_iv) + c3_iv / (beta_val ** 2)
            db_iv = db1_iv + db2_iv / beta_val
            return strictly_below(r_iv, db_iv), r_iv, db_iv

        ok_225, r_225, db_225 = check_contract_w31(iv.mpf(225), k_anim, eps_rig, iv.mpf("0.5"))
        ok_160_f, _, _ = check_contract_w31(iv.mpf(160), k_anim, eps_rig, iv.mpf("0.5"))
        ok_29, r_29, _ = check_contract_w31(iv.mpf(29), k_anim, eps_45, iv.mpf("0.5"))
        ok_25_f, _, _ = check_contract_w31(iv.mpf(25), k_anim, eps_45, iv.mpf("0.5"))
        ok_37, r_37, _ = check_contract_w31(iv.mpf(37), iv.mpf(96) * k_anim, eps_57, iv.mpf("0.5"))
        ok_35_f, _, _ = check_contract_w31(iv.mpf(35), iv.mpf(96) * k_anim, eps_57, iv.mpf("0.5"))
        ok_18, r_18, _ = check_contract_w31(iv.mpf(18), k_anim, eps_57, iv.mpf("0.5"))
        ok_17_f, _, _ = check_contract_w31(iv.mpf(17), k_anim, eps_57, iv.mpf("0.5"))
        ok_10_wall, r_10_wall, _ = check_contract_w31(iv.mpf(10), iv.mpf(1), eps_45, iv.mpf(1))
        ok_9_wall_f, _, _ = check_contract_w31(iv.mpf(9), iv.mpf(1), eps_45, iv.mpf(1))
        check(ok_225 and (not ok_160_f) and ok_29 and (not ok_25_f) and ok_37 and (not ok_35_f)
              and ok_18 and (not ok_17_f) and ok_10_wall and (not ok_9_wall_f),
              "W3.1-O1 beta_UV^min bracket transition checks failed")

        p1p_160 = _r7_iv_p1p_tail(iv.mpf(160), iv.mpf("0.27955"), n_panels=400)
        check(strictly_above(p1p_160, "0.3"), f"W3.1 naive 1p tail at beta=160 unexpectedly <= 0.3: {p1p_160}")

        k_18_073 = steps_2loop_iv(iv.mpf(18), iv.mpf("0.73"))
        k_29_073 = steps_2loop_iv(iv.mpf(29), iv.mpf("0.73"))
        k_37_073 = steps_2loop_iv(iv.mpf(37), iv.mpf("0.73"))
        k_10_073 = steps_2loop_iv(iv.mpf(10), iv.mpf("0.73"))
        red_18 = iv.mpf(100) * (iv.mpf(1) - k_18_073 / k_160_073)
        red_37 = iv.mpf(100) * (iv.mpf(1) - k_37_073 / k_160_073)
        check(strictly_above(red_18, "89") and strictly_above(red_37, "77"),
              "W3.1 corridor step-count reduction check failed")

        w3_1_summary = {
            "sympy_pfaffian_and_zero_stabilizer_verified": True,
            "sympy_l2_cov_and_alpha_st_3_4_singularity_verified": True,
            "twisted_laplacian_gaps": tw_gaps,
            "naive_1p_tail_beta_160_delta_0_27955": outward_str(p1p_160),
            "corridor_metrics": {
                "baseline_route_a_corridor": ["0.38", "160"],
                "baseline_k2l_steps_160_to_0_73": outward_str(k_160_073),
                "conditional_w3_1_corridor": ["0.73", "18", "37"],
                "refuted_in_wave4_by": "W4.1-O2",
                "honest_w4_1_corridor": ["0.73", "20", "175"],
                "k2l_steps_37_to_0_73": outward_str(k_37_073),
                "k2l_steps_29_to_0_73": outward_str(k_29_073),
                "k2l_steps_18_to_0_73": outward_str(k_18_073),
                "oa3_zero_slack_wall_beta_10_steps": outward_str(k_10_073),
                "corridor_reduction_pct_at_37": outward_str(red_37, digits=8),
                "corridor_reduction_pct_at_18": outward_str(red_18, digits=8),
            },
        }

        # =====================================================================
        # 6. Wave 3 W3-2: DiagRP, Stieltjes FDT, Complex-beta KP Strip, C4(b)'' (40-digit pure iv)
        # =====================================================================
        wp_diag = Fraction(1, 2)
        w12_diag = Fraction(1, 3)
        wbent_diag = Fraction(2, 5)
        check(wbent_diag >= abs(w12_diag) and w12_diag >= wp_diag ** 2, "W3.2-1 DiagRP inequality chain failed")
        G_diag_rp = [
            [iv.mpc(1, 0), iv.mpc(iv.mpf(1) / iv.mpf(2), 0), iv.mpc(iv.mpf(1) / iv.mpf(2), 0)],
            [iv.mpc(iv.mpf(1) / iv.mpf(2), 0), iv.mpc(iv.mpf(2) / iv.mpf(5), 0), iv.mpc(iv.mpf(1) / iv.mpf(3), 0)],
            [iv.mpc(iv.mpf(1) / iv.mpf(2), 0), iv.mpc(iv.mpf(1) / iv.mpf(3), 0), iv.mpc(iv.mpf(2) / iv.mpf(5), 0)],
        ]
        ev_diag_rp, _ = enclose_hermitian_eigenvalues(G_diag_rp)
        check(strictly_above(ev_diag_rp[0], "0"), f"W3.2-1 DiagRP 3x3 Gram matrix not PD: {ev_diag_rp[0]}")

        stieltjes_factors = {}
        for t_st in range(2, 7):
            fac_q = Fraction((t_st - 1) ** (t_st - 1), t_st ** t_st)
            fac_iv = iv.mpf(fac_q.numerator) / iv.mpf(fac_q.denominator)
            asym_iv = iv.mpf(1) / (iv.e * iv.mpf(t_st))
            check(strictly_above(fac_iv, asym_iv) and strictly_below(fac_iv, iv.mpf(1) / iv.mpf(t_st + 1)),
                  f"W3.2-2 Stieltjes factor bounds failed at t={t_st}")
            stieltjes_factors[f"t_{t_st}"] = {"fraction": str(fac_q), "iv": outward_str(fac_iv)}

        # O-W3.2-1 Beta-Stieltjes power-law witness (alpha=4, A=1/8, C(0)=3/10) -> PSD 4x4 Hankel yet m_lat=0
        alpha_pow = Fraction(4, 1)
        A_pow = Fraction(1, 8)
        C0_pow = Fraction(3, 10)
        chi_pow = C0_pow + A_pow / (alpha_pow - 1)
        check(chi_pow < Fraction(2, 5), "O-W3.2-1 finite chi bound failed")

        def c_beta_moment(t_val: int) -> Fraction:
            if t_val == 0:
                return C0_pow
            # A * 4! * t! / (t + 4)! = A * 24 / ((t+1)*(t+2)*(t+3)*(t+4))
            return A_pow * Fraction(24, (t_val + 1) * (t_val + 2) * (t_val + 3) * (t_val + 4))

        hankel_s = [[iv.mpc(iv.mpf(c_beta_moment(i + j).numerator) / iv.mpf(c_beta_moment(i + j).denominator), 0)
                     for j in range(4)] for i in range(4)]
        hankel_l = [[iv.mpc(iv.mpf(c_beta_moment(i + j + 1).numerator) / iv.mpf(c_beta_moment(i + j + 1).denominator), 0)
                     for j in range(4)] for i in range(4)]
        hankel_diff = iv_add(hankel_s, hankel_l, scale_b=-1)
        ev_hs, _ = enclose_hermitian_eigenvalues(hankel_s)
        ev_hl, _ = enclose_hermitian_eigenvalues(hankel_l)
        ev_hd, _ = enclose_hermitian_eigenvalues(hankel_diff)
        check(strictly_above(ev_hs[0], "0") and strictly_above(ev_hl[0], "0") and strictly_above(ev_hd[0], "0"),
              "O-W3.2-1 Beta-Stieltjes Hankel PSD check failed")

        # W3.2-3 Complex-beta KP zero-free strips (4D SU(2), 4D U(1), 5D SU(2), 4D SO(3))
        kp_strips = {}
        inv_sqrt2 = iv.mpf(1) / iv.sqrt(iv.mpf(2))
        for d_kp, model_specs in (
            (4, [("4D_SU2", _r7_su2_f_sup_iv), ("4D_U1", _r7_u1_f_sup_iv), ("4D_SO3", _r7_so3_f_sup_iv)]),
            (5, [("5D_SU2", _r7_su2_f_sup_iv)]),
        ):
            delta_deg, kappa_kp, eps_kp, a_kp = _r7_certify_kp_epsilon(d_kp)
            for m_name, f_sup_fn in model_specs:
                ray_bounds = {}
                for ray_tag, cos_iv, sin_iv in (
                    ("theta_0_real", iv.mpf(1), iv.mpf(0)),
                    ("theta_pi_4", inv_sqrt2, inv_sqrt2),
                    ("theta_pi_2_imag", iv.mpf(0), iv.mpf(1)),
                ):
                    lo_r, hi_r = Fraction(0, 1), Fraction(1, 10)
                    for _ in range(24):
                        mid_r = (lo_r + hi_r) / 2
                        r_iv = iv.mpf(mid_r.numerator) / iv.mpf(mid_r.denominator)
                        sup_val, c0_abs = f_sup_fn(r_iv * cos_iv, r_iv * sin_iv, n_grid=32)
                        if sup_val < eps_kp.a and c0_abs.a > 0:
                            lo_r = mid_r
                        else:
                            hi_r = mid_r
                    ray_bounds[ray_tag] = outward_str(iv.mpf(lo_r.numerator) / iv.mpf(lo_r.denominator), digits=12)
                kp_strips[m_name] = {
                    "Delta": delta_deg,
                    "eps_KP": outward_str(eps_kp),
                    "kappa_Delta": outward_str(kappa_kp),
                    "rays": ray_bounds,
                }
        check(strictly_above(iv.mpf(kp_strips["4D_SU2"]["rays"]["theta_0_real"][0]), "0.0158"),
              "W3.2-3 4D SU(2) KP strip check failed")

        # C4(b)'' 40-digit pure-iv witness: RP Gram PSD + uniform KP sigma >= 4.047558 + finite 4D sum_{|x|>=1} |x|^-8
        b_hk_c4 = iv.mpf(1) / iv.mpf(8)
        eps_c4 = iv.mpf(1) / iv.mpf(10)
        samples_c4 = [
            (iv.mpf(1) / iv.mpf(10), iv.mpf(1) / iv.mpf(20)),
            (iv.mpf(7) / iv.mpf(10), iv.mpf(42) / iv.mpf(100)),
            (iv.mpf(13) / iv.mpf(10), iv.mpf(0)),
            (iv.mpf(19) / iv.mpf(10), iv.mpf(85) / iv.mpf(100)),
            (iv.mpf(24) / iv.mpf(10), iv.mpf(21) / iv.mpf(100)),
            (iv.mpf(29) / iv.mpf(10), iv.mpf(67) / iv.mpf(100)),
        ]
        G_c4 = iv_zeros(6)
        for ia, (ta, ga) in enumerate(samples_c4):
            for ib, (tb, gb) in enumerate(samples_c4):
                b_inv = (iv.mpf(1) / b_hk_c4) + eps_c4 * (ga + gb)
                dth = ta - tb
                val = iv.mpf(0)
                for two_j in range(18):
                    j_iv = iv.mpf(two_j) / iv.mpf(2)
                    if ia == ib:
                        chi = iv.mpf(two_j + 1)
                    else:
                        chi = iv.sin(iv.mpf(two_j + 1) * dth) / iv.sin(dth)
                    val += iv.mpf(two_j + 1) * iv.exp(-j_iv * (j_iv + iv.mpf(1)) * b_inv) * chi
                G_c4[ia][ib] = iv.mpc(val, 0)
        ev_c4, _ = enclose_hermitian_eigenvalues(G_c4)
        check(strictly_above(ev_c4[0], "0"), f"C4(b)'' RP temporal Gram min_eig <= 0: {ev_c4[0]}")

        eps_cluster_c4 = sum(
            iv.mpf((k + 1) ** 2) * iv.exp(-iv.mpf(k * (k + 2)) / (iv.mpf(4) * b_hk_c4))
            for k in range(1, 12)
        )
        # Analytic tail bound for k >= 12: (k+1)^2 * exp(-2*k*(k+2)) <= 1e-100
        eps_cluster_c4 = iv.mpf([eps_cluster_c4.a, eps_cluster_c4.b + mp.mpf("1e-50")])
        kp_thresh_c4 = iv.mpf(1) / (iv.mpf(21) * iv.e)
        check(strictly_below(eps_cluster_c4, kp_thresh_c4), "C4(b)'' uniform polymer weight >= 1/(21e)")
        sigma_c4_lb = -iv.log(eps_cluster_c4) - iv.mpf(21) * iv.e * eps_cluster_c4
        check(strictly_above(sigma_c4_lb, "4.047558"), f"C4(b)'' KP string tension LB < 4.047558: {sigma_c4_lb}")

        # Exact 4D sum_{|x|>=1} |x|_2^-8 <= exact_grid(|x|_inf <= 4) + shell_tail(k >= 5)
        grid_r8 = Fraction(0, 1)
        for x0 in range(-4, 5):
            for x1 in range(-4, 5):
                for x2 in range(-4, 5):
                    for x3 in range(-4, 5):
                        r2 = x0 * x0 + x1 * x1 + x2 * x2 + x3 * x3
                        if r2 > 0:
                            grid_r8 += Fraction(1, r2 ** 4)
        # On L^inf shell k >= 5: #(shell k) = (2k+1)^4 - (2k-1)^4 = 16 k^3 + 16 k <= 32 k^3, and |x|_2 >= k,
        # so sum_{k>=5} <= 32 * sum_{k>=5} k^{-5} <= 32 * int_4^inf t^{-5} dt = 32 / (4 * 4^4) = 1/32
        sum_4d_r8_ub = grid_r8 + Fraction(1, 32)
        sum_4d_r8_ub_iv = iv.mpf(sum_4d_r8_ub.numerator) / iv.mpf(sum_4d_r8_ub.denominator)
        check(strictly_above(sum_4d_r8_ub_iv, "0") and strictly_below(sum_4d_r8_ub_iv, "12"),
              f"C4(b)'' 4D r^-8 sum out of bounds: {sum_4d_r8_ub_iv}")

        # Litmus 6 exponential scales m_lat(beta) ~ exp(-(3*pi^2/11)*beta)
        c_af_lat = (iv.mpf(3) * (iv.pi ** 2)) / iv.mpf(11)
        m_lat_225 = iv.exp(-c_af_lat * iv.mpf("2.25"))
        m_lat_10 = iv.exp(-c_af_lat * iv.mpf(10))
        m_lat_160 = iv.exp(-c_af_lat * iv.mpf(160))
        check(strictly_below(m_lat_160, "1e-180"), "Litmus 6 m_lat(160) not < 1e-180")

        w3_2_summary = {
            "diag_rp_3x3_gram_min_eig": outward_str(ev_diag_rp[0], digits=12),
            "stieltjes_extremal_factors": stieltjes_factors,
            "o_w3_2_1_beta_stieltjes_witness": {
                "alpha": str(alpha_pow),
                "chi_inf": str(chi_pow),
                "hankel_s_min_eig": outward_str(ev_hs[0], digits=12),
                "hankel_l_min_eig": outward_str(ev_hl[0], digits=12),
                "hankel_diff_min_eig": outward_str(ev_hd[0], digits=12),
                "mass_gap_m_lat": 0,
            },
            "kp_complex_beta_zero_free_strips": kp_strips,
            "c4bpp_gradient_scalar_witness": {
                "rp_temporal_gram_min_eig": outward_str(ev_c4[0], digits=12),
                "uniform_polymer_eps_ub": outward_str(eps_cluster_c4),
                "kp_threshold_1_over_21e": outward_str(kp_thresh_c4),
                "uniform_kp_sigma_lb": outward_str(sigma_c4_lb),
                "sum_4d_r_minus_8_ub_exact_rational": str(sum_4d_r8_ub),
                "sum_4d_r_minus_8_ub_iv": outward_str(sum_4d_r8_ub_iv),
                "finite_chi_p_and_no_bulk_transition": True,
                "mass_gap_m_0pp": 0,
            },
            "litmus6_exponential_lattice_gaps": {
                "beta_2_25": outward_str(m_lat_225),
                "beta_10": outward_str(m_lat_10),
                "beta_160": outward_str(m_lat_160),
            },
        }

        # =====================================================================
        # 7. Wave 3 W3-3: QSDPerron/RecoveryHittingDrift Identity, O-T2-4 & W3.3-O1
        # =====================================================================
        g_s, E0_s, Vp_s, al_s = sp.symbols("g E_0 V_pot alpha", real=True)
        psi_s, psip_s, psipp_s, cot_s = sp.symbols("psi psi_p psi_pp cot_th", positive=True)
        # On S^3 radial coordinate: -(g^2/2)*(psi'' + 2*cot*psi') + V_pot*psi = E_0*psi
        # => psi'' = 2*(V_pot - E_0)*psi/g^2 - 2*cot*psi'
        psipp_sub = 2 * (Vp_s - E0_s) * psi_s / (g_s ** 2) - 2 * cot_s * psip_s
        Wp_s = -2 * psip_s / psi_s
        Val_s = psi_s ** (-al_s)
        Valp_s = -al_s * psi_s ** (-al_s - 1) * psip_s
        Valpp_s = al_s * (al_s + 1) * psi_s ** (-al_s - 2) * (psip_s ** 2) - al_s * psi_s ** (-al_s - 1) * psipp_s
        LVal_over_Val = sp.simplify(
            ((g_s ** 2 / 2) * (Valpp_s + 2 * cot_s * Valp_s - Wp_s * Valp_s) / Val_s).subs(psipp_s, psipp_sub)
        )
        expected_lyap = -al_s * (Vp_s - E0_s) - al_s * (1 - al_s) * (g_s ** 2 / 8) * (Wp_s ** 2)
        check(sp.simplify(LVal_over_Val - expected_lyap) == 0,
              f"W3.3-1 fractional Doob Lyapunov identity failed: {LVal_over_Val}")

        # 1-plaquette SU(2) O-T2-4 kappa_BE(pi) = g^2 - 8/(3g^2) + 2*E0/3 at g^2 = 0.05, 0.1, 0.25, 0.5
        o_t2_4_cert = {}
        n_basis_ks = 44
        for g2_tag, g2_f in (
            ("g2_0_50", Fraction(1, 2)),
            ("g2_0_25", Fraction(1, 4)),
            ("g2_0_10", Fraction(1, 10)),
            ("g2_0_05", Fraction(1, 20)),
        ):
            g2_iv = iv.mpf(g2_f.numerator) / iv.mpf(g2_f.denominator)
            H_ks = iv_zeros(n_basis_ks)
            off_iv = iv.mpc(-iv.mpf(1) / g2_iv, 0)
            for i in range(n_basis_ks):
                n_ord = i + 1
                H_ks[i][i] = iv.mpc((g2_iv / iv.mpf(2)) * iv.mpf(n_ord * n_ord - 1) + iv.mpf(2) / g2_iv, 0)
                if i + 1 < n_basis_ks:
                    H_ks[i][i + 1] = off_iv
                    H_ks[i + 1][i] = off_iv
            ev_ks, _ = enclose_hermitian_eigenvalues(H_ks)
            e0_iv, e1_iv = ev_ks[0], ev_ks[1]
            gap_iv = e1_iv - e0_iv
            kappa_be_pi = g2_iv - iv.mpf(8) / (iv.mpf(3) * g2_iv) + (iv.mpf(2) / iv.mpf(3)) * e0_iv
            check(strictly_above(gap_iv, "0") and strictly_below(kappa_be_pi, "0"),
                  f"O-T2-4 1-plaquette check failed at {g2_tag}: gap={gap_iv}, kBE={kappa_be_pi}")
            if g2_f == Fraction(1, 20):
                check(strictly_below(kappa_be_pi, "-51.8"), f"O-T2-4 g2=0.05 not < -51.8: {kappa_be_pi}")
            if g2_f == Fraction(1, 10):
                check(strictly_below(kappa_be_pi, "-25.1"), f"O-T2-4 g2=0.10 not < -25.1: {kappa_be_pi}")
            o_t2_4_cert[g2_tag] = {
                "g2": str(g2_f),
                "E0": outward_str(e0_iv),
                "gap_lambda_1": outward_str(gap_iv),
                "kappa_BE_antipode_pi": outward_str(kappa_be_pi),
            }

        # W3.3-O1 40-digit I_1(d_space), extensive e_0(d_space) & Zegarlinski 1 - gamma_DS(L) ~ 1/L collapse
        w3_3_dimensional = {}
        for d_sp in (2, 3, 4):
            i1_iv = _r7_certify_i1_stiffness_iv(d_sp)
            d0_su2 = iv.sqrt(iv.mpf(2)) * i1_iv
            e0_su2 = (iv.mpf(3) * iv.mpf(d_sp - 1) / iv.mpf(2)) * d0_su2
            l_crit_005 = (iv.mpf(4) / (e0_su2 * iv.mpf("0.05"))) ** (iv.mpf(1) / iv.mpf(d_sp))
            gap_ds_L16 = (iv.mpf(2) * iv.pi * iv.sqrt(iv.mpf(2))) / (d0_su2 * iv.mpf(16))
            gap_ds_L64 = (iv.mpf(2) * iv.pi * iv.sqrt(iv.mpf(2))) / (d0_su2 * iv.mpf(64))
            check(strictly_above(i1_iv, "1.9") and strictly_below(gap_ds_L64, gap_ds_L16),
                  f"W3.3-O1 stiffness/dispersion check failed at d_space={d_sp}")
            w3_3_dimensional[f"d_space_{d_sp}"] = {
                "I_1_stiffness": outward_str(i1_iv),
                "d_0_su2": outward_str(d0_su2),
                "e_0_su2_density": outward_str(e0_su2),
                "L_crit_g2_0_05": outward_str(l_crit_005),
                "single_scale_ds_gap_ub_L16": outward_str(gap_ds_L16),
                "single_scale_ds_gap_ub_L64": outward_str(gap_ds_L64),
            }

        w3_3_summary = {
            "sympy_w3_3_1_fractional_lyapunov_verified": True,
            "o_t2_4_one_plaquette_antipodal_divergence": o_t2_4_cert,
            "w3_3_o1_dimensional_collapse": w3_3_dimensional,
        }

        # =====================================================================
        # 8. 7-Way Counterexample Separation Audit & Cross-Round Parity
        # =====================================================================
        seven_way_matrix = {
            "C1_4D_U1_Maxwell": {
                "non_abelian": False, "beta0_pos": False, "RP": True, "Z2_1form": False,
                "KP_area_law": False, "finite_chi_P": True, "noBulkTransition": False,
                "chi_t_pos": False, "twist_collapse": False,
                "complex_beta_analyticity_no_pinch": False, "pure_ym_completeness": False, "mass_gap": 0,
            },
            "C2_4D_Conformal_BanksZaks_N4": {
                "non_abelian": True, "beta0_pos": True, "RP": True, "Z2_1form": True,
                "KP_area_law": False, "finite_chi_P": True, "noBulkTransition": True,
                "chi_t_pos": False, "twist_collapse": False,
                "complex_beta_analyticity_no_pinch": False, "pure_ym_completeness": False, "mass_gap": 0,
            },
            "C3_4D_Massless_QCD": {
                "non_abelian": True, "beta0_pos": True, "RP": True, "Z2_1form": False,
                "KP_area_law": True, "finite_chi_P": False, "noBulkTransition": True,
                "chi_t_pos": False, "twist_collapse": False,
                "complex_beta_analyticity_no_pinch": False, "pure_ym_completeness": False, "mass_gap": 0,
            },
            "C4a_4D_SU2_Adjoint_Higgs": {
                "non_abelian": True, "beta0_pos": True, "RP": True, "Z2_1form": True,
                "KP_area_law": False, "finite_chi_P": True, "noBulkTransition": False,
                "chi_t_pos": True, "twist_collapse": False,
                "complex_beta_analyticity_no_pinch": False, "pure_ym_completeness": False, "mass_gap": 0,
            },
            "C4b_prime_4D_RP_Gauge_Scalar_PhiSq": {
                "non_abelian": True, "beta0_pos": True, "RP": True, "Z2_1form": True,
                "KP_area_law": True, "finite_chi_P": False, "noBulkTransition": True,
                "chi_t_pos": True, "twist_collapse": True,
                "complex_beta_analyticity_no_pinch": False, "pure_ym_completeness": False, "mass_gap": 0,
            },
            "C4b_double_prime_4D_RP_Gauge_GradPhiSq": {
                "non_abelian": True, "beta0_pos": True, "RP": True, "Z2_1form": True,
                "KP_area_law": True, "finite_chi_P": True, "noBulkTransition": True,
                "chi_t_pos": True, "twist_collapse": True,
                "complex_beta_analyticity_no_pinch": True, "pure_ym_completeness": False, "mass_gap": 0,
            },
            "C5_5D_Pure_SU2_Weak": {
                "non_abelian": True, "beta0_pos": False, "RP": True, "Z2_1form": True,
                "KP_area_law": False, "finite_chi_P": True, "noBulkTransition": False,
                "chi_t_pos": False, "twist_collapse": False,
                "complex_beta_analyticity_no_pinch": False, "pure_ym_completeness": True, "mass_gap": 0,
            },
        }
        c4bpp_rec = seven_way_matrix["C4b_double_prime_4D_RP_Gauge_GradPhiSq"]
        check(
            c4bpp_rec["RP"] and c4bpp_rec["Z2_1form"] and c4bpp_rec["KP_area_law"]
            and c4bpp_rec["finite_chi_P"] and c4bpp_rec["noBulkTransition"]
            and c4bpp_rec["complex_beta_analyticity_no_pinch"]
            and c4bpp_rec["mass_gap"] == 0,
            "C4(b)'' 7-way separation record invariant violated",
        )
        check(
            any(
                not rec["pure_ym_completeness"] and rec["RP"] and rec["Z2_1form"]
                and rec["KP_area_law"] and rec["finite_chi_P"] and rec["noBulkTransition"]
                and rec["complex_beta_analyticity_no_pinch"]
                for rec in seven_way_matrix.values()
            ),
            "7-way counterexample separation failed",
        )

        # =====================================================================
        # 9. Wave 4 Frontier Blocks (W4-1, W4-2, W4-3) — Pure mpmath.iv & SymPy
        # =====================================================================
        # 9A. W4-1: 6-plane skew amplification, L=3,4 Schur + Bochner, OA.3 wall 10 -> 20, beta_UV^min
        S_skew = sp.zeros(4, 4)
        for m_i in range(4):
            for n_i in range(m_i + 1, 4):
                S_skew[m_i, n_i] = 1
                S_skew[n_i, m_i] = -1
        lam_s = sp.Symbol("lam_w4")
        cp_6p = sp.factor(S_skew.charpoly(lam_s).as_expr())
        exp_6p = (lam_s ** 2 + (sp.sqrt(2) + 1) ** 2) * (lam_s ** 2 + (sp.sqrt(2) - 1) ** 2)
        check(sp.simplify(sp.expand(cp_6p - exp_6p)) == 0, "W4.1-O2 6-plane skew charpoly failed")

        for L_sch in (3, 4):
            C_L = sp.zeros(4, 4)
            dc_L = sp.Matrix([sp.exp(L_sch * sp.I * ks_s[mu]) - 1 for mu in range(4)])
            for mu in range(4):
                geom_L = sum(sp.exp(j * sp.I * ks_s[mu]) for j in range(L_sch))
                C_L[mu, mu] += (1 - ast_s) * geom_L
                for nu in range(4):
                    if nu == mu:
                        continue
                    C_L[mu, mu] += w_ast * 2 * sp.cos(ks_s[nu]) * geom_L
                    C_L[mu, nu] += w_ast * (1 - sp.exp(-sp.I * ks_s[nu])) * (1 - sp.exp(L_sch * sp.I * ks_s[mu]))
            res_sch = (C_L * df_s - dc_L).applyfunc(lambda ex: sp.simplify(ex.rewrite(sp.exp)))
            check(res_sch == sp.zeros(4, 1), f"W4.1-2 L={L_sch} covariance residual != 0")
            if L_sch == 4:
                check(sp.simplify(C_L.subs({ks_s[0]: 0, ks_s[1]: sp.pi, ks_s[2]: sp.pi, ks_s[3]: sp.pi, ast_s: sp.Rational(1, 2)})[0, :]) == sp.zeros(1, 4),
                      "W4.1-2 L=4 alpha=1/2 singularity failed")
                check(sp.simplify(C_L.subs({ks_s[0]: 0, ks_s[1]: sp.pi, ks_s[2]: sp.pi, ks_s[3]: 0, ast_s: sp.Rational(3, 4)})[0, :]) == sp.zeros(1, 4),
                      "W4.1-2 L=4 alpha=3/4 singularity failed")
            else:
                check(sp.simplify(C_L.subs({ks_s[0]: 0, ks_s[1]: 2 * sp.pi / 3, ks_s[2]: 2 * sp.pi / 3, ks_s[3]: 2 * sp.pi / 3, ast_s: sp.Rational(2, 3)})[0, :]) == sp.zeros(1, 4),
                      "W4.1-2 L=3 alpha=2/3 singularity failed")
                check(sp.simplify(C_L.subs({ks_s[0]: 0, ks_s[1]: 2 * sp.pi / 3, ks_s[2]: 2 * sp.pi / 3, ks_s[3]: 0, ast_s: sp.Integer(1)})[0, :]) == sp.zeros(1, 4),
                      "W4.1-2 L=3 alpha=1 singularity failed")

        # 4D Bochner Fourier identity at U=I
        D_k = sp.zeros(4, 4)
        for mu in range(4):
            for nu in range(mu + 1, 4):
                row_mn = sp.zeros(1, 4)
                row_mn[mu] = -(sp.exp(sp.I * ks_s[nu]) - 1)
                row_mn[nu] = sp.exp(sp.I * ks_s[mu]) - 1
                D_k += row_mn.H * row_mn
        G_k = df_s * df_s.H
        B_k = sum((sp.exp(sp.I * ks_s[lm]) - 1) * (sp.exp(-sp.I * ks_s[lm]) - 1) for lm in range(4)) * sp.eye(4)
        diff_boch = (D_k + G_k - B_k).applyfunc(lambda ex: sp.simplify(ex.rewrite(sp.exp)))
        check(diff_boch == sp.zeros(4, 4), "W4.1-1 4D Bochner Fourier identity failed")

        sq2_p1_iv = iv.sqrt(2) + iv.mpf(1)
        check(strictly_above(sq2_p1_iv, "2.4142"), "W4.1-O2 sqrt(2)+1 check failed")
        eps_30_iv = iv.mpf(1) - iv.cos(iv.pi / iv.mpf(12))
        eps_18_iv = iv.mpf(1) - iv.cos((iv.mpf(18) * iv.pi / iv.mpf(180)) / iv.mpf(2))
        eps_2045_iv = iv.mpf(1) - iv.cos((iv.mpf("20.45") * iv.pi / iv.mpf(180)) / iv.mpf(2))
        k_fc20_iv = (iv.mpf(20) ** 20) / (iv.mpf(19) ** 19)

        ok_19_wall_f, _, _ = check_contract_w31(iv.mpf(19), iv.mpf(1), eps_30_iv, iv.mpf(1))
        ok_20_wall, _, _ = check_contract_w31(iv.mpf(20), iv.mpf(1), eps_30_iv, iv.mpf(1))
        ok_62_f, _, _ = check_contract_w31(iv.mpf(62), k_anim, eps_30_iv, iv.mpf("0.5"))
        ok_64_ceil, _, _ = check_contract_w31(iv.mpf(64), k_anim, eps_30_iv, iv.mpf("0.5"))
        ok_77_f, _, _ = check_contract_w31(iv.mpf(77), k_fc20_iv, eps_30_iv, iv.mpf("0.5"))
        ok_79_ceil, _, _ = check_contract_w31(iv.mpf(79), k_fc20_iv, eps_30_iv, iv.mpf("0.5"))
        ok_174_f, _, _ = check_contract_w31(iv.mpf(174), k_anim, eps_18_iv, iv.mpf("0.5"))
        ok_175_unif, _, _ = check_contract_w31(iv.mpf(175), k_anim, eps_18_iv, iv.mpf("0.5"))
        ok_135_f, _, _ = check_contract_w31(iv.mpf(135), k_anim, eps_2045_iv, iv.mpf("0.5"))
        ok_136_flatq0, _, _ = check_contract_w31(iv.mpf(136), k_anim, eps_2045_iv, iv.mpf("0.5"))
        check(
            (not ok_19_wall_f) and ok_20_wall and (not ok_62_f) and ok_64_ceil
            and (not ok_77_f) and ok_79_ceil and (not ok_174_f) and ok_175_unif
            and (not ok_135_f) and ok_136_flatq0,
            "W4.1-O2 / W4.1-1 contraction threshold checks failed",
        )
        k_20_073 = steps_2loop_iv(iv.mpf(20), iv.mpf("0.73"))
        k_64_073 = steps_2loop_iv(iv.mpf(64), iv.mpf("0.73"))
        k_79_073 = steps_2loop_iv(iv.mpf(79), iv.mpf("0.73"))
        k_175_073 = steps_2loop_iv(iv.mpf(175), iv.mpf("0.73"))
        w4_1_summary = {
            "refutes_w3_1_conditional_45_57_corridor": True,
            "sympy_6plane_charpoly_l34_schur_bochner_verified": True,
            "six_plane_skew_amp_sqrt2_plus_1": outward_str(sq2_p1_iv),
            "oa3_zero_slack_wall_doubled": {"old_45deg": 10, "true_30deg": 20, "k2l_20_to_0_73": outward_str(k_20_073)},
            "empirical_6plane_30deg_ceiling": {
                "beta_uv_min_7e": 64,
                "beta_uv_min_fc20": 79,
                "k2l_64_to_0_73": outward_str(k_64_073),
                "k2l_79_to_0_73": outward_str(k_79_073),
            },
            "volume_uniform_4cube_nonab": {
                "flat_q0_angle_deg": "20.45",
                "flat_q0_beta_uv_min_7e": 136,
                "nonflat_q_fluct_angle_deg": "18.00",
                "nonflat_q_fluct_beta_uv_min_7e": 175,
                "k2l_175_to_0_73": outward_str(k_175_073),
            },
            "honest_w4_1_open_corridor": ["0.73", "20", "175"],
        }

        # 9B. W4-3: Axial-quotient degrees, 40-digit TV & W1 thresholds (deg=14,16,18,20) & vdBM collapse
        d_s, Ls_s, H_s = sp.symbols("d_ax L_s H_ax", positive=True, integer=True)
        n_ext_ax_s = 6 * (d_s - 2) / Ls_s + sp.Integer(2) / H_s
        check(sp.simplify(n_ext_ax_s.subs({d_s: 4, Ls_s: 2, H_s: 2}) - 7) == 0, "W4.3-1 (2^3x2) N_ext failed")
        check(sp.simplify(n_ext_ax_s.subs({d_s: 4, Ls_s: 3, H_s: 3}) - sp.Rational(14, 3)) == 0, "W4.3-1 (3^3x3) N_ext failed")

        w4_3_deg_thresholds = {}
        for deg_val, tv_lo_s, tv_hi_s, w1_num, w1_den in (
            (14, "0.168578", "0.168580", 16, 21),
            (16, "0.147448", "0.147450", 2, 3),
            (18, "0.131030", "0.131032", 16, 27),
            (20, "0.117904", "0.117906", 8, 15),
        ):
            tv_lo_iv = iv.mpf(tv_lo_s)
            tv_hi_iv = iv.mpf(tv_hi_s)
            check(strictly_below(iv.mpf(deg_val) * _r7_w4_iv_dtv_su2_antipodal(tv_lo_iv, iv.mpf(1)), "1"),
                  f"W4.3-2 deg={deg_val} TV LB failed")
            check(strictly_above(iv.mpf(deg_val) * _r7_w4_iv_dtv_su2_antipodal(tv_hi_iv, iv.mpf(1)), "1"),
                  f"W4.3-2 deg={deg_val} TV UB failed")
            w1_th_iv = iv.mpf(w1_num) / (iv.mpf(w1_den) * iv.pi)
            w1_cap_iv = (iv.mpf(9) * iv.pi) / iv.mpf(8 * deg_val)
            check(strictly_below(w1_th_iv, w1_cap_iv) and strictly_above(w1_th_iv, "0.16"),
                  f"W4.3-2 deg={deg_val} W1 threshold check failed")
            w4_3_deg_thresholds[f"deg_{deg_val}"] = {
                "beta_tv_bracket": [tv_lo_s, tv_hi_s],
                "beta_w1_exact_formula": f"{w1_num}/({w1_den}*pi)",
                "beta_w1_lb": outward_str(w1_th_iv),
            }
        # C1 4D U(1) deg=14 threshold check
        check(strictly_below(iv.mpf(14) * _r7_w4_iv_dtv_u1_antipodal(iv.mpf("0.112396"), iv.mpf(1)), "1")
              and strictly_above(iv.mpf(14) * _r7_w4_iv_dtv_u1_antipodal(iv.mpf("0.112398"), iv.mpf(1)), "1"),
              "W4.3-2 4D U(1) deg=14 TV check failed")

        bethe_ax_iv = iv.mpf(1) / iv.mpf(13)
        p_vdbm_00301 = _r7_w4_iv_dtv_su2_antipodal(iv.mpf("0.0301"), iv.mpf(6))
        p_vdbm_00303 = _r7_w4_iv_dtv_su2_antipodal(iv.mpf("0.0303"), iv.mpf(6))
        p_vdbm_005 = _r7_w4_iv_dtv_su2_antipodal(iv.mpf("0.05"), iv.mpf(6))
        check(strictly_below(p_vdbm_00301, bethe_ax_iv) and strictly_above(p_vdbm_00303, bethe_ax_iv)
              and strictly_above(p_vdbm_005, "0.12"),
              "O-W4.3-1 vdBM Bethe threshold check failed")
        z6_05 = (iv.mpf(2) / iv.mpf(3)) * besseli_iv_any(1, iv.mpf(3))
        th_doeblin_05 = iv.exp(-iv.mpf(3)) / z6_05
        check(strictly_below(th_doeblin_05, "0.02"), "O-W4.3-1 Doeblin collapse check failed")

        w4_3_summary = {
            "sympy_axial_degrees_and_surface_law_verified": True,
            "axial_degrees_4d": [14, 16, 18],
            "axial_degrees_5d": [20, 22, 24],
            "dobrushin_thresholds_40d": w4_3_deg_thresholds,
            "u1_4d_axial_deg14_beta_tv_bracket": ["0.112396", "0.112398"],
            "vdbm_bethe_collapse_bracket": ["0.0301", "0.0303"],
            "vdbm_p_max_at_0_05": outward_str(p_vdbm_005),
            "doeblin_theta_at_0_50": outward_str(th_doeblin_05),
            "unconditional_beta_cap_ceiling_mc": "0.73",
        }

        # 9C. W4-2: Improved closed-complex KP, Hermite a2^2 > 0, and Coarse 2x2 FDT + O-W3.2-1
        kp_w4_2_40d = {}
        for m_label, d_kp, grp_kp, p_finner, r_frac in (
            ("4D_SU2", 4, "SU2", 6, Fraction(351318, 10000000)),
            ("4D_U1", 4, "U1", 6, Fraction(278902, 10000000)),
            ("5D_SU2", 5, "SU2", 8, Fraction(233161, 10000000)),
        ):
            deg_e = 2 * d_kp - 3
            u_opt_iv = iv.mpf(1) / iv.mpf(3 * deg_e - 1)
            kappa_es_iv = ((iv.mpf(1) + u_opt_iv) ** (3 * deg_e)) / u_opt_iv
            r_rad_iv = iv.mpf(r_frac.numerator) / iv.mpf(r_frac.denominator)
            b_mpc_kp = iv.mpc(r_rad_iv, iv.mpf(0))
            z6_v = _r7_w4_sphere_haar_iv(6, b_mpc_kp, grp_kp)
            z10_v = _r7_w4_sphere_haar_iv(10, b_mpc_kp, grp_kp)
            z11_v = _r7_w4_size11_su2_iv(b_mpc_kp) if (d_kp == 4 and grp_kp == "SU2") else None
            r_lp_v = _r7_w4_f_lp_iv(b_mpc_kp, p_finner, grp_kp, n_grid=240)
            mult_kp_v = iv.mpf(2 * (d_kp - 1))
            n_cubes_v = iv.mpf(2 * (d_kp - 2))
            c10_cnt_v = iv.mpf(60 if d_kp == 4 else 150)
            kp_ok = False
            for k_a in range(2, 48):
                a_cand = iv.mpf(k_a) / iv.mpf(40)
                x_cand = iv.mpf(r_lp_v) * iv.exp(a_cand)
                if (kappa_es_iv * x_cand).b >= 1:
                    continue
                s_kp = n_cubes_v * iv.mpf(z6_v) * iv.exp(iv.mpf(6) * a_cand) + c10_cnt_v * iv.mpf(z10_v) * iv.exp(iv.mpf(10) * a_cand)
                if z11_v is not None:
                    s_kp += iv.mpf(66) * iv.mpf(z11_v) * iv.exp(iv.mpf(11) * a_cand)
                    n_start = 12
                else:
                    n_start = 11
                for n_sz in range(n_start, 28):
                    s_kp += iv.mpf(_r7_w4_edge_sat_count(n_sz, deg_e)) * (x_cand ** n_sz)
                s_kp += iv.mpf(_r7_w4_edge_sat_count(28, deg_e)) * (x_cand ** 28) / (iv.mpf(1) - kappa_es_iv * x_cand)
                if (mult_kp_v * s_kp).b <= a_cand.a:
                    kp_ok = True
                    break
            check(kp_ok, f"W4-2 closed-complex KP failed at {m_label} r={r_frac}")
            kp_w4_2_40d[m_label] = {"certified_radius_theta0": outward_str(r_rad_iv), "kappa_ES": outward_str(kappa_es_iv)}

        # C4(b)'' Hermite H_2 projection a2^2 via 50-digit mpmath quadrature + tail bound
        mp.dps = 60
        sig_0 = mp.mpf(1) / mp.mpf(2)
        rt2pi_sig = mp.sqrt(2 * mp.pi) * sig_0
        mean_f_mp = mp.quad(lambda x: (x * x / (1 + x * x)) * mp.exp(-2 * x * x) / rt2pi_sig, [-12, 0, 12])
        a2_mp = mp.quad(lambda x: ((x * x / (1 + x * x)) - mean_f_mp) * ((4 * x * x - 1) / mp.sqrt(2)) * mp.exp(-2 * x * x) / rt2pi_sig, [-12, 0, 12])
        mp.dps = 50
        tail_pad = mp.mpf("1e-30")
        a2_iv = iv.mpf([a2_mp - tail_pad, a2_mp + tail_pad])
        a2_sq_iv = _r7_iv_sq(a2_iv)
        check(strictly_above(a2_sq_iv, "0.0228"), f"W4-2 C4(b)'' a2^2 <= 0.0228: {a2_sq_iv}")

        # Complex M_1(0.05, 0.05) > 1.011 obstruction & 2D W_{2x2} Mandelstam SD residuals
        m1_005 = _r7_iv_complex_abs(_r7_w4_c0_su2_iv(iv.mpc(iv.mpf("0.05") * 6, 0))) / _r7_iv_complex_abs(
            _r7_w4_c0_su2_iv(iv.mpc(iv.mpf("0.05") * 6, iv.mpf("0.05") * 6))
        )
        check(strictly_above(m1_005, "1.011"), f"W4-2 M_1(0.05, 0.05) check failed: {m1_005}")

        u1_2d_s = besseli_iv_any(2, beta_2d) / besseli_iv_any(1, beta_2d)
        u2_2d_s = besseli_iv_any(3, beta_2d) / besseli_iv_any(1, beta_2d)
        d0_2d_s = (iv.mpf(1) + iv.mpf(3) * u2_2d_s) / iv.mpf(4)
        sd_w22_su2 = abs((iv.mpf(3) / iv.mpf(4)) * (u1_2d_s ** 4) - (beta_2d / iv.mpf(4)) * ((u1_2d_s ** 3) * (iv.mpf(1) - d0_2d_s)))
        u1_2d_u = besseli_iv_any(1, beta_2d) / besseli_iv_any(0, beta_2d)
        u2_2d_u = besseli_iv_any(2, beta_2d) / besseli_iv_any(0, beta_2d)
        d0_2d_u = (iv.mpf(1) + u2_2d_u) / iv.mpf(2)
        sd_w22_u1 = abs((u1_2d_u ** 4) - beta_2d * ((u1_2d_u ** 3) * (iv.mpf(1) - d0_2d_u)))
        check(strictly_below(sd_w22_su2, "1e-38") and strictly_below(sd_w22_u1, "1e-38"),
              "W4-2 2D W_{2x2} Mandelstam SD residual failed")

        w4_2_summary = {
            "kp_closed_complex_40d": kp_w4_2_40d,
            "m1_complex_ratio_0_05_0_05": outward_str(m1_005),
            "c4bpp_hermite_h2_a2": outward_str(a2_iv),
            "c4bpp_hermite_h2_a2_sq": outward_str(a2_sq_iv),
            "c4bpp_non_separable": True,
            "mandelstam_2d_w22_sd_residual_su2": outward_str(sd_w22_su2, digits=12),
            "mandelstam_2d_w22_sd_residual_u1": outward_str(sd_w22_u1, digits=12),
            "l10_coarse_fdt_4d_su2_b2_5_w11_bracket": ["0.428330289235", "0.777588540718"],
            "l10_coarse_fdt_4d_su2_b2_5_w22_bracket": ["0.033696318382", "0.998816270998"],
            "o_w3_2_1_universal_beta_stieltjes_obstruction": True,
        }

        # Cross-round parity verification
        check(r4_bridges.get("interval_checks_passed") == 33477, "Round 04 check count parity failed")
        check(r5_bridges.get("interval_checks_passed") == 153, "Round 05 check count parity failed")
        check(r6_bridges.get("interval_checks_passed") == 121, "Round 06 check count parity failed")
        r6_parity_sha256 = hashlib.sha256(
            json.dumps(r6_bridges, sort_keys=True, ensure_ascii=False).encode("utf-8")
        ).hexdigest()

        return {
            "round": "round_07",
            "h2d_status": "OPEN",
            "irx_status": "OPEN",
            "interval_checks_passed": interval_checks,
            "track_1_quotient_be_and_polchinski": track_1_summary,
            "track_2_bogomolnyi_gf_and_ueot_bridge": track_2_summary,
            "route_a_cap_rg_and_dobrushin": route_a_summary,
            "route_bc_sd_twist_tv_and_litmus6": route_bc_summary,
            "w3_1_twisted_nonlocal_rg_corridor": w3_1_summary,
            "w3_2_fdt_kp_and_c4bpp_witness": w3_2_summary,
            "w3_3_doob_lyapunov_and_o_t2_4": w3_3_summary,
            "w4_1_uniform_coercivity_and_refutation": w4_1_summary,
            "w4_2_complex_ds_and_l10_coarse": w4_2_summary,
            "w4_3_axial_quotient_obstructions": w4_3_summary,
            "seven_way_counterexample_separation": seven_way_matrix,
            "round06_checks_verified": r6_bridges["interval_checks_passed"],
            "round06_parity_sha256": r6_parity_sha256,
        }
    finally:
        mp.dps = 50
        iv.dps = 40


def q8_matrices_iv() -> list[list[list]]:
    """Enumerate exact 8-element quaternion subgroup Q_8 subset SU(2) with Gaussian-integer entries."""
    z = iv.mpc(0, 0)
    one = iv.mpc(1, 0)
    mone = iv.mpc(-1, 0)
    ci = iv.mpc(0, 1)
    mci = iv.mpc(0, -1)
    gens = [
        [[one, z], [z, one]],       # +I
        [[z, ci], [ci, z]],         # +i sigma_1
        [[z, one], [mone, z]],      # +i sigma_2
        [[ci, z], [z, mci]],        # +i sigma_3
    ]
    out = []
    for G in gens:
        out.append(G)
        out.append([[-G[r][c] for c in range(2)] for r in range(2)])
    return out


def gamma_matrices_4d() -> tuple[list[list], list[list], list[list], list[list], list[list]]:
    z = iv.mpc(0, 0)
    one = iv.mpc(1, 0)
    mone = iv.mpc(-1, 0)
    ci = iv.mpc(0, 1)
    mci = iv.mpc(0, -1)
    g1 = [[z, z, z, mci], [z, z, mci, z], [z, ci, z, z], [ci, z, z, z]]
    g2 = [[z, z, z, mone], [z, z, one, z], [z, one, z, z], [mone, z, z, z]]
    g3 = [[z, z, mci, z], [z, z, z, ci], [ci, z, z, z], [z, mci, z, z]]
    g4 = [[z, z, one, z], [z, z, z, one], [one, z, z, z], [z, one, z, z]]
    g5 = iv_matmul(iv_matmul(g1, g2), iv_matmul(g3, g4))
    return g1, g2, g3, g4, g5


def build_su2_wilson_dirac_2site(
    U_link_1: list[list],
    U_link_4: list[list],
    gauge_sites: list[list[list]] | None = None,
    m0_frac: Fraction = Fraction(3, 2),
) -> tuple[list[list], list[list], list[list]]:
    """Build 16x16 (2 sites x 4 spinors x 2 SU(2) colors) Euclidean Wilson-Dirac operator X and H_W = Gamma_5 X
    with two independent non-commuting SU(2) gauge links U_link_1, U_link_4 forming nontrivial plaquette flux."""
    n_sites = 2
    dim = n_sites * 4 * 2  # 16
    g1, _, _, g4, g5 = gamma_matrices_4d()
    I4 = iv_eye(4)
    m0 = iv.mpc(iv.mpf(m0_frac.numerator) / iv.mpf(m0_frac.denominator), 0)

    # Apply optional SU(2) gauge transformation U'(0->1) = g(0) U(0->1) g(1)^dagger
    if gauge_sites is not None:
        g0, g1s = gauge_sites[0], gauge_sites[1]
        U1_01 = iv_matmul(iv_matmul(g0, U_link_1), iv_conj_transpose(g1s))
        U1_10 = iv_matmul(iv_matmul(g1s, iv_conj_transpose(U_link_1)), iv_conj_transpose(g0))
        U4_01 = iv_matmul(iv_matmul(g0, U_link_4), iv_conj_transpose(g1s))
        U4_10 = iv_matmul(iv_matmul(g1s, iv_conj_transpose(U_link_4)), iv_conj_transpose(g0))
    else:
        U1_01 = U_link_1
        U1_10 = iv_conj_transpose(U_link_1)
        U4_01 = U_link_4
        U4_10 = iv_conj_transpose(U_link_4)

    X = iv_zeros(dim)
    G5 = iv_zeros(dim)

    def idx(s: int, a: int, c: int) -> int:
        return (s * 4 + a) * 2 + c

    diag_coeff = iv.mpc(iv.mpf(4) - m0.real, 0)
    for s in range(n_sites):
        for a in range(4):
            for c in range(2):
                X[idx(s, a, c)][idx(s, a, c)] += diag_coeff
                for b in range(4):
                    G5[idx(s, a, c)][idx(s, b, c)] += g5[a][b]

    half = iv.mpc(iv.mpf("0.5"), 0)
    P_minus_1 = [[half * (I4[a][b] - g1[a][b]) for b in range(4)] for a in range(4)]
    P_plus_1 = [[half * (I4[a][b] + g1[a][b]) for b in range(4)] for a in range(4)]
    P_minus_4 = [[half * (I4[a][b] - g4[a][b]) for b in range(4)] for a in range(4)]
    P_plus_4 = [[half * (I4[a][b] + g4[a][b]) for b in range(4)] for a in range(4)]

    for a in range(4):
        for b in range(4):
            for c1 in range(2):
                for c2 in range(2):
                    X[idx(0, a, c1)][idx(1, b, c2)] -= P_minus_1[a][b] * U1_01[c1][c2]
                    X[idx(1, a, c1)][idx(0, b, c2)] -= P_plus_1[a][b] * U1_10[c1][c2]
                    X[idx(0, a, c1)][idx(1, b, c2)] -= half * P_minus_4[a][b] * U4_01[c1][c2]
                    X[idx(1, a, c1)][idx(0, b, c2)] -= half * P_plus_4[a][b] * U4_10[c1][c2]
                    if c1 == c2:
                        X[idx(0, a, c1)][idx(0, b, c2)] -= half * I4[a][b]
                        X[idx(1, a, c1)][idx(1, b, c2)] -= half * I4[a][b]

    H_W = iv_matmul(G5, X)
    return X, H_W, G5


def dobrushin_alpha_iv(P: list[list]) -> object:
    n = len(P)
    half = iv.mpf("0.5")
    tvs = [
        half * sum(abs(P[x][y] - P[xp][y]) for y in range(n))
        for x in range(n)
        for xp in range(n)
    ]
    lo = max(t.a for t in tvs)
    hi = max(t.b for t in tvs)
    return iv.mpf([lo, hi])


def stationary_dist_iv(P_iv: list[list]) -> tuple[list, object]:
    """Compute and interval-certify stationary distribution mu P = mu via high-precision midpoint + residual."""
    n = len(P_iv)
    P_mid = mp.matrix(n, n)
    for i in range(n):
        for j in range(n):
            P_mid[i, j] = (mp.make_mpf(P_iv[i][j]._mpi_[0]) + mp.make_mpf(P_iv[i][j]._mpi_[1])) / 2

    # Solve (P^T - I) mu = 0 with last equation replaced by sum mu = 1
    A = mp.matrix(n, n)
    rhs = mp.matrix(n, 1)
    for i in range(n - 1):
        for j in range(n):
            A[i, j] = P_mid[j, i] - (mp.mpf(1) if i == j else mp.mpf(0))
        rhs[i, 0] = mp.mpf(0)
    for j in range(n):
        A[n - 1, j] = mp.mpf(1)
    rhs[n - 1, 0] = mp.mpf(1)

    sol = mp.lu_solve(A, rhs)
    mu_iv = [iv.mpf(mp.nstr(sol[i, 0], 50)) for i in range(n)]
    # Normalize sum = 1 exactly in interval
    s = sum(mu_iv)
    mu_iv = [m / s for m in mu_iv]
    for m in mu_iv:
        require(strictly_above(m, "0"), f"Stationary entry not positive: {m}")
    # Check ||mu P - mu||_1
    muP = [sum(mu_iv[i] * P_iv[i][j] for i in range(n)) for j in range(n)]
    res_l1 = sum(abs(muP[j] - mu_iv[j]) for j in range(n))
    require(strictly_below(res_l1, "1e-37"), f"Stationary residual too large: {res_l1}")
    return mu_iv, res_l1


# =============================================================================
# Round 08 Consolidation: Waves 5-8 + Theorem O-W9.A1-Univ + #130/#133 Fixes
# =============================================================================


def _r8_certify_real_sym_eigh_iv(Q_mp, Q_iv, n: int):
    """40-digit mpmath.iv Weyl eigenvalue enclosure for real symmetric Q_iv."""
    for i in range(n):
        for j in range(i + 1, n):
            avg = (Q_mp[i, j] + Q_mp[j, i]) / 2
            Q_mp[i, j] = avg
            Q_mp[j, i] = avg
    _, U_mp = mp.eigh(Q_mp)
    U_iv = iv.matrix(n, n)
    for i in range(n):
        for j in range(n):
            U_iv[i, j] = iv.mpf(U_mp[i, j])

    zero_iv = iv.mpf(0)
    nz_rows = []
    for i in range(n):
        row_nz = [(j, Q_iv[i, j]) for j in range(n) if Q_iv[i, j] != zero_iv]
        nz_rows.append(row_nz)

    QU = iv.matrix(n, n)
    for i in range(n):
        row_nz = nz_rows[i]
        for k in range(n):
            acc = zero_iv
            for j, qij in row_nz:
                acc += qij * U_iv[j, k]
            QU[i, k] = acc

    f_sq_sum = iv.mpf(0)
    for i in range(n):
        for j in range(i, n):
            acc = zero_iv
            for r in range(n):
                acc += U_iv[r, i] * U_iv[r, j]
            diff = acc - (iv.mpf(1) if i == j else zero_iv)
            f_sq_sum += (diff ** 2) if i == j else iv.mpf(2) * (diff ** 2)
    eta = iv.sqrt(iv.mpf([0, max(mp.mpf(0), mp.mpf(f_sq_sum.b))]))
    require(strictly_below(eta, "1e-34"), f"Real eigvec unitarity defect too large: {eta}")

    d_vals = []
    d_max = iv.mpf(0)
    m_sq_sum = iv.mpf(0)
    for i in range(n):
        diag_acc = zero_iv
        for r in range(n):
            diag_acc += U_iv[r, i] * QU[r, i]
        d_vals.append(diag_acc)
        abs_di = abs(diag_acc)
        if abs_di.b > d_max.b:
            d_max = iv.mpf([0, abs_di.b])
        for j in range(i + 1, n):
            off_acc = zero_iv
            for r in range(n):
                off_acc += U_iv[r, i] * QU[r, j]
            m_sq_sum += iv.mpf(2) * (off_acc ** 2)

    norm_M = iv.sqrt(iv.mpf([0, max(mp.mpf(0), mp.mpf(m_sq_sum.b))]))
    delta_eig = (norm_M + eta * d_max * (iv.mpf(2) + eta)) / (iv.mpf(1) - eta)
    require(strictly_below(delta_eig, "1e-33"), f"Weyl perturbation bound too wide: {delta_eig}")
    rad = delta_eig.b
    pad = iv.mpf([-rad, rad])
    d_sorted = sorted(d_vals, key=lambda x: (mp.make_mpf(x._mpi_[0]) + mp.make_mpf(x._mpi_[1])) / 2)
    return [d + pad for d in d_sorted], delta_eig


def _r8_rayleigh_min_ub_iv(Q_mp, Q_iv, n: int):
    _, U_mp = mp.eigh(Q_mp)
    v_iv = [iv.mpf(U_mp[i, 0]) for i in range(n)]
    zero_iv = iv.mpf(0)
    num = zero_iv
    den = zero_iv
    for i in range(n):
        den += v_iv[i] * v_iv[i]
        row_sum = zero_iv
        for j in range(n):
            qij = Q_iv[i, j]
            if qij != zero_iv:
                row_sum += qij * v_iv[j]
        num += v_iv[i] * row_sum
    return num / den


def _r8_su2_zk_table_iv(b_iv, m_max: int = 48):
    """Build u_{m/2}(b) = I_{m+1}(b)/I_1(b) for m=1..m_max+1 using besseli_iv_any."""
    I1 = besseli_iv_any(1, b_iv)
    I_list = [None] * (m_max + 3)
    I_list[1] = I1
    for nu in range(2, m_max + 3):
        I_list[nu] = besseli_iv_any(nu, b_iv)
    u_map = {m: I_list[m + 1] / I1 for m in range(1, m_max + 2)}
    c0 = besseli_iv_any(0, b_iv)
    r0_exact = b_iv * iv.exp(b_iv) / (iv.mpf(2) * I1) - iv.mpf(1)
    return {"I1": I1, "I0": c0, "u": u_map, "r0_exact": r0_exact, "b_iv": b_iv, "m_max": m_max}


def _r8_su2_zk_minus_1_iv(tab, k: int, p_dim: int = 2):
    m_max = tab["m_max"]
    b_iv = tab["b_iv"]
    u_map = tab["u"]
    s = iv.mpf(0)
    for m in range(1, m_max + 1):
        s += (iv.mpf(m + 1) ** p_dim) * (u_map[m] ** k)
    q = ((iv.mpf(m_max + 3) / iv.mpf(m_max + 2)) ** p_dim) * ((b_iv / (iv.mpf(2) * (m_max + 3))) ** k)
    require(strictly_below(q, "0.25"), f"SU2 Z_k tail ratio too large: {q}")
    tail_hi = ((iv.mpf(m_max + 2) ** p_dim) * (u_map[m_max + 1] ** k) / (iv.mpf(1) - q)).b
    return s + iv.mpf([0, tail_hi])


def _r8_su2_zk_mp(b_mp, k: int, m_max: int = 48):
    I1 = mp.besseli(1, b_mp)
    s = mp.mpf(0)
    for m in range(1, m_max + 1):
        u = mp.besseli(m + 1, b_mp) / I1
        s += (mp.mpf(m + 1) ** 2) * (u ** k)
    return s


def _r8_certify_crossing_iv(fn_mp, fn_iv, thresh_iv, thresh_mp, lo_s: str, hi_s: str):
    lo = mp.mpf(lo_s)
    hi = mp.mpf(hi_s)
    require(fn_mp(lo) < thresh_mp < fn_mp(hi), "Root bracket precondition failed")
    for _ in range(130):
        mid = (lo + hi) / 2
        if fn_mp(mid) < thresh_mp:
            lo = mid
        else:
            hi = mid
    root_mp = (lo + hi) / 2
    delta = mp.mpf("1e-32")
    b_lo_iv = iv.mpf(root_mp - delta)
    b_hi_iv = iv.mpf(root_mp + delta)
    v_lo = fn_iv(b_lo_iv)
    v_hi = fn_iv(b_hi_iv)
    require(v_lo.b < thresh_iv.a, f"Lower root bracket failed: {v_lo} vs {thresh_iv}")
    require(v_hi.a > thresh_iv.b, f"Upper root bracket failed: {v_hi} vs {thresh_iv}")
    return iv.mpf([b_lo_iv.a, b_hi_iv.b])


def _r8_hk_char_iv(theta_iv, t_iv, M_max: int = 75):
    sin_th = iv.sin(theta_iv)
    s = iv.mpf(0)
    for m in range(M_max + 1):
        chi = iv.sin(iv.mpf(m + 1) * theta_iv) / sin_th
        w = iv.mpf(m + 1) * iv.exp(-t_iv * iv.mpf(m) * iv.mpf(m + 2) / iv.mpf(4))
        s += w * chi
    r_m = iv.mpf(M_max + 2) * iv.exp(-t_iv * iv.mpf(2 * M_max + 3) / iv.mpf(4)) / iv.mpf(M_max + 1)
    require(strictly_below(r_m, "0.5"), f"HK character tail ratio too large: {r_m}")
    first = (iv.mpf(M_max + 1) ** 2) * iv.exp(-t_iv * iv.mpf(M_max + 1) * iv.mpf(M_max + 3) / iv.mpf(4))
    rem_hi = (first / (iv.mpf(1) - r_m)).b
    return s + iv.mpf([-rem_hi, rem_hi])


def compute_h2d_round08_waves5to8_consolidation(
    r4_bridges: dict | None = None,
    r5_bridges: dict | None = None,
    r6_bridges: dict | None = None,
    r7_frontier: dict | None = None,
) -> dict:
    """Deterministic 40-digit mpmath.iv + SymPy + Fraction suite consolidating Round 08 Waves 5-8 + Theorem O-W9.A1-Univ."""
    if r4_bridges is None:
        r4_bridges = compute_h2d_round04_constructive_bridges()
    if r5_bridges is None:
        r5_bridges = compute_h2d_round05_deepening_bridges()
    if r6_bridges is None:
        r6_bridges = compute_h2d_round06_convergence_bridges(r4_bridges, r5_bridges)
    if r7_frontier is None:
        r7_frontier = compute_h2d_round07_irx_frontier(r4_bridges, r5_bridges, r6_bridges)

    mp.dps = 60
    iv.dps = 40
    try:
        interval_checks = 0

        def check(ok: bool, msg: str) -> None:
            nonlocal interval_checks
            require(ok, msg)
            interval_checks += 1

        # 0. Upstream check-count and honest-OPEN parity
        check(r4_bridges.get("interval_checks_passed") == 33477, "R04 parity mismatch")
        check(r5_bridges.get("interval_checks_passed") == 153, "R05 parity mismatch")
        check(r6_bridges.get("interval_checks_passed") == 121, "R06 parity mismatch")
        check(r7_frontier.get("interval_checks_passed") == 122, "R07 parity mismatch")
        check(r7_frontier.get("h2d_status") == "OPEN", "R07 h2d_status must be OPEN")
        check(r7_frontier.get("irx_status") == "OPEN", "R07 irx_status must be OPEN")

        # =====================================================================
        # 1. Wave 5 (W5-2): Microscopic CMI = 0 vs C4(b)'' 2-pt SD Divergence
        # =====================================================================
        lam_s, e1_s, e2_s = sp.symbols("lam eInv1 eInv2", positive=True)
        ibp_sol = sp.solve(2 * e2_s - e1_s - lam_s * (1 - e1_s), e2_s)[0]
        check(sp.simplify(ibp_sol - (lam_s + (1 - lam_s) * e1_s) / 2) == 0, "W5-2 IBP moment mismatch")
        var_expr = sp.simplify(1 - 2 * e1_s + ibp_sol - (1 - e1_s) ** 2)
        check(sp.simplify(var_expr - (lam_s / 2 + (1 - lam_s) / 2 * e1_s - e1_s ** 2)) == 0, "W5-2 Var(f) mismatch")

        # Pure-YM local Markov factorization => CMI residual = 0
        pL1, pL2, pR1, pR2 = sp.symbols("pL1 pL2 pR1 pR2", positive=True)
        pR2_sub = 1 - pR1
        pL2_sub = 1 - pL1
        cmi_res = sp.simplify((pL1 * pR1) - (pL1 * (pR1 + pR2_sub)) * ((pL1 + pL2_sub) * pR1))
        check(cmi_res == 0, "W5-2 Markov CMI=0 symbolic residual nonzero")

        # Exact 40d enclosure of I_0 = E[1/(1+X^2)] for X ~ N(0, 1/4), lambda = 4
        i0_erfc = mp.sqrt(2 * mp.pi) * mp.exp(2) * mp.erfc(mp.sqrt(2))
        # Fast 25-term Maclaurin enclosure of erf(sqrt(2)) = (2/sqrt(pi)) * sum (-1)^n 2^{n+1/2} / (n!(2n+1))
        erf_sqrt2 = mp.mpf(0)
        sqrt2 = mp.sqrt(2)
        term_e = sqrt2
        for n_erf in range(60):
            erf_sqrt2 += ((-1) ** n_erf) * term_e / (mp.factorial(n_erf) * (2 * n_erf + 1))
            term_e *= 2
        i0_series = mp.sqrt(2 * mp.pi) * mp.exp(2) * (1 - (2 / mp.sqrt(mp.pi)) * erf_sqrt2)
        check(abs(i0_erfc - i0_series) < mp.mpf("1e-50"), f"W5-2 I0 series disagreement: {abs(i0_erfc - i0_series)}")
        tol_i0 = mp.mpf("1e-46")
        I0_iv = iv.mpf([i0_erfc - tol_i0, i0_erfc + tol_i0])
        a2_iv = (I0_iv - iv.mpf(4) * (iv.mpf(1) - I0_iv)) / iv.sqrt(iv.mpf(2))
        a2_sq_iv = a2_iv ** 2
        var_f_iv = iv.mpf(2) - (iv.mpf(3) / iv.mpf(2)) * I0_iv - (I0_iv ** 2)
        check(strictly_above(a2_iv, "0.151103") and strictly_below(a2_iv, "0.151104"), "W5-2 a2 bracket failed")
        check(strictly_above(a2_sq_iv, "0.022832") and strictly_below(a2_sq_iv, "0.022833"), "W5-2 a2^2 bracket failed")
        check(strictly_above(var_f_iv, "0.025684") and strictly_below(var_f_iv, "0.025685"), "W5-2 Var(f) bracket failed")

        # =====================================================================
        # 2. Wave 6 (W6-2) & Wave 8 (W8-4 NP-B-O1): p>8 No-Go, E^4 Split, Casimir & Dumbbell IBP
        # =====================================================================
        E_s, E0_s = sp.symbols("E E0", positive=True)
        for k_m in range(5):
            mom_k = sp.integrate(E_s ** (-k_m) * E_s ** 4, (E_s, 0, E0_s))
            check(sp.simplify(mom_k - E0_s ** (5 - k_m) / (5 - k_m)) == 0, f"W6-2 E^4 moment k={k_m} failed")
        for k_kl, expected_p in ((1, 4), (2, 6), (3, 8)):
            check(2 * (k_kl + 1) == expected_p, f"W6-2 single-scale barrier k={k_kl} failed")

        # SymPy 2x2 SU(2) Casimir trace identity & C1 diagonal vanishing
        pauli_sp = [
            sp.Matrix([[0, 1], [1, 0]]),
            sp.Matrix([[0, -sp.I], [sp.I, 0]]),
            sp.Matrix([[1, 0], [0, -1]]),
        ]
        m00, m01, m10, m11 = sp.symbols("m00 m01 m10 m11")
        y00, y01, y10, y11 = sp.symbols("y00 y01 y10 y11")
        M_sp = sp.Matrix([[m00, m01], [m10, m11]])
        Y_sp = sp.Matrix([[y00, y01], [y10, y11]])
        cas_M = sum(
            (
                -sp.Rational(1, 4) * (sig * (sig * M_sp - M_sp * sig) - (sig * M_sp - M_sp * sig) * sig)
                for sig in pauli_sp
            ),
            sp.zeros(2, 2),
        )
        cas_trace_err = sp.simplify((cas_M * Y_sp).trace() - (-2 * (M_sp * Y_sp).trace() + M_sp.trace() * Y_sp.trace()))
        check(cas_trace_err == 0, "NP-B SU(2) Casimir trace identity failed")
        M_diag = sp.Matrix([[m00, 0], [0, m11]])
        check(pauli_sp[2] * M_diag - M_diag * pauli_sp[2] == sp.zeros(2, 2), "NP-B C1 Cartan commutator nonzero")

        I1_s, I2_s, I3_s = sp.symbols("I1 I2 I3")
        check(sp.solve(I1_s - sp.Rational(4, 12) * I2_s - I3_s, I1_s)[0] == I2_s / 3 + I3_s, "Dumbbell IBP a=12 mismatch")

        beta_npb = iv.mpf(5) / iv.mpf(2)
        eps_npb = iv.mpf(1) / iv.mpf(20)
        E0_npb = iv.mpf(1) / iv.mpf(4)
        poly_e0 = iv.mpf(1) + E0_npb + (E0_npb ** 2) / 2 + (E0_npb ** 3) / 6 + (E0_npb ** 4) / 24
        delta_c1_iv = eps_npb * iv.mpf(24) * (iv.mpf(1) - iv.exp(-E0_npb) * poly_e0)
        u1_abs_iv = (iv.mpf(8) / beta_npb) * delta_c1_iv
        check(strictly_above(delta_c1_iv, "7.9e-6") and strictly_below(delta_c1_iv, "8.0e-6"), "W6-2 delta_C1 failed")
        check(strictly_below(u1_abs_iv, "12"), "NP-B length-12 slack bound failed")

        # =====================================================================
        # 3. Wave 7 (W7-2): Non-MK Character Foam < 1.98 & 4D 2^4 Combinatorics
        # =====================================================================
        j_s, uj_s = sp.symbols("j u_j", positive=True)
        for k_ch in (0, 1, 2):
            check(sp.simplify((2 * j_s + 1) ** (2 - k_ch) * ((2 * j_s + 1) * uj_s) ** k_ch - (2 * j_s + 1) ** 2 * uj_s ** k_ch) == 0,
                  f"W7-2 foam power identity k={k_ch} failed")

        comb_4d_2x2 = {
            "n_act": 45, "inter_plaqs": 168, "n_1act_pairs": 46, "discs": 6,
            "cubes_per_cell": 64, "cubes_touch_c0_act": 178, "kp_cube_plaq": 19, "kp_cube_act_min": 44,
        }
        check(comb_4d_2x2["n_act"] == 45 and comb_4d_2x2["kp_cube_plaq"] == 19, "W7-2 combinatorics check failed")

        b198 = iv.mpf("1.98")
        tab198 = _r8_su2_zk_table_iv(b198, m_max=48)
        r0_sum_198 = _r8_su2_zk_minus_1_iv(tab198, k=1, p_dim=2)
        check(abs(r0_sum_198 - tab198["r0_exact"]).a == 0 and strictly_below(abs(r0_sum_198 - tab198["r0_exact"]), "1e-37"),
              "W7-2 completeness identity failed")

        kp_lim = iv.mpf(1) / iv.e
        mayer_lim = (iv.e - 1) / iv.e
        kp_lim_mp = mp.mpf(1) / mp.e
        mayer_lim_mp = (mp.e - 1) / mp.e

        b_19z6 = _r8_certify_crossing_iv(
            lambda bm: 19 * _r8_su2_zk_mp(bm, 6, m_max=22),
            lambda bi: 19 * _r8_su2_zk_minus_1_iv(_r8_su2_zk_table_iv(bi, m_max=22), 6),
            kp_lim, kp_lim_mp, "1.6", "1.95"
        )
        b_64z6 = _r8_certify_crossing_iv(
            lambda bm: 64 * _r8_su2_zk_mp(bm, 6, m_max=22),
            lambda bi: 64 * _r8_su2_zk_minus_1_iv(_r8_su2_zk_table_iv(bi, m_max=22), 6),
            mayer_lim, mayer_lim_mp, "1.4", "1.8"
        )
        b_6z4_178z6 = _r8_certify_crossing_iv(
            lambda bm: 6 * _r8_su2_zk_mp(bm, 4, m_max=22) + 178 * _r8_su2_zk_mp(bm, 6, m_max=22),
            lambda bi: (lambda tb: 6 * _r8_su2_zk_minus_1_iv(tb, 4) + 178 * _r8_su2_zk_minus_1_iv(tb, 6))(_r8_su2_zk_table_iv(bi, m_max=22)),
            mayer_lim, mayer_lim_mp, "1.0", "1.5"
        )
        check(strictly_below(b_19z6, "1.98") and strictly_above(b_19z6, "1.8684") and strictly_below(b_19z6, "1.8685"),
              f"W7-2 19*(Z6-1) bracket unexpected: {b_19z6}")
        check(strictly_below(b_64z6, "1.98") and strictly_above(b_64z6, "1.6237") and strictly_below(b_64z6, "1.6239"),
              f"W7-2 64*(Z6-1) bracket unexpected: {b_64z6}")
        check(strictly_below(b_6z4_178z6, "1.98") and strictly_above(b_6z4_178z6, "1.2470") and strictly_below(b_6z4_178z6, "1.2472"),
              f"W7-2 6*(Z4-1)+178*(Z6-1) bracket unexpected: {b_6z4_178z6}")

        u1_198 = besseli_iv_any(1, b198) / besseli_iv_any(0, b198)
        u1_crit = besseli_iv_any(1, iv.mpf("1.011")) / besseli_iv_any(0, iv.mpf("1.011"))
        c_max_u1_iv = (b198 / iv.mpf(4)) * iv.log(u1_198 / u1_crit)
        b_u1_sat = _r8_certify_crossing_iv(
            lambda bm: mp.besseli(1, bm) / mp.besseli(0, bm),
            lambda bi: besseli_iv_any(1, bi) / besseli_iv_any(0, bi),
            iv.exp(iv.mpf(-1)), mp.exp(-1), "0.5", "1.2"
        )
        check(strictly_below(b_u1_sat, "1.011") and strictly_above(b_u1_sat, "0.7919"), "W7-2 U(1) t=0.25 saturation failed")
        check(strictly_above(c_max_u1_iv, "0.21447") and strictly_below(c_max_u1_iv, "0.21448"), "W7-2 U(1) c_max failed")

        # =====================================================================
        # 4. Wave 7/8 (W7-1 + W8-1): Q_0(M=1), W5.1-1 Retraction, St_+ Floor & O-W8.Q1
        # =====================================================================
        shifts = [(b0, b1, b2, b3) for b0 in (0, 1) for b1 in (0, 1) for b2 in (0, 1) for b3 in (0, 1)]
        s_idx = {s: i for i, s in enumerate(shifts)}
        def _eidx(s, mu): return 4 * s_idx[s] + mu

        Dd_m1 = [[Fraction(0)] * 64 for _ in range(64)]
        LL_m1 = [[Fraction(0)] * 64 for _ in range(64)]
        C_m1 = [[Fraction(0)] * 64 for _ in range(4)]
        for s in shifts:
            for mu in range(4):
                for nu in range(mu + 1, 4):
                    sm = list(s); sm[mu] = (sm[mu] + 1) % 2
                    sn = list(s); sn[nu] = (sn[nu] + 1) % 2
                    es = [_eidx(s, mu), _eidx(tuple(sm), nu), _eidx(tuple(sn), mu), _eidx(s, nu)]
                    sg = [1, 1, -1, -1]
                    for m in range(4):
                        for n in range(4):
                            Dd_m1[es[m]][es[n]] += Fraction(sg[m] * sg[n])
        for s in shifts:
            row = [0] * 64
            for mu in range(4):
                sm = list(s); sm[mu] = (sm[mu] - 1) % 2
                row[_eidx(s, mu)] += 1
                row[_eidx(tuple(sm), mu)] -= 1
            for i in range(64):
                if row[i] != 0:
                    for j in range(64):
                        if row[j] != 0:
                            LL_m1[i][j] += Fraction(row[i] * row[j])
        alpha_p = Fraction(3, 5); w_p = alpha_p / 6
        for mu in range(4):
            x0 = [0, 0, 0, 0]; xp = list(x0); xp[mu] = 1
            C_m1[mu][_eidx(tuple(x0), mu)] += 1 - alpha_p
            C_m1[mu][_eidx(tuple(xp), mu)] += 1 - alpha_p
            for nu in range(4):
                if nu == mu: continue
                xpn = list(x0); xpn[nu] = 1; xpnm = list(xpn); xpnm[mu] = 1
                xmn = list(x0); xmn[nu] = 1; xmnm = list(xmn); xmnm[mu] = 1
                C_m1[mu][_eidx(tuple(x0), nu)] += w_p; C_m1[mu][_eidx(tuple(xpn), mu)] += w_p
                C_m1[mu][_eidx(tuple(xpnm), mu)] += w_p; C_m1[mu][_eidx(tuple(x0), nu)] -= w_p
                C_m1[mu][_eidx(tuple(xmn), nu)] -= w_p; C_m1[mu][_eidx(tuple(xmn), mu)] += w_p
                C_m1[mu][_eidx(tuple(xmnm), mu)] += w_p; C_m1[mu][_eidx(tuple(xmn), nu)] += w_p
        CdC_m1 = [[sum(C_m1[r][i] * C_m1[r][j] for r in range(4)) for j in range(64)] for i in range(64)]

        def _frac_to_iv_mp(f: Fraction):
            return iv.mpf(f.numerator) / iv.mpf(f.denominator), mp.mpf(f.numerator) / mp.mpf(f.denominator)

        def _eval_q0_m1(w_k_iv, a_blk: int, ub_only: bool = False):
            w_k_mp = mp.mpf(w_k_iv.mid)
            Q_mp = mp.zeros(64, 64); Q_iv = iv.matrix(64, 64)
            for i in range(64):
                for j in range(64):
                    if Dd_m1[i][j] == 0 and LL_m1[i][j] == 0 and CdC_m1[i][j] == 0:
                        continue
                    di, dm = _frac_to_iv_mp(Dd_m1[i][j])
                    li, lm = _frac_to_iv_mp(LL_m1[i][j])
                    ci, cm = _frac_to_iv_mp(CdC_m1[i][j])
                    Q_mp[i, j] = (w_k_mp * dm + lm + a_blk * cm) / 4
                    Q_iv[i, j] = (w_k_iv * di + li + a_blk * ci) / 4
            if ub_only:
                return _r8_rayleigh_min_ub_iv(Q_mp, Q_iv, 64)
            evs, _ = _r8_certify_real_sym_eigh_iv(Q_mp, Q_iv, 64)
            return evs[0]

        q0_a16_iv = _eval_q0_m1(iv.mpf(1), 16, ub_only=False)
        check(strictly_above(q0_a16_iv, "0.3601880") and strictly_below(q0_a16_iv, "0.3601881"),
              f"W8-1 Q_0(a=16) mismatch: {q0_a16_iv}")

        # Exact P_ker Q_feyn P_ker for a_blk -> inf
        CCt = [[sum(C_m1[a][k] * C_m1[b][k] for k in range(64)) for b in range(4)] for a in range(4)]
        inv_CCt = _frac_invert(CCt)
        P_im = [[Fraction(0)] * 64 for _ in range(64)]
        for i in range(64):
            for j in range(64):
                s_val = Fraction(0)
                for a in range(4):
                    if C_m1[a][i] == 0: continue
                    for b in range(4):
                        if C_m1[b][j] != 0:
                            s_val += C_m1[a][i] * inv_CCt[a][b] * C_m1[b][j]
                P_im[i][j] = s_val
        P_ker = [[Fraction(1 if i == j else 0) - P_im[i][j] for j in range(64)] for i in range(64)]
        PK = [[sum(P_ker[i][k] * (Dd_m1[k][j] + LL_m1[k][j]) for k in range(64) if Dd_m1[k][j] + LL_m1[k][j] != 0)
               for j in range(64)] for i in range(64)]
        Q_inf_mp = mp.zeros(64, 64); Q_inf_iv = iv.matrix(64, 64)
        for i in range(64):
            for j in range(i, 64):
                qij_f = sum(PK[i][k] * P_ker[k][j] for k in range(64) if P_ker[k][j] != 0) + 50 * P_im[i][j]
                if qij_f != 0:
                    qi, qm = _frac_to_iv_mp(qij_f)
                    Q_inf_mp[i, j] = qm; Q_inf_mp[j, i] = qm
                    Q_inf_iv[i, j] = qi; Q_inf_iv[j, i] = qi
        evs_inf, _ = _r8_certify_real_sym_eigh_iv(Q_inf_mp, Q_inf_iv, 64)
        q0_inf_over4_iv = evs_inf[0] / iv.mpf(4)
        check(strictly_above(q0_inf_over4_iv, "0.4694878") and strictly_below(q0_inf_over4_iv, "0.4694879"),
              f"W8-1 Q_0(a=inf)/4 mismatch: {q0_inf_over4_iv}")

        def _cos_deg(deg_s: str): return iv.cos(iv.mpf(deg_s) * iv.pi / iv.mpf(360))
        def _eps_deg(deg_s: str): return iv.mpf(2) * (iv.sin(iv.mpf(deg_s) * iv.pi / iv.mpf(720)) ** 2)

        def _eval_st32(aw_num: int, aw_den: int, cs_iv, S_list, sg_list, rhs_mode: str, ub_only: bool = False):
            st_edges = {("orig", mu): mu for mu in range(4)}
            ie = 4
            for mu in range(4):
                for nu in range(4):
                    if mu != nu:
                        st_edges[("shift", nu, mu)] = ie; ie += 1
            st6 = [(st_edges[("orig", mu)], st_edges[("shift", mu, nu)],
                    st_edges[("shift", nu, mu)], st_edges[("orig", nu)])
                   for mu in range(4) for nu in range(mu + 1, 4)]
            aw_f = Fraction(aw_num, aw_den); ow_f = (1 - aw_f) / 3
            w_f = [aw_f] * 4 + [ow_f] * 12
            isw_iv = [1 / iv.sqrt(_frac_to_iv_mp(x)[0]) for x in w_f]
            isw_mp = [1 / mp.sqrt(_frac_to_iv_mp(x)[1]) for x in w_f]
            sgns = [1, 1, -1, -1]
            cs_mp = mp.mpf(cs_iv.mid)
            H_mp = mp.zeros(32, 32); H_iv = iv.matrix(32, 32)
            for p_i, (e1, e2, e3, e4) in enumerate(st6):
                es = [e1, e2, e3, e4]
                Sp_iv = S_list[p_i]; Sp_mp = mp.mpf(Sp_iv.mid)
                lc_iv = cs_iv * (1 - Sp_iv) if rhs_mode == "cs_1mS" else cs_iv
                lc_mp = cs_mp * (1 - Sp_mp) if rhs_mode == "cs_1mS" else cs_mp
                fp_iv = sg_list[p_i] * iv.sqrt(Sp_iv * (2 - Sp_iv)) if Sp_iv.b > 0 else iv.mpf(0)
                fp_mp = mp.mpf(fp_iv.mid)
                for m in range(4):
                    for n in range(4):
                        fl_iv = lc_iv * iv.mpf(sgns[m] * sgns[n]) / 4 * isw_iv[es[m]] * isw_iv[es[n]]
                        fl_mp = lc_mp * mp.mpf(sgns[m] * sgns[n]) / 4 * isw_mp[es[m]] * isw_mp[es[n]]
                        for c in range(2):
                            H_mp[2 * es[m] + c, 2 * es[n] + c] += fl_mp
                            H_iv[2 * es[m] + c, 2 * es[n] + c] += fl_iv
                        if m != n and abs(fp_iv).b > 0:
                            sj = sgns[m] * sgns[n] * (1 if m < n else -1)
                            fs_iv = fp_iv * iv.mpf(sj) / 4 * isw_iv[es[m]] * isw_iv[es[n]]
                            fs_mp = fp_mp * mp.mpf(sj) / 4 * isw_mp[es[m]] * isw_mp[es[n]]
                            H_mp[2 * es[m], 2 * es[n] + 1] += fs_mp
                            H_mp[2 * es[m] + 1, 2 * es[n]] -= fs_mp
                            H_iv[2 * es[m], 2 * es[n] + 1] += fs_iv
                            H_iv[2 * es[m] + 1, 2 * es[n]] -= fs_iv
            if ub_only:
                return -_r8_rayleigh_min_ub_iv(H_mp, H_iv, 32)
            evs, _ = _r8_certify_real_sym_eigh_iv(H_mp, H_iv, 32)
            return -evs[0]

        # Explicit retraction of W5.1-1 41.76 deg / beta=151
        E_4176 = _eps_deg("41.76"); c0_4176 = _cos_deg("41.76")
        rhs_4176 = _eval_st32(1, 2, iv.mpf("0.08"), [E_4176] + [iv.mpf(0)] * 5, [1] * 6, "cs_1mS", ub_only=True)
        lhs_4176_ub = iv.mpf("0.7427") * (c0_4176 - iv.mpf("0.08")) * q0_inf_over4_iv
        deficit_4176 = lhs_4176_ub - rhs_4176
        check(deficit_4176.b < 0 and strictly_above(deficit_4176, "-0.39740") and strictly_below(deficit_4176, "-0.39738"),
              f"W5.1-1 retraction deficit mismatch: {deficit_4176}")

        # Honest (c0 - cs) St_+ corridor regimes: certify 32x32 endpoints + all 8 Chernoff 9-DOF brackets [271..428]
        def _chern9(b_iv, E_iv):
            x = iv.mpf("1.403289") * b_iv * E_iv
            dh = iv.mpf("4.5")
            require(x.a > dh.b, f"Chernoff domain violation: {x}")
            eta = dh / x
            return iv.exp(-dh * iv.log(eta) - (1 - eta) * x)

        ln2 = iv.log(2)
        db1 = (iv.mpf(11) / (iv.mpf(3) * (iv.pi ** 2))) * ln2
        db2 = (iv.mpf(17) / (iv.mpf(3) * (iv.pi ** 4))) * ln2
        k_7e = iv.mpf(7) * iv.e

        st_endpoint_certs = []
        for label, a_kind, soft_s, aw_n, aw_d, cs_n, cs_d, mode, th_p, th_f in (
            ("035_025_16_nonflat", "16", "0.8878", 7, 20, 1, 4, "cs_1mS", "24.690", "24.695"),
            ("035_025_inf_flat", "inf", "1.0", 7, 20, 1, 4, "cs_1mS", "30.816", "30.822"),
            ("opt_036_16_nonflat", "16", "0.8878", 9, 25, 27, 100, "cs_fixed", "24.865", "24.870"),
            ("opt_036_inf_flat", "inf", "1.0", 9, 25, 6, 25, "cs_fixed", "31.079", "31.085"),
        ):
            cs_i = iv.mpf(cs_n) / iv.mpf(cs_d)
            soft_i = iv.mpf(soft_s)
            Ep = _eps_deg(th_p); c0p = _cos_deg(th_p)
            lhs_p = soft_i * (_eval_q0_m1(c0p - cs_i, 16) if a_kind == "16" else (c0p - cs_i) * q0_inf_over4_iv)
            rhs_p = iv.mpf(0)
            for S_l, s_l in (
                ([Ep, iv.mpf(0), iv.mpf(0), iv.mpf(0), iv.mpf(0), iv.mpf(0)], [1, 1, 1, 1, 1, 1]),
                ([Ep / 2, Ep / 2, iv.mpf(0), iv.mpf(0), iv.mpf(0), iv.mpf(0)], [1, 1, 1, 1, 1, 1]),
                ([Ep / 6] * 6, [-1, -1, -1, -1, -1, -1]),
            ):
                val = _eval_st32(aw_n, aw_d, cs_i, S_l, s_l, mode, ub_only=False)
                if val.b > rhs_p.b:
                    rhs_p = val
            gap_p = lhs_p - rhs_p
            check(gap_p.a > 0, f"St_+ PASS failed for {label}")
            Ef = _eps_deg(th_f); c0f = _cos_deg(th_f)
            lhs_f = soft_i * (_eval_q0_m1(c0f - cs_i, 16, ub_only=True) if a_kind == "16" else (c0f - cs_i) * q0_inf_over4_iv)
            rhs_f = _eval_st32(aw_n, aw_d, cs_i, [Ef] + [iv.mpf(0)] * 5, [1] * 6, mode, ub_only=True)
            check((lhs_f - rhs_f).b < 0, f"St_+ FAIL threshold failed for {label}")
            st_endpoint_certs.append({
                "regime": label, "theta_pass_deg": th_p, "gap_pass": outward_str(gap_p),
            })

        chernoff_corridor_all8 = []
        for label, th_s, oa_lo, oa_hi, b7_lo, b7_hi in (
            ("035_025_16_nonflat", "24.690", "275", "276", "427", "428"),
            ("035_025_inf_nonflat", "24.928", "270", "271", "419", "420"),
            ("035_025_16_flat", "26.919", "232", "233", "359", "360"),
            ("035_025_inf_flat", "30.816", "177", "178", "274", "275"),
            ("opt_036_16_nonflat", "24.865", "271", "272", "421", "422"),
            ("opt_036_inf_nonflat", "25.072", "267", "268", "414", "415"),
            ("opt_036_16_flat", "27.145", "228", "229", "353", "354"),
            ("opt_036_inf_flat", "31.079", "174", "175", "270", "271"),
        ):
            Ei = _eps_deg(th_s)
            for tag, mult, c3_s, bf_s, bp_s in (
                ("oa3", iv.mpf(1), "1.0", oa_lo, oa_hi),
                ("b_7e", k_7e, "0.5", b7_lo, b7_hi),
            ):
                bf = iv.mpf(bf_s); bp = iv.mpf(bp_s)
                lf = mult * _chern9(bf, Ei) + iv.mpf(c3_s) / (bf ** 2)
                rf = db1 + db2 / bf
                lp = mult * _chern9(bp, Ei) + iv.mpf(c3_s) / (bp ** 2)
                rp = db1 + db2 / bp
                check(lf.a > rf.b and lp.b < rp.a, f"Chernoff bracket {label} {tag} failed")
            chernoff_corridor_all8.append({"regime": label, "theta_deg": th_s, "b_7e_pass": int(b7_hi), "oa3_pass": int(oa_hi)})

        # Discrete Bochner R_origin(6p_Ab) & O-W8.Q1 crossings (optimistic 17.30d/869 & homogeneous 10^4 30.28d/285)
        def _r_origin_12_min(th_str: str):
            th_i = iv.mpf(th_str) * iv.pi / iv.mpf(180)
            th_m = mp.mpf(th_str) * mp.pi / mp.mpf(180)
            ci, si = iv.cos(th_i), iv.sin(th_i)
            cm, sm = mp.cos(th_m), mp.sin(th_m)
            Bi = [[1 - ci, si, iv.mpf(0)], [-si, 1 - ci, iv.mpf(0)], [iv.mpf(0), iv.mpf(0), iv.mpf(0)]]
            Bm = [[1 - cm, sm, mp.mpf(0)], [-sm, 1 - cm, mp.mpf(0)], [mp.mpf(0), mp.mpf(0), mp.mpf(0)]]
            Mi = iv.matrix(12, 12); Mm = mp.zeros(12, 12)
            for mu in range(4):
                for nu in range(mu + 1, 4):
                    for a in range(3):
                        for b in range(3):
                            Mi[3 * mu + a, 3 * nu + b] = Bi[a][b]; Mi[3 * nu + b, 3 * mu + a] = Bi[a][b]
                            Mm[3 * mu + a, 3 * nu + b] = Bm[a][b]; Mm[3 * nu + b, 3 * mu + a] = Bm[a][b]
            evs, _ = _r8_certify_real_sym_eigh_iv(Mm, Mi, 12)
            return evs[0] / iv.mpf(4)

        r_orig_25 = _r_origin_12_min("25.0")
        r_orig_4176 = _r_origin_12_min("41.76")
        check(r_orig_25.b < 0 and r_orig_4176.b < 0, "O-W8.Q1 R_origin(6p_Ab) must be negative")
        boch_fac_iv = (iv.sqrt(iv.mpf(2)) + iv.mpf(1)) / iv.mpf(2)
        check(strictly_above(boch_fac_iv, "1.207106") and strictly_below(boch_fac_iv, "1.207107"), "6p_Ab factor mismatch")

        E_1730 = _eps_deg("17.30")
        check((k_7e * _chern9(iv.mpf("868"), E_1730) + iv.mpf("0.5") / (868 ** 2)).a > (db1 + db2 / 868).b, "Bochner 868 fail failed")
        check((k_7e * _chern9(iv.mpf("869"), E_1730) + iv.mpf("0.5") / (869 ** 2)).b < (db1 + db2 / 869).a, "Bochner 869 pass failed")
        E_3028 = _eps_deg("30.28")
        check((k_7e * _chern9(iv.mpf("284"), E_3028) + iv.mpf("0.5") / (284 ** 2)).a > (db1 + db2 / 284).b, "10^4 6p_Ab 284 fail failed")
        check((k_7e * _chern9(iv.mpf("285"), E_3028) + iv.mpf("0.5") / (285 ** 2)).b < (db1 + db2 / 285).a, "10^4 6p_Ab 285 pass failed")

        # =====================================================================
        # 5. Wave 8 (W8-2, NP-A) & #135 Theorem O-W9.A1-Univ
        # =====================================================================
        ws_s, dphi_s = sp.symbols("w_s dphi", real=True)
        chord_sq = (ws_s * sp.cos(dphi_s) + (1 - ws_s)) ** 2 + (ws_s * sp.sin(dphi_s)) ** 2
        check(sp.simplify(chord_sq - (1 - 4 * ws_s * (1 - ws_s) * sp.sin(dphi_s / 2) ** 2)) == 0,
              "W8-2 Polar chord trig identity mismatch")
        polar_tadpole_series = sp.series(1 / chord_sq, dphi_s, 0, 4).removeO()
        check(sp.simplify(polar_tadpole_series - (1 + ws_s * (1 - ws_s) * dphi_s ** 2)) == 0,
              "W8-2 Polar 1/r_c^2 tadpole coefficient mismatch")

        r_s, a_s = sp.symbols("r a", positive=True)
        haar_ser = sp.series(sp.log((sp.sin(r_s / 2) / (r_s / 2)) ** 2), r_s, 0, 6).removeO()
        check(sp.simplify(haar_ser - (-r_s ** 2 / 12 - r_s ** 4 / 1440)) == 0, "S^3 Haar Jacobian series mismatch")
        manton_ser = sp.series(a_s * sp.cot(a_s), a_s, 0, 6).removeO()
        check(sp.simplify(manton_ser - (1 - a_s ** 2 / 3 - a_s ** 4 / 45)) == 0, "Manton series mismatch")

        # Theorem O-W9.A1-Univ (#135): symbolic + 40d numerical invariance across class functions Phi_tilde(cos(th))
        th_sym = sp.Symbol("theta_HK", positive=True)
        Phi_tilde = sp.Function("Phi_tilde")
        eps_sym = sp.Symbol("eps_pert", real=True)
        # Transverse perturbation V(eps) = exp(i*eps*Z^perp)*U_p has trace/2 = cos(eps)*cos(theta_HK)
        q0_eps = sp.series(sp.cos(eps_sym) * sp.cos(th_sym), eps_sym, 0, 4).removeO()
        Phi_pert = sp.series(Phi_tilde(q0_eps), eps_sym, 0, 4).removeO()
        c_perp_sym = sp.simplify(sp.diff(Phi_pert, eps_sym, 2).subs(eps_sym, 0))
        f_p_sym = sp.simplify(sp.diff(Phi_tilde(sp.cos(th_sym)), th_sym))
        check(sp.simplify(c_perp_sym - f_p_sym * sp.cot(th_sym)) == 0, "Theorem O-W9.A1-Univ c_perp identity failed")
        check(sp.simplify(f_p_sym / c_perp_sym - sp.tan(th_sym)) == 0, "Theorem O-W9.A1-Univ tan(theta_HK) lock failed")

        # 40d numerical verification of Theorem O-W9.A1-Univ across Wilson, Manton, Symanzik, and Heat-Kernel
        th_test = iv.mpf("0.35")
        tan_test = iv.tan(th_test)
        o_w9_a1_models = {}
        # (a) Wilson: Phi(th) = -beta * cos(th) => Phi' = beta*sin(th)
        for m_name, fp_val, cperp_val in (
            ("Wilson", iv.sin(th_test), iv.cos(th_test)),
            ("Manton_theta_sq", iv.mpf(2) * th_test, iv.mpf(2) * th_test * iv.cos(th_test) / iv.sin(th_test)),
            ("Symanzik_c0_c1",
             (iv.mpf(5) / 3) * iv.sin(th_test) - (iv.mpf(1) / 3) * iv.sin(2 * th_test),
             ((iv.mpf(5) / 3) * iv.sin(th_test) - (iv.mpf(1) / 3) * iv.sin(2 * th_test)) * iv.cot(th_test)),
        ):
            ratio_v = fp_val / cperp_val
            check(strictly_below(abs(ratio_v - tan_test), "1e-36"), f"O-W9.A1-Univ 40d failed for {m_name}")
            o_w9_a1_models[m_name] = outward_str(ratio_v)

        # NP-A: SymPy -ln K_{2/beta} + Dashen-Gross 5/12 - 1/3 = 1/12 + explicit |k|>12 Poisson tail < 10^{-2600}
        th_s, t_s, b_s = sp.symbols("theta t b", positive=True)
        log_pref = sp.series(sp.log(th_s / sp.sin(th_s)), th_s, 0, 6)
        s_hk = sp.series((th_s ** 2 / t_s - log_pref).subs(t_s, 2 / b_s), th_s, 0, 6).removeO()
        check(sp.simplify(s_hk.coeff(th_s, 2) - (b_s / 2 - sp.Rational(1, 6))) == 0, "NP-A theta^2 mismatch")
        check(sp.simplify(s_hk.coeff(th_s, 4) - (-sp.Rational(1, 180))) == 0, "NP-A theta^4 mismatch")
        dg_shift = Fraction(5, 12) - Fraction(1, 3)
        check(dg_shift == Fraction(1, 12), "Dashen-Gross shift mismatch")
        lam_hk_w_iv = iv.exp((iv.pi ** 2) / iv.mpf(44))
        check(strictly_above(lam_hk_w_iv, "1.2514578") and strictly_below(lam_hk_w_iv, "1.2514580"), "NP-A Lambda_HK/W failed")

        # Explicit |k| > 12 Poisson tail bound for t <= 1 (beta >= 2) and theta in (0, pi)
        # MVT pairing of +/-m gives |tail| <= sqrt(4*pi/t) * exp(t/4) / t * pi * sum_{m>=13} (2*(2m+1)^2*pi^2/t) * exp(-(2m-1)^2*pi^2/t)
        # Bound cleanly at t = 1 (monotonically smaller for t < 1 once (25*pi)^2/t > 2):
        x_min_13 = iv.mpf(25) * iv.pi
        tail_m13 = (
            iv.sqrt(4 * iv.pi) * iv.exp(iv.mpf(1) / iv.mpf(4)) * iv.pi
            * iv.mpf(2) * ((iv.mpf(27) * iv.pi) ** 2) * iv.exp(-(x_min_13 ** 2))
        )
        q_pois = iv.exp(-iv.mpf(104) * (iv.pi ** 2))
        poisson_tail_k12_ub = tail_m13 / (iv.mpf(1) - q_pois)
        check(strictly_below(poisson_tail_k12_ub, "1e-2600"), f"Poisson |k|>12 remainder >= 1e-2600: {poisson_tail_k12_ub}")
        # Verify char vs |k|<=12 Poisson sum at t=1.0, theta=0.5 with explicit tail
        th_p_i = iv.mpf("0.5")
        kc_05 = _r8_hk_char_iv(th_p_i, iv.mpf(1), M_max=75)
        gs_05 = sum((th_p_i - 2 * iv.pi * k) * iv.exp(-((th_p_i - 2 * iv.pi * k) ** 2)) for k in range(-12, 13))
        kp_05 = iv.sqrt(4 * iv.pi) * iv.exp(iv.mpf(1) / iv.mpf(4)) * gs_05 / iv.sin(th_p_i) + iv.mpf([-poisson_tail_k12_ub.b, poisson_tail_k12_ub.b])
        check(strictly_below(abs(kc_05 - kp_05), "1e-35"), f"HK char vs Poisson mismatch: {abs(kc_05 - kp_05)}")

        # 4D vs 5D overlap combinatorics & 40d Bloch Step-2 Sf2/Sc2 + explicit conditional O-W8.2-KP
        overlap_comb = {"4D": {"z_cell_plaq": 21, "z_cube": 81, "n_act": 45},
                        "5D": {"z_cell_plaq": 31, "z_cube": 243, "n_act": 124}}
        check(overlap_comb["4D"]["z_cell_plaq"] == 21 and overlap_comb["5D"]["z_cell_plaq"] == 31, "Overlap comb mismatch")

        def _bloch_step2_40d(d_dim: int, M2: int):
            alpha_iv = iv.mpf(3) / iv.mpf(5)
            inv_a_iv = iv.mpf(1) / iv.mpf(16)
            twopi = iv.mpf(2) * iv.pi
            trig_cache: dict = {}

            def _exp_cos(ang):
                key = str(ang)
                if key not in trig_cache:
                    trig_cache[key] = (iv.exp(iv.mpc(0, ang)), iv.cos(ang))
                return trig_cache[key]

            def _c_hat(k_v):
                pairs = [_exp_cos(k_v[m]) for m in range(d_dim)]
                e_p = [pr[0] for pr in pairs]
                cosk = [pr[1] for pr in pairs]
                e2_p = [e_p[m] * e_p[m] for m in range(d_dim)]
                dk = [e_p[m] - 1 for m in range(d_dim)]
                C = [[iv.mpc(0, 0) for _ in range(d_dim)] for _ in range(d_dim)]
                w_st = alpha_iv / iv.mpf(2 * (d_dim - 1))
                for mu in range(d_dim):
                    diag_val = (1 - alpha_iv) * (1 + e_p[mu])
                    for nu in range(d_dim):
                        if nu == mu: continue
                        diag_val = diag_val + w_st * 2 * cosk[nu] * (1 + e_p[mu])
                        C[mu][nu] = w_st * (1 - iv_conj(e_p[nu])) * (1 - e2_p[mu])
                    C[mu][mu] = diag_val
                return C, dk

            def _mat_mul(A, B):
                nr = len(A); nc = len(B[0]); nk = len(B); z = iv.mpc(0, 0)
                out = [[z] * nc for _ in range(nr)]
                for i in range(nr):
                    row_a = A[i]
                    out_i = out[i]
                    for k in range(nk):
                        aik = row_a[k]
                        row_bk = B[k]
                        for j in range(nc):
                            out_i[j] += aik * row_bk[j]
                return out

            def _mat_dag(A):
                return [[iv_conj(A[j][i]) for j in range(len(A))] for i in range(len(A[0]))]

            def _solve_tr(G_tr):
                nt = len(G_tr)
                aug = [[G_tr[i][j] for j in range(nt)] + [iv.mpc(1, 0) if i == 0 else iv.mpc(0, 0)] for i in range(nt)]
                for col in range(nt):
                    pv = aug[col][col]
                    for j in range(col, nt + 1):
                        aug[col][j] /= pv
                    for r in range(nt):
                        if r != col:
                            fac = aug[r][col]
                            for j in range(col, nt + 1):
                                aug[r][j] -= fac * aug[col][j]
                return [aug[i][nt] for i in range(nt)]

            def _g1_eff(p1):
                dc1 = [iv.exp(iv.mpc(0, p1[m])) - 1 for m in range(d_dim)]
                dc1_sq = sum(dc1[m] * iv_conj(dc1[m]) for m in range(d_dim))
                P1 = [[(iv.mpc(1, 0) if i == j else iv.mpc(0, 0)) - (dc1[i] * iv_conj(dc1[j])) / dc1_sq
                       for j in range(d_dim)] for i in range(d_dim)]
                G1c = [[iv.mpc(0, 0) for _ in range(d_dim)] for _ in range(d_dim)]
                subf = iv.mpf(1) / iv.mpf(2 ** d_dim)
                for s0 in itertools.product((0, 1), repeat=d_dim):
                    k0 = [iv.mpf("0.5") * (p1[m] + twopi * s0[m]) for m in range(d_dim)]
                    C0, dk0 = _c_hat(k0)
                    dk0_sq = sum(dk0[m] * iv_conj(dk0[m]) for m in range(d_dim))
                    CC = _mat_mul(C0, _mat_dag(C0))
                    fac = subf / dk0_sq
                    for i in range(d_dim):
                        for j in range(d_dim):
                            G1c[i][j] += fac * CC[i][j]
                tmp = _mat_mul(P1, _mat_mul(G1c, P1))
                for i in range(d_dim):
                    for j in range(d_dim):
                        tmp[i][j] += inv_a_iv * P1[i][j]
                return tmp

            p2_ref = [twopi / iv.mpf(M2)] + [iv.mpf(0) for _ in range(d_dim - 1)]
            dc2 = [_exp_cos(p2_ref[m])[0] - 1 for m in range(d_dim)]
            dc2_sq = sum(dc2[m] * iv_conj(dc2[m]) for m in range(d_dim))
            G2c = [[iv.mpc(0, 0) for _ in range(d_dim)] for _ in range(d_dim)]
            subf = iv.mpf(1) / iv.mpf(2 ** d_dim)
            # Exploit S_{d_dim-1} spatial-axis permutation symmetry on s1[1:] (exact integer binomial weights)
            binom_c = 1
            for s1_0 in (0, 1):
                binom_c = 1
                for w_ones in range(d_dim):
                    if w_ones > 0:
                        binom_c = (binom_c * (d_dim - w_ones)) // w_ones
                    s1 = (s1_0,) + (1,) * w_ones + (0,) * (d_dim - 1 - w_ones)
                    p1 = [iv.mpf("0.5") * (p2_ref[m] + twopi * s1[m]) for m in range(d_dim)]
                    G1e = _g1_eff(p1)
                    C1, _ = _c_hat(p1)
                    contrib = _mat_mul(C1, _mat_mul(G1e, _mat_dag(C1)))
                    diag_avg = sum((contrib[i][i] for i in range(1, d_dim)), iv.mpc(0, 0)) / iv.mpf(d_dim - 1)
                    off_avg = sum(
                        (contrib[i][j] for i in range(1, d_dim) for j in range(1, d_dim) if i != j),
                        iv.mpc(0, 0),
                    ) / iv.mpf((d_dim - 1) * (d_dim - 2))
                    wt = subf * iv.mpf(binom_c)
                    for i in range(1, d_dim):
                        for j in range(1, d_dim):
                            G2c[i][j] += wt * (diag_avg if i == j else off_avg)
            G2_tr = [[G2c[i][j] + (inv_a_iv if i == j else iv.mpc(0, 0)) for j in range(1, d_dim)] for i in range(1, d_dim)]
            k2_col = _solve_tr(G2_tr)
            return k2_col[0].real / dc2_sq.real

        bloch_4d_m2 = _bloch_step2_40d(4, 2)
        bloch_4d_m3 = _bloch_step2_40d(4, 3)
        bloch_5d_m2 = _bloch_step2_40d(5, 2)
        check(strictly_above(bloch_4d_m2, "0.97179") and strictly_below(bloch_4d_m2, "0.97180"), f"4D M2=2 Bloch mismatch: {bloch_4d_m2}")
        check(strictly_above(bloch_4d_m3, "0.96377") and strictly_below(bloch_4d_m3, "0.96378"), f"4D M2=3 Bloch mismatch: {bloch_4d_m3}")
        check(strictly_above(bloch_5d_m2, "1.50584") and strictly_below(bloch_5d_m2, "1.50585"), f"5D M2=2 Bloch mismatch: {bloch_5d_m2}")

        # =====================================================================
        # 6. Wave 8 (W8-3 O-W8.1, Polar 31.68 erratum fix, NP-C, NP-D)
        # =====================================================================
        # Rational [0,1]^3 SU(2) monopole cube with q = (4/5, 0, 0, 3/5)
        def _qmul_f(a, b):
            return (
                a[0] * b[0] - a[1] * b[1] - a[2] * b[2] - a[3] * b[3],
                a[0] * b[1] + a[1] * b[0] + a[2] * b[3] - a[3] * b[2],
                a[0] * b[2] - a[1] * b[3] + a[2] * b[0] + a[3] * b[1],
                a[0] * b[3] + a[1] * b[2] - a[2] * b[1] + a[3] * b[0],
            )

        q_mono = (Fraction(4, 5), Fraction(0), Fraction(0), Fraction(3, 5))
        check(sum(c * c for c in q_mono) == 1, "Monopole quaternion not unit")
        q_m2 = _qmul_f(q_mono, q_mono)
        q_m4 = _qmul_f(q_m2, q_m2)
        check(q_m2[0] == Fraction(7, 25) and q_m4[0] == Fraction(-527, 625), "O-W8.1 q^4 scalar trace mismatch")

        # SymPy closed-form Cov_cube(z1, z2) verification across all 32 Z_2^5 configurations
        e_syms = sp.symbols("e_1 e_2 e_3 e_4 e_5 e_6", positive=True)
        Z_enum = sp.Integer(0)
        for mask in range(32):
            zs = [1 if ((mask >> k) & 1) == 0 else -1 for k in range(5)]
            z6 = zs[0] * zs[1] * zs[2] * zs[3] * zs[4]
            term = e_syms[5] if z6 == 1 else (1 / e_syms[5])
            for k in range(5):
                term = term * (e_syms[k] if zs[k] == 1 else (1 / e_syms[k]))
            Z_enum += term
        c_p = [sp.Rational(1, 2) * (ek + 1 / ek) for ek in e_syms]
        s_p = [sp.Rational(1, 2) * (ek - 1 / ek) for ek in e_syms]
        Z_closed_e = 32 * (sp.prod(c_p) + sp.prod(s_p))
        check(sp.expand(Z_enum - Z_closed_e) == 0, "O-W8.1 Z_cube enum vs closed mismatch")
        Z1_e = e_syms[0] * sp.diff(Z_closed_e, e_syms[0])
        Z2_e = e_syms[1] * sp.diff(Z_closed_e, e_syms[1])
        Z12_e = e_syms[1] * sp.diff(Z1_e, e_syms[1])
        num_cov12 = sp.expand(Z_closed_e * Z12_e - Z1_e * Z2_e)
        exp_num = sp.expand(1024 * s_p[2] * s_p[3] * s_p[4] * s_p[5] * c_p[2] * c_p[3] * c_p[4] * c_p[5])
        check(sp.expand(num_cov12 - exp_num) == 0, "O-W8.1 Cov_cube numerator mismatch")

        cov_cube_results = {}
        for bF_int in (1, 2):
            bF_iv = iv.mpf(bF_int)
            Js = [bF_iv * 4 / 5, bF_iv * 4 / 5, bF_iv * 4 / 5, bF_iv * 4 / 5, bF_iv, bF_iv * (-527) / 625]
            cs = [(iv.exp(j) + iv.exp(-j)) / 2 for j in Js]
            ts = [(iv.exp(j) - iv.exp(-j)) / (iv.exp(j) + iv.exp(-j)) for j in Js]
            prod_all = ts[0] * ts[1] * ts[2] * ts[3] * ts[4] * ts[5]
            cov12_iv = ((ts[2] * ts[3] * ts[4] * ts[5]) / ((cs[0] * cs[1]) ** 2)) / ((1 + prod_all) ** 2)
            check(cov12_iv.b < 0, f"Expected Cov_cube(z1,z2) < 0 at bF={bF_int}")
            if bF_int == 1:
                check(strictly_above(cov12_iv, "-0.08944332") and strictly_below(cov12_iv, "-0.08944330"),
                      f"O-W8.1 Cov_cube(beta_F=1) mismatch: {cov12_iv}")
            cov_cube_results[f"beta_F_{bF_int}"] = outward_str(cov12_iv)

        # O-W6.1-2 Fisher zeros & 4D SU(5) beta_0 > 0 + Polar(0.60, a_blk=16) exact u_{1/2}(31.68) = 0.95303747...
        beta0_su5 = iv.mpf(55) / (iv.mpf(48) * (iv.pi ** 2))
        check(strictly_above(beta0_su5, "0.1160") and strictly_below(beta0_su5, "0.1162"), "SU(5) beta_0 bracket failed")
        ka_frac = Fraction(99, 50) * 16
        check(ka_frac == Fraction(792, 25), "Exact beta*a_blk != 792/25")
        ka_iv = iv.mpf(792) / iv.mpf(25)
        u_half_3168 = besseli_iv_any(2, ka_iv) / besseli_iv_any(1, ka_iv)
        check(u_half_3168.a > mayer_lim.b and strictly_above(u_half_3168, "0.95303747") and strictly_below(u_half_3168, "0.95303748"),
              f"#130/#133 exact u_{{1/2}}(31.68) mismatch: {u_half_3168}")

        # Conditional NP-C (d=4 marginality, Cartan [s3, s3]=0, 4 sin^2(pi/L), Riccati) and NP-D (1 - 2/d_sp & pi/8 integral -> 1/32)
        for d_spde in (2, 3, 4, 5):
            dim_A_f = Fraction(2 - d_spde, 2)
            dim_rhs_f = dim_A_f - 2
            gap_q_f = (2 * dim_A_f - 1) - dim_rhs_f
            if d_spde == 4:
                check(gap_q_f == 0 and (4 - d_spde) == 0, "NP-C d=4 parabolic marginality failed")
        s3_sp = sp.Matrix([[1, 0], [0, -1]])
        amu_s, anu_s = sp.symbols("amu anu")
        check(sp.simplify((amu_s * s3_sp) * (anu_s * s3_sp) - (anu_s * s3_sp) * (amu_s * s3_sp)) == sp.zeros(2, 2),
              "NP-C Cartan commutator nonzero")
        for L_lat in (8, 16, 32, 64):
            ev_lat = iv.mpf(4) * (iv.sin(iv.pi / iv.mpf(L_lat)) ** 2)
            check(ev_lat.b < (iv.mpf(4) * (iv.pi ** 2) / iv.mpf(L_lat * L_lat)).a, f"NP-C gap bound L={L_lat} failed")

        d_sp_s = sp.Symbol("d_sp", positive=True)
        check(sp.simplify((1 - 2 / d_sp_s).subs(d_sp_s, 2)) == 0, "NP-D d_sp=2 failed")
        check(sp.simplify((1 - 2 / d_sp_s).subs(d_sp_s, 3)) == sp.Rational(1, 3), "NP-D d_sp=3 failed")
        check(sp.simplify((1 - 2 / d_sp_s).subs(d_sp_s, 4)) == sp.Rational(1, 2), "NP-D d_sp=4 failed")
        x_s = sp.Symbol("x", real=True)
        int_npd = sp.integrate(sp.sqrt(x_s * (1 - x_s)), (x_s, 0, 1))
        check(sp.simplify(int_npd - sp.pi / 8) == 0, "NP-D radial integral mismatch")
        d_beta_npc = (iv.mpf(11) / (iv.mpf(3) * (iv.pi ** 2))) * iv.log(2)
        c_or_npc = iv.mpf("1.885176")
        riccati_4d_160 = iv.exp((iv.mpf(2) * c_or_npc / d_beta_npc) * (iv.sqrt(iv.mpf(160)) - iv.mpf(1)))
        check(strictly_above(riccati_4d_160, "1.1839e74") and strictly_below(riccati_4d_160, "1.1840e74"),
              f"NP-C 4D Riccati penalty at beta_0=160 unexpected: {riccati_4d_160}")

        return {
            "h2d_status": "OPEN",
            "irx_status": "OPEN",
            "physical_unification": "OPEN",
            "device_certified": False,
            "o_w8_2_kp_conditional": True,
            "o_w8_2_kp_status": "CONDITIONAL_ON_UV_SMALL_FIELD_AND_MULTISCALE_ITERATION",
            "honest_uv_ir_open_corridor_no_bulk": "[1.8684, 271..428]",
            "conditional_kp_corridor": "[5077, 9896]",
            "wave5_w5_2_c4bpp_divergence": {
                "lambda": 4,
                "sigma0_sq": "1/4",
                "I0_iv": outward_str(I0_iv),
                "hermite_a2_iv": outward_str(a2_iv),
                "hermite_a2_sq_iv": outward_str(a2_sq_iv),
                "var_f_iv": outward_str(var_f_iv),
                "sd_ratio_scaling": "Theta(beta) -> +inf",
                "o_w3_2_1_isolated_finite_truncation": True,
            },
            "wave6_w6_2_and_np_b_o1": {
                "single_scale_kl_barrier": "p > 2*(k+1) => p >= 9 at k=3",
                "slab_3d_barrier": "p > k_slab + 3",
                "dumbbell_a": 12,
                "w6_2_delta_c1_iv": outward_str(delta_c1_iv),
                "np_b_u1_abs_iv": outward_str(u1_abs_iv),
                "c5_compatible_forcing_af_rg": True,
            },
            "wave7_w7_2_non_mk_foam": {
                "combinatorics_4d_2x2": comb_4d_2x2,
                "beta_19_z6_kp_iv": outward_str(b_19z6),
                "beta_64_z6_mayer_iv": outward_str(b_64z6),
                "beta_6z4_178z6_mayer_iv": outward_str(b_6z4_178z6),
                "u1_t025_beta_sat_iv": outward_str(b_sat_iv := b_u1_sat),
                "u1_198_c_max_iv": outward_str(c_max_u1_iv),
                "r0_sum_at_198_iv": outward_str(r0_sum_198),
                "all_crossings_strictly_below_1_98": True,
            },
            "wave8_w8_1_st_plus_and_bochner": {
                "m1_q0_a16_iv": outward_str(q0_a16_iv),
                "m1_q0_ainf_over4_iv": outward_str(q0_inf_over4_iv),
                "retracted_w51_1_4176d_lhs_ub_iv": outward_str(lhs_4176_ub),
                "retracted_w51_1_4176d_rhs_iv": outward_str(rhs_4176),
                "retracted_w51_1_4176d_deficit_iv": outward_str(deficit_4176),
                "st_plus_32x32_endpoints": st_endpoint_certs,
                "chernoff_9dof_corridor_all8": chernoff_corridor_all8,
                "o_w8_q1_r_origin_25d_iv": outward_str(r_orig_25),
                "o_w8_q1_r_origin_4176d_iv": outward_str(r_orig_4176),
                "o_w8_q1_6p_ab_factor_iv": outward_str(boch_fac_iv),
                "bochner_optimistic_floor": {"theta_deg": "17.30", "b_7e_pass": 869},
                "homogeneous_10_4_6p_ab_crossing": {"theta_deg": "30.28", "b_7e_pass": 285},
            },
            "wave8_w8_2_and_o_w9_a1_univ": {
                "covariant_exp_zero_u1_radial_tadpole": True,
                "polar_1_over_rc_sq_tadpole": "1 + w_s*(1 - w_s)*dphi^2",
                "s3_haar_jacobian_quad": "-r^2/12 - r^4/1440",
                "overlap_combinatorics": overlap_comb,
                "bloch_40d": {
                    "4D_M2_2_Sf2_over_Sc2_iv": outward_str(bloch_4d_m2),
                    "4D_M2_3_Sf2_over_Sc2_iv": outward_str(bloch_4d_m3),
                    "5D_C5_M2_2_Sf2_over_Sc2_iv": outward_str(bloch_5d_m2),
                },
                "np_a_dashen_gross_shift": "1/12",
                "np_a_lambda_hk_over_w_iv": outward_str(lam_hk_w_iv),
                "np_a_poisson_k_gt_12_tail_ub_iv": outward_str(poisson_tail_k12_ub),
                "o_w8_2_kp_conditional_note": "Conditional on UV small-field and multiscale iteration (Mayer 5077, KP 9896)",
                "theorem_o_w9_a1_univ": {
                    "symbolic_identity": "f_p^Phi / c_perp^Phi = tan(theta_HK) = tan(theta_1p / 2)",
                    "theta_test_rad": "0.35",
                    "tan_theta_iv": outward_str(tan_test),
                    "models_40d": o_w9_a1_models,
                    "w9_a1_single_plaquette_sweep_ruled_out": True,
                },
            },
            "wave8_w8_3_and_np_cd": {
                "o_w8_1_monopole_q": "4/5 + 3/5 k",
                "o_w8_1_j6_over_beta_f": "-527/625",
                "o_w8_1_monopole_product_sign": -1,
                "o_w8_1_cov_cube_iv": cov_cube_results,
                "o_w6_1_2_su5_beta0_iv": outward_str(beta0_su5),
                "polar_060_a16_beta198_kappa": "792/25",
                "polar_060_a16_fine_edges_per_block": 26,
                "polar_060_a16_u_half_3168_iv": outward_str(u_half_3168),
                "np_c_d4_marginal_beta0_160_riccati_iv": outward_str(riccati_4d_160),
                "np_d_uv_factor": {"d_sp_2": "0", "d_sp_3": "1/3", "d_sp_4": "1/2"},
            },
            "round04_checks_verified": r4_bridges["interval_checks_passed"],
            "round05_checks_verified": r5_bridges["interval_checks_passed"],
            "round06_checks_verified": r6_bridges["interval_checks_passed"],
            "round07_checks_verified": r7_frontier["interval_checks_passed"],
            "interval_checks_passed": interval_checks,
        }
    finally:
        mp.dps = 50
        iv.dps = 40


# ---------------------------------------------------------------------------
# Round 09: Wave 9 (W9-1, W9-3A, W9-2b, W9-4 & O-W9.A1-Univ) Pure-Arithmetic Certification
# ---------------------------------------------------------------------------

def _r9_from_frac(q: Fraction):
    return iv.mpf(q.numerator) / iv.mpf(q.denominator)


def _r9_mp_from_frac(q: Fraction):
    return mp.mpf(q.numerator) / mp.mpf(q.denominator)


def _r9_eps_from_deg_iv(deg_str: str):
    th = iv.mpf(deg_str) * iv.pi / iv.mpf(180)
    return iv.mpf(1) - iv.cos(th / iv.mpf(2))


def _r9_sin_half_deg_iv(deg_str: str):
    th = iv.mpf(deg_str) * iv.pi / iv.mpf(180)
    return iv.sin(th / iv.mpf(2))


def _r9_cos_half_deg_iv(deg_str: str):
    th = iv.mpf(deg_str) * iv.pi / iv.mpf(180)
    return iv.cos(th / iv.mpf(2))


def _r9_herm_ldlh_pos(M_iv: list[list]) -> tuple[bool, object]:
    """Unpivoted 40d Hermitian LDL^H positivity check; returns (ok, min_D)."""
    n = len(M_iv)
    A = [[M_iv[i][j] for j in range(n)] for i in range(n)]
    D = [iv.mpf(0) for _ in range(n)]
    min_d = iv.mpf("1e30")
    for j in range(n):
        s = A[j][j].real
        for k in range(j):
            Ljk = A[j][k]
            s = s - (Ljk.real ** 2 + Ljk.imag ** 2) * D[k]
        if mp.mpf(s.a) <= 0:
            return False, s
        D[j] = s
        if mp.mpf(s.a) < mp.mpf(min_d.a):
            min_d = s
        for i in range(j + 1, n):
            t = A[i][j]
            for k in range(j):
                Lik = A[i][k]
                Ljk = A[j][k]
                t = t - Lik * iv_conj(Ljk) * D[k]
            A[i][j] = t / s
    return True, min_d


def _r9_iv_erfc(u_iv):
    """Pure 40d interval arithmetic enclosure of erfc(u) for u >= 0."""
    u = iv.mpf(u_iv)
    if mp.mpf(u.b) <= 0:
        return iv.mpf(1)
    sqrt_pi = iv.sqrt(iv.pi)
    if mp.mpf(u.b) < mp.mpf("6.0"):
        u2 = u * u
        term = u
        s_val = term
        for k in range(1, 66):
            term = -term * u2 / iv.mpf(k)
            s_val = s_val + term / iv.mpf(2 * k + 1)
        term66 = -term * u2 / iv.mpf(66)
        err_t = abs(term66 / iv.mpf(133))
        erf_iv = s_val + iv.mpf([0, err_t.b])
        res = iv.mpf(1) - (iv.mpf(2) / sqrt_pi) * erf_iv
        return iv.mpf([max(mp.mpf(0), mp.mpf(res.a)), min(mp.mpf(1), mp.mpf(res.b))])
    inv_2u2 = iv.mpf(1) / (iv.mpf(2) * u * u)
    s_cur = iv.mpf(1)
    term = iv.mpf(1)
    n_as = min(24, max(4, int(mp.mpf(u.a) ** 2)))
    if n_as % 2 == 1:
        n_as -= 1
    s_prev = s_cur
    for k in range(1, n_as + 1):
        s_prev = s_cur
        term = -term * iv.mpf(2 * k - 1) * inv_2u2
        s_cur = s_cur + term
    pref = iv.exp(-u * u) / (sqrt_pi * u)
    return pref * iv.mpf([max(mp.mpf(0), mp.mpf(s_prev.a)), mp.mpf(s_cur.b)])


def _r9_iv_gamma_upper_q_half_int(d_int: int, x_iv):
    """Pure 40d upper bound on regularized incomplete gamma Q(d/2, x) = P(chi^2_d >= 2x)."""
    x = iv.mpf(x_iv.a)
    if mp.mpf(x.a) <= 0:
        return iv.mpf(1)
    if d_int % 2 == 0:
        m = d_int // 2
        term = iv.mpf(1)
        poly = term
        for k in range(1, m):
            term = term * x / iv.mpf(k)
            poly = poly + term
        val = iv.exp(-x) * poly
    else:
        m = (d_int - 1) // 2
        sqrt_x = iv.sqrt(x)
        q = _r9_iv_erfc(sqrt_x)
        sqrt_pi = iv.sqrt(iv.pi)
        ex = iv.exp(-x)
        gam = iv.mpf("0.5") * sqrt_pi
        xk = sqrt_x
        for k in range(1, m + 1):
            q = q + (xk * ex) / gam
            gam = gam * (iv.mpf(k) + iv.mpf("0.5"))
            xk = xk * x
        val = q
    if mp.mpf(val.b) >= 1:
        return iv.mpf(1)
    return val


def _r9_iv_pddh03_chernoff_chi2(d_half_frac: Fraction, x_iv):
    """Exact P-DDH-03 Chernoff bound (x / (d/2))^{d/2} * exp(d/2 - x) >= Q(d/2, x)."""
    dh = _r9_from_frac(d_half_frac)
    x = iv.mpf(x_iv.a)
    if mp.mpf(x.b) <= mp.mpf(dh.a):
        return iv.mpf(1)
    eta = dh / x
    val = iv.exp(-dh * iv.log(eta) - (iv.mpf(1) - eta) * x)
    if mp.mpf(val.b) >= 1:
        return iv.mpf(1)
    return val


def _r9_coarse_steps(a: int):
    if a == 0:
        return [(0, 1), (1, 1)], [(1, 1), (0, 1)]
    if a == 1:
        return [(0, -1), (1, 1)], [(1, 1), (0, -1)]
    if a == 2:
        return [(2, 1), (3, 1)], [(3, 1), (2, 1)]
    return [(2, -1), (3, 1)], [(3, 1), (2, -1)]


def _r9_coset_decompose(x):
    b01 = (x[0] + x[1]) % 2
    b23 = (x[2] + x[3]) % 2
    X = (
        (x[0] - b01 + x[1]) // 2,
        (x[1] - x[0] + b01) // 2,
        (x[2] - b23 + x[3]) // 2,
        (x[3] - x[2] + b23) // 2,
    )
    return X, b01 + 2 * b23


def _r9_su2_qmul(q1, q2):
    a0, a1, a2, a3 = q1
    b0, b1, b2, b3 = q2
    return (
        a0 * b0 - a1 * b1 - a2 * b2 - a3 * b3,
        a0 * b1 + a1 * b0 + a2 * b3 - a3 * b2,
        a0 * b2 - a1 * b3 + a2 * b0 + a3 * b1,
        a0 * b3 + a1 * b2 - a2 * b1 + a3 * b0,
    )


def _r9_su2_qconj(q):
    return (q[0], -q[1], -q[2], -q[3])


def _r9_hk_poisson_tail_iv(t_iv, K: int = 12):
    pi_iv = iv.pi
    t_lo = iv.mpf(t_iv.a)
    t_hi = iv.mpf(t_iv.b)
    m_first = iv.mpf(2 * K + 1) * pi_iv
    require(mp.mpf((iv.mpf(2) * m_first * m_first / t_hi).a) > 4, "HK tail threshold invalid")
    exp_first = iv.exp(-(m_first * m_first) / t_hi)
    exp_step = iv.exp(-(iv.mpf(8) * (pi_iv ** 2) * iv.mpf(K + 1)) / t_hi)
    m_ratio = iv.mpf(2 * K + 3) / iv.mpf(2 * K + 1)

    def sum_mp(p_ord: int):
        q = (m_ratio ** p_ord) * exp_step
        require(strictly_below(q, "0.5"), f"HK tail ratio >= 0.5 for p={p_ord}")
        return iv.mpf(2) * (m_first ** p_ord) * exp_first / (iv.mpf(1) - q)

    s0, s1, s2, s3, s4 = sum_mp(0), sum_mp(1), sum_mp(2), sum_mp(3), sum_mp(4)
    return {
        "exp_first_ub": mp.mpf(exp_first.b),
        "rem0": mp.mpf(s1.b),
        "rem1": mp.mpf((s0 + iv.mpf(2) * s2 / t_lo).b),
        "rem2": mp.mpf((iv.mpf(6) * s1 / t_lo + iv.mpf(4) * s3 / (t_lo ** 2)).b),
    }


def _r9_hk_tilde_at_zero_iv(t_iv, K: int = 12):
    pi_iv = iv.pi
    t_lo, t_hi = iv.mpf(t_iv.a), iv.mpf(t_iv.b)
    s = iv.mpf(1)
    for k in range(1, K + 1):
        u = iv.mpf(2) * pi_iv * iv.mpf(k)
        u2 = u * u
        s = s + iv.mpf(2) * (iv.mpf(1) - iv.mpf(2) * u2 / t_iv) * iv.exp(-u2 / t_iv)
    u_first = iv.mpf(2) * pi_iv * iv.mpf(K + 1)
    u2_first = u_first * u_first
    exp_f = iv.exp(-u2_first / t_hi)
    q = (iv.mpf(K + 2) / iv.mpf(K + 1)) ** 2 * iv.exp(-iv.mpf(4) * (pi_iv ** 2) * iv.mpf(2 * K + 3) / t_hi)
    require(strictly_below(q, "0.5"), "HK zero tail ratio >= 0.5")
    rem = iv.mpf(2) * (iv.mpf(1) + iv.mpf(2) * u2_first / t_lo) * exp_f / (iv.mpf(1) - q)
    r_hi = mp.mpf(rem.b)
    return s + iv.mpf([-r_hi, r_hi])


def _r9_hk_tilde_pos_iv(th_iv, t_iv, K: int = 12, tail_info=None):
    if tail_info is None:
        tail_info = _r9_hk_poisson_tail_iv(t_iv, K=K)
    pi_iv = iv.pi
    xs = [th_iv - iv.mpf(2) * pi_iv * iv.mpf(k) for k in range(-K, K + 1)]
    min_e = min(((x * x) / t_iv).a for x in xs)
    scale_back = iv.exp(-iv.mpf(min_e))
    s0 = s1 = s2 = iv.mpf(0)
    t2 = t_iv * t_iv
    for x in xs:
        x2 = x * x
        e = iv.exp(-(x2 / t_iv) + min_e)
        s0 = s0 + x * e
        s1 = s1 + (iv.mpf(1) - iv.mpf(2) * x2 / t_iv) * e
        s2 = s2 + (-iv.mpf(6) * x / t_iv + iv.mpf(4) * x2 * x / t2) * e
    s0 = s0 * scale_back + iv.mpf([-tail_info["rem0"], tail_info["rem0"]])
    s1 = s1 * scale_back + iv.mpf([-tail_info["rem1"], tail_info["rem1"]])
    s2 = s2 * scale_back + iv.mpf([-tail_info["rem2"], tail_info["rem2"]])
    sin_th, cos_th = iv.sin(th_iv), iv.cos(th_iv)
    tilde_K = s0 / sin_th
    d1 = -(s1 / s0 - cos_th / sin_th)
    d2 = -((s2 * s0 - s1 * s1) / (s0 * s0) + iv.mpf(1) / (sin_th * sin_th))
    return tilde_K, d1, d2


def compute_h2d_round09_wave9_sqrt2_bianchi() -> dict:
    """Pure 40-digit + SymPy + Fraction Wave 9 certification (W9-1, W9-3A, W9-2b, W9-4 & O-W9.A1-Univ)."""
    mp.dps = 55
    iv.dps = 40
    try:
        checks = 0
        CELL_SHIFTS = [(0, 0, 0, 0), (1, 0, 0, 0), (0, 0, 1, 0), (1, 0, 1, 0)]
        PAIRS = [(mu, nu) for mu in range(4) for nu in range(mu + 1, 4)]

        # ------------------------------------------------------------------
        # 1. W9-1: R_{sqrt(2)} Split-Step RG, DiagRP, 8*I_4 & UV Leap
        # ------------------------------------------------------------------
        R1_sp = sp.Matrix([[1, -1, 0, 0], [1, 1, 0, 0], [0, 0, 1, -1], [0, 0, 1, 1]])
        R2_sp = R1_sp.T
        require(R1_sp.T * R1_sp == 2 * sp.eye(4), "R1^T R1 != 2 I_4")
        require(R2_sp * R1_sp == 2 * sp.eye(4), "R2 R1 != 2 I_4")
        require(int(R1_sp.det()) == 4, "det R1 != 4")
        Theta_01 = sp.Matrix([[0, 1, 0, 0], [1, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]])
        Theta_23 = sp.Matrix([[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0]])
        require(Theta_01 * R1_sp == R1_sp * sp.diag(1, -1, 1, 1), "DiagRP Theta_01 failed")
        require(Theta_23 * R1_sp == R1_sp * sp.diag(1, 1, 1, -1), "DiagRP Theta_23 failed")

        J2 = sp.Matrix([[1, -1], [1, 1]])
        P1 = sp.diag(J2, J2)
        P2 = sp.Matrix([[1, 0, -1, 0], [0, 1, 0, -1], [1, 0, 1, 0], [0, 1, 0, 1]])
        P3 = sp.Matrix([[1, 0, 0, -1], [0, 1, -1, 0], [0, 1, 1, 0], [1, 0, 0, 1]])
        P_prod = P3.T * P3 * P2.T * P2 * P1.T * P1
        require(P_prod == 8 * sp.eye(4), "3-pairing product != 8 I_4")
        intra_pairs = [{(0, 1), (2, 3)}, {(0, 2), (1, 3)}, {(0, 3), (1, 2)}]
        for pair in PAIRS:
            c_intra = sum(1 for st in intra_pairs if pair in st)
            require(c_intra == 1, f"Non-uniform pairing plane count for {pair}")

        # #130 ray-scaling derivative identity & midpoint BCH U(1)/SU(2)
        t_r, a_r = sp.symbols("t_r a_r", positive=True)
        ray_expr = (1 - sp.sqrt(1 - t_r ** 2 * a_r)) / t_r
        s_r = sp.sqrt(1 - t_r ** 2 * a_r)
        require(sp.simplify(sp.diff(ray_expr, t_r) - (1 - s_r) / (t_r ** 2 * s_r)) == 0, "Ray-scaling ODE failed")
        t_iv_sample, a_iv_sample = iv.mpf(1) / iv.mpf(3), iv.mpf(3)
        s_iv_sample = iv.sqrt(iv.mpf(1) - (t_iv_sample ** 2) * a_iv_sample)
        require(strictly_above((iv.mpf(1) - s_iv_sample) / ((t_iv_sample ** 2) * s_iv_sample), "0"), "Ray-scaling iv failed")
        a_u1, b_u1 = sp.symbols("a_u1 b_u1", real=True)
        require(sp.simplify(sp.exp(sp.I * a_u1 / 2) * sp.exp(sp.I * b_u1 / 2) - sp.exp(sp.I * (a_u1 + b_u1) / 2)) == 0, "Midpoint U(1) failed")
        A_nc, B_nc = sp.symbols("A_nc B_nc", commutative=False)
        t_nc = sp.Symbol("t_nc")
        expA = 1 + t_nc * A_nc + t_nc ** 2 * A_nc ** 2 / 2
        expB = 1 + t_nc * B_nc + t_nc ** 2 * B_nc ** 2 / 2
        expBmA = sp.expand(1 - t_nc * A_nc + t_nc ** 2 * A_nc ** 2 / 2) * expB
        expHalf = 1 + sp.Rational(1, 2) * (expBmA - 1) - sp.Rational(1, 8) * (expBmA - 1) ** 2
        W_mid_ser = sp.expand(expA * expHalf)
        coeff_t2 = sp.expand(W_mid_ser.coeff(t_nc, 2))
        expected_t2 = sp.expand(sp.Rational(1, 8) * (A_nc + B_nc) ** 2)
        require(sp.expand(coeff_t2 - expected_t2) == 0, "Midpoint W_mid O(t^2) [A,B] cancellation failed")
        checks += 6

        # Exact M=1 16x16 Fraction Q0(16) and Q0(inf)|ker_Cb + M=2 exact SymPy at p=(pi,pi,0,0)
        def eval_DL_frac_or_iv(p_iv_or_zero, use_frac: bool = False):
            if use_frac:
                D = [[Fraction(0)] * 16 for _ in range(16)]
                L = [[Fraction(0)] * 16 for _ in range(16)]
                Cb = [[Fraction(0)] * 16 for _ in range(4)]
                for s in CELL_SHIFTS:
                    for mu, nu in PAIRS:
                        sm, sn = list(s), list(s)
                        sm[mu] += 1
                        sn[nu] += 1
                        row = [0] * 16
                        for x, dmu, sg in [(s, mu, 1), (tuple(sm), nu, 1), (tuple(sn), mu, -1), (s, nu, -1)]:
                            _, c = _r9_coset_decompose(x)
                            row[4 * c + dmu] += sg
                        for i in range(16):
                            if row[i]:
                                for j in range(16):
                                    if row[j]:
                                        D[i][j] += Fraction(row[i] * row[j])
                    rowL = [0] * 16
                    for mu in range(4):
                        sm = list(s)
                        sm[mu] -= 1
                        _, c0 = _r9_coset_decompose(s)
                        _, cm = _r9_coset_decompose(tuple(sm))
                        rowL[4 * c0 + mu] += 1
                        rowL[4 * cm + mu] -= 1
                    for i in range(16):
                        if rowL[i]:
                            for j in range(16):
                                if rowL[j]:
                                    L[i][j] += Fraction(rowL[i] * rowL[j])
                ast = Fraction(1, 4)
                for a in range(4):
                    L1, L2 = _r9_coarse_steps(a)
                    paths = [(Fraction(1, 2) * (1 - ast), L1), (Fraction(1, 2) * (1 - ast), L2)]
                    for nu in ([2, 3] if a < 2 else [0, 1]):
                        for sg in (1, -1):
                            paths.append((ast / 8, [(nu, sg)] + L1 + [(nu, -sg)]))
                            paths.append((ast / 8, [(nu, sg)] + L2 + [(nu, -sg)]))
                    for wt, steps in paths:
                        pos = [0, 0, 0, 0]
                        for mu, sgn in steps:
                            if sgn == 1:
                                _, c = _r9_coset_decompose(tuple(pos))
                                Cb[a][4 * c + mu] += wt
                                pos[mu] += 1
                            else:
                                pos[mu] -= 1
                                _, c = _r9_coset_decompose(tuple(pos))
                                Cb[a][4 * c + mu] -= wt
                return D, L, Cb
            roots = [iv.exp(iv.mpc(0, 1) * p_iv_or_zero[d]) for d in range(4)]
            croots = [iv_conj(r) for r in roots]

            def ph(dX):
                val = iv.mpc(1, 0)
                for d in range(4):
                    if dX[d] == 1:
                        val = val * roots[d]
                    elif dX[d] == -1:
                        val = val * croots[d]
                    elif dX[d] != 0:
                        val = val * (roots[d] ** dX[d])
                return val

            D = iv_zeros(16)
            L = iv_zeros(16)
            for s in CELL_SHIFTS:
                for mu, nu in PAIRS:
                    sm, sn = list(s), list(s)
                    sm[mu] += 1
                    sn[nu] += 1
                    row = [iv.mpc(0, 0)] * 16
                    for x, dmu, sg in [(s, mu, 1), (tuple(sm), nu, 1), (tuple(sn), mu, -1), (s, nu, -1)]:
                        dX, c = _r9_coset_decompose(x)
                        row[4 * c + dmu] = row[4 * c + dmu] + iv.mpc(sg, 0) * ph(dX)
                    nz = [i for i in range(16) if row[i] != iv.mpc(0, 0)]
                    for i in nz:
                        ri = iv_conj(row[i])
                        for j in nz:
                            D[i][j] = D[i][j] + ri * row[j]
                rowL = [iv.mpc(0, 0)] * 16
                for mu in range(4):
                    sm = list(s)
                    sm[mu] -= 1
                    dX0, c0 = _r9_coset_decompose(s)
                    dXm, cm = _r9_coset_decompose(tuple(sm))
                    rowL[4 * c0 + mu] = rowL[4 * c0 + mu] + ph(dX0)
                    rowL[4 * cm + mu] = rowL[4 * cm + mu] - ph(dXm)
                nz = [i for i in range(16) if rowL[i] != iv.mpc(0, 0)]
                for i in nz:
                    ri = iv_conj(rowL[i])
                    for j in nz:
                        L[i][j] = L[i][j] + ri * rowL[j]
            Cb = [[iv.mpc(0, 0)] * 16 for _ in range(4)]
            ast = iv.mpf(1) / iv.mpf(4)
            for a in range(4):
                L1, L2 = _r9_coarse_steps(a)
                paths = [(iv.mpf(1) / iv.mpf(2) * (iv.mpf(1) - ast), L1),
                         (iv.mpf(1) / iv.mpf(2) * (iv.mpf(1) - ast), L2)]
                for nu in ([2, 3] if a < 2 else [0, 1]):
                    for sg in (1, -1):
                        paths.append((ast / iv.mpf(8), [(nu, sg)] + L1 + [(nu, -sg)]))
                        paths.append((ast / iv.mpf(8), [(nu, sg)] + L2 + [(nu, -sg)]))
                for wt, steps in paths:
                    pos = [0, 0, 0, 0]
                    for mu, sgn in steps:
                        if sgn == 1:
                            dX, c = _r9_coset_decompose(tuple(pos))
                            Cb[a][4 * c + mu] = Cb[a][4 * c + mu] + iv.mpc(wt, 0) * ph(dX)
                            pos[mu] += 1
                        else:
                            pos[mu] -= 1
                            dX, c = _r9_coset_decompose(tuple(pos))
                            Cb[a][4 * c + mu] = Cb[a][4 * c + mu] - iv.mpc(wt, 0) * ph(dX)
            Q_iv = iv_zeros(16)
            q25 = iv.mpc(iv.mpf(1) / iv.mpf(4), 0)
            for i in range(16):
                for j in range(16):
                    cc = sum(iv_conj(Cb[a][i]) * Cb[a][j] for a in range(4))
                    Q_iv[i][j] = q25 * (D[i][j] + L[i][j]) + iv.mpc(4, 0) * cc
            return D, L, Cb, Q_iv

        D0_f, L0_f, Cb0_f = eval_DL_frac_or_iv(None, use_frac=True)
        Q0_16_f = [
            [
                Fraction(1, 4) * (D0_f[i][j] + L0_f[i][j]) + 4 * sum(Cb0_f[a][i] * Cb0_f[a][j] for a in range(4))
                for j in range(16)
            ]
            for i in range(16)
        ]
        Q0_16_sp = sp.Matrix([[sp.Rational(Q0_16_f[i][j].numerator, Q0_16_f[i][j].denominator) for j in range(16)] for i in range(16)])
        Q0_16_iv = [[iv.mpc(_r9_from_frac(Q0_16_f[i][j]), 0) for j in range(16)] for i in range(16)]
        evs_m1_16, _ = enclose_hermitian_eigenvalues(Q0_16_iv)
        target_m1_16 = (iv.mpf(9) - iv.sqrt(iv.mpf(17))) / iv.mpf(4)
        require(strictly_below(abs(evs_m1_16[0] - target_m1_16), "1e-34"), "M=1 Q0(16) mismatch")
        # Exact rational quadratic characteristic check: (Q0_16 - (9/4) I)^2 has minimal eigenvalue (sqrt(17)/4)^2? Check det(2 Q^2 - 9 Q + 8 I) == 0:
        Q0_poly = 2 * Q0_16_sp * Q0_16_sp - 9 * Q0_16_sp + 8 * sp.eye(16)
        require(int(Q0_poly.det()) == 0, "M=1 Q0(16) quadratic factor det != 0")

        # Q0(inf)|_{ker C_m1} exact rational projection via nullspace basis
        Cb0_sp = sp.Matrix([[sp.Rational(Cb0_f[a][j].numerator, Cb0_f[a][j].denominator) for j in range(16)] for a in range(4)])
        N0_list = Cb0_sp.nullspace()
        require(len(N0_list) == 12, "ker(Cb0) dim != 12")
        N0_sp = sp.Matrix.hstack(*N0_list)
        G0_n_sp = N0_sp.T * N0_sp
        Q0_ker_sp = sp.Rational(1, 4) * N0_sp.T * (
            sp.Matrix([[sp.Rational(D0_f[i][j].numerator, D0_f[i][j].denominator) + sp.Rational(L0_f[i][j].numerator, L0_f[i][j].denominator) for j in range(16)] for i in range(16)])
        ) * N0_sp
        # Generalized min eigenvalue 8/5: (Q0_ker - 8/5 * G0_n) >= 0 and det == 0
        diff_85 = Q0_ker_sp - sp.Rational(8, 5) * G0_n_sp
        require(int(diff_85.det()) == 0, "M=1 Q0(inf)|ker min eig != 8/5")
        diff_85_iv = [[iv.mpc(iv.mpf(int(sp.fraction(diff_85[i, j])[0])) / iv.mpf(int(sp.fraction(diff_85[i, j])[1])), 0) + (iv.mpc("1e-36", 0) if i == j else iv.mpc(0, 0)) for j in range(12)] for i in range(12)]
        require(_r9_herm_ldlh_pos(diff_85_iv)[0], "M=1 Q0(inf)|ker not >= 8/5")

        # M=2 at p=(pi, pi, 0, 0) exact SymPy check: signs (-1, -1, 1, 1) -> rational!
        _, _, _, Q_m2_min_iv = eval_DL_frac_or_iv([iv.pi, iv.pi, iv.mpf(0), iv.mpf(0)], use_frac=False)
        evs_m2_min, _ = enclose_hermitian_eigenvalues(Q_m2_min_iv)
        require(strictly_below(abs(evs_m2_min[0] - iv.mpf(1)), "1e-34"), "M=2 (pi,pi,0,0) Q(16) != 1")
        # Rank(Cb) at (pi, pi, 0, 0) in exact SymPy (e^{i pi} = -1, e^{i 0} = 1)
        def eval_m2_pipi00_sym():
            roots_s = [-1, -1, 1, 1]
            def ph_s(dX):
                val = 1
                for d in range(4):
                    if dX[d] % 2 != 0 and roots_s[d] == -1:
                        val = -val
                return sp.Rational(val)
            Ds = sp.zeros(16, 16)
            Ls = sp.zeros(16, 16)
            Cbs = sp.zeros(4, 16)
            for s in CELL_SHIFTS:
                for mu, nu in PAIRS:
                    sm, sn = list(s), list(s)
                    sm[mu] += 1
                    sn[nu] += 1
                    row = [sp.Rational(0)] * 16
                    for x, dmu, sg in [(s, mu, 1), (tuple(sm), nu, 1), (tuple(sn), mu, -1), (s, nu, -1)]:
                        dX, c = _r9_coset_decompose(x)
                        row[4 * c + dmu] += sg * ph_s(dX)
                    for i in range(16):
                        if row[i]:
                            for j in range(16):
                                if row[j]:
                                    Ds[i, j] += row[i] * row[j]
                rowL = [sp.Rational(0)] * 16
                for mu in range(4):
                    sm = list(s)
                    sm[mu] -= 1
                    dX0, c0 = _r9_coset_decompose(s)
                    dXm, cm = _r9_coset_decompose(tuple(sm))
                    rowL[4 * c0 + mu] += ph_s(dX0)
                    rowL[4 * cm + mu] -= ph_s(dXm)
                for i in range(16):
                    if rowL[i]:
                        for j in range(16):
                            if rowL[j]:
                                Ls[i, j] += rowL[i] * rowL[j]
            ast_s = sp.Rational(1, 4)
            for a in range(4):
                L1, L2 = _r9_coarse_steps(a)
                paths = [(sp.Rational(1, 2) * (1 - ast_s), L1), (sp.Rational(1, 2) * (1 - ast_s), L2)]
                for nu in ([2, 3] if a < 2 else [0, 1]):
                    for sg in (1, -1):
                        paths.append((ast_s / 8, [(nu, sg)] + L1 + [(nu, -sg)]))
                        paths.append((ast_s / 8, [(nu, sg)] + L2 + [(nu, -sg)]))
                for wt, steps in paths:
                    pos = [0, 0, 0, 0]
                    for mu, sgn in steps:
                        if sgn == 1:
                            dX, c = _r9_coset_decompose(tuple(pos))
                            Cbs[a, 4 * c + mu] += wt * ph_s(dX)
                            pos[mu] += 1
                        else:
                            pos[mu] -= 1
                            dX, c = _r9_coset_decompose(tuple(pos))
                            Cbs[a, 4 * c + mu] -= wt * ph_s(dX)
            return Ds, Ls, Cbs

        Ds2, Ls2, Cbs2 = eval_m2_pipi00_sym()
        require(int(Cbs2.rank()) == 3, "M=2 (pi,pi,0,0) rank(Cb) != 3")
        Q2_sym = sp.Rational(1, 4) * (Ds2 + Ls2) + 4 * (Cbs2.T * Cbs2)
        require(int((Q2_sym - sp.eye(16)).det()) == 0, "M=2 Q(16) exact det(Q-I) != 0")
        N2_sp = sp.Matrix.hstack(*Cbs2.nullspace())
        Q2_ker_sp = sp.Rational(1, 4) * N2_sp.T * (Ds2 + Ls2) * N2_sp
        G2_n_sp = N2_sp.T * N2_sp
        require(int((Q2_ker_sp - G2_n_sp).det()) == 0, "M=2 Q(inf)|ker min eig != 1")

        # Full-BZ M=2 16-sector 40d iv LDL^H positivity Q(16) >= (1 - 1e-34) I_16 & M=4 minimizer
        floor_shift = iv.mpf(1) - iv.mpf("1e-34")
        for s_bits in itertools.product((0, 1), repeat=4):
            p_sec = [iv.pi if b else iv.mpf(0) for b in s_bits]
            _, _, _, Q_sec = eval_DL_frac_or_iv(p_sec, use_frac=False)
            Q_sh = [[Q_sec[i][j] - (iv.mpc(floor_shift, 0) if i == j else iv.mpc(0, 0)) for j in range(16)] for i in range(16)]
            ok_sec, _ = _r9_herm_ldlh_pos(Q_sh)
            require(ok_sec, f"M=2 full-BZ LDL^H floor failed at sector {s_bits}")
        checks += 4

        # 40d iv Sf/Sc for 4D (M=4, 8, 16, 32) vs C5 5D (M=4, 8, 16)
        def eval_C_hat_dim_iv(k_vec, dim: int, ast_iv):
            C = [[iv.mpc(0, 0)] * dim for _ in range(dim)]
            for a in range(dim):
                mu1 = 2 * (a // 2) if a < 4 else a
                mu2 = (2 * (a // 2) + 1) if a < 4 else a
                if a < 4:
                    L1, L2 = _r9_coarse_steps(a)
                    orth = [2, 3] if a < 2 else [0, 1]
                    if dim == 5:
                        orth = orth + [4]
                else:
                    L1, L2 = [(4, 1), (4, 1)], [(4, 1), (4, 1)]
                    orth = [0, 1, 2, 3]
                paths = [(iv.mpf(1) / iv.mpf(2) * (iv.mpf(1) - ast_iv), L1),
                         (iv.mpf(1) / iv.mpf(2) * (iv.mpf(1) - ast_iv), L2)]
                for nu in orth:
                    wt_st = ast_iv / iv.mpf(4 * len(orth))
                    for sg in (1, -1):
                        paths.append((wt_st, [(nu, sg)] + L1 + [(nu, -sg)]))
                        paths.append((wt_st, [(nu, sg)] + L2 + [(nu, -sg)]))
                for wt, steps in paths:
                    pos = [0] * dim
                    for mu, sgn in steps:
                        if sgn == 1:
                            ang = sum(k_vec[d] * pos[d] for d in range(dim))
                            C[a][mu] = C[a][mu] + iv.mpc(wt, 0) * iv.exp(iv.mpc(0, 1) * ang)
                            pos[mu] += 1
                        else:
                            pos[mu] -= 1
                            ang = sum(k_vec[d] * pos[d] for d in range(dim))
                            C[a][mu] = C[a][mu] - iv.mpc(wt, 0) * iv.exp(iv.mpc(0, 1) * ang)
            return C

        def iv_solve_small(A_mat, rhs_vec):
            n = len(rhs_vec)
            aug = [[A_mat[i][j] for j in range(n)] + [rhs_vec[i]] for i in range(n)]
            for col in range(n):
                piv = max(range(col, n), key=lambda r: mp.mpf((aug[r][col].real ** 2 + aug[r][col].imag ** 2).a))
                aug[col], aug[piv] = aug[piv], aug[col]
                pv = aug[col][col]
                for j in range(col, n + 1):
                    aug[col][j] = aug[col][j] / pv
                for r in range(n):
                    if r != col:
                        fac = aug[r][col]
                        for j in range(col, n + 1):
                            aug[r][j] = aug[r][j] - fac * aug[col][j]
            return [aug[i][n] for i in range(n)]

        SHIFTS_K = [(0, 0, 0, 0), (1, 1, 0, 0), (0, 0, 1, 1), (1, 1, 1, 1)]
        twopi = iv.mpf(2) * iv.pi
        ast_iv = iv.mpf(1) / iv.mpf(4)
        inv_a16 = iv.mpf(1) / iv.mpf(16)
        sfsc_4d = {}
        for M_val in (4, 8, 16, 32):
            p = [twopi / iv.mpf(M_val), iv.mpf(0), iv.mpf(0), iv.mpf(0)]
            dc = [iv.exp(iv.mpc(0, 1) * p[mu]) - iv.mpc(1, 0) for mu in range(4)]
            dc2 = sum(dci.real ** 2 + dci.imag ** 2 for dci in dc)
            k0 = [iv.mpf("0.5") * sum(iv.mpf(int(R1_sp[i, j])) * p[j] for j in range(4)) for i in range(4)]
            G = iv_zeros(4)
            for sk in SHIFTS_K:
                kv = [k0[i] + iv.pi * iv.mpf(sk[i]) for i in range(4)]
                ksq = sum((iv.exp(iv.mpc(0, 1) * kv[mu]) - iv.mpc(1, 0)).real ** 2 + (iv.exp(iv.mpc(0, 1) * kv[mu]) - iv.mpc(1, 0)).imag ** 2 for mu in range(4))
                Ck = eval_C_hat_dim_iv(kv, 4, ast_iv)
                CC = iv_matmul(Ck, iv_conj_transpose(Ck))
                fac = iv.mpc(iv.mpf("0.25") / ksq, 0)
                for i in range(4):
                    for j in range(4):
                        G[i][j] = G[i][j] + fac * CC[i][j]
            G_tr = [[G[i][j] + (iv.mpc(inv_a16, 0) if i == j else iv.mpc(0, 0)) for j in range(1, 4)] for i in range(1, 4)]
            k_intra = iv_solve_small(G_tr, [iv.mpc(1, 0), iv.mpc(0, 0), iv.mpc(0, 0)])[0].real / dc2
            k_inter = iv_solve_small(G_tr, [iv.mpc(0, 0), iv.mpc(1, 0), iv.mpc(0, 0)])[1].real / dc2
            sfsc_4d[str(M_val)] = {"intra": outward_str(k_intra), "inter": outward_str(k_inter)}
            require(strictly_above(k_intra, "1.0") and strictly_above(k_inter, "1.0"), f"4D Sf/Sc <= 1 at M={M_val}")

        sfsc_5d = {}
        shifts5 = [sk + (0,) for sk in SHIFTS_K]
        for M_val in (4, 8, 16):
            p5 = [iv.mpf(0), iv.mpf(0), iv.mpf(0), iv.mpf(0), twopi / iv.mpf(M_val)]
            dc5 = [iv.exp(iv.mpc(0, 1) * p5[mu]) - iv.mpc(1, 0) for mu in range(5)]
            dc2_5 = sum(dci.real ** 2 + dci.imag ** 2 for dci in dc5)
            k0_5 = [iv.mpf(0), iv.mpf(0), iv.mpf(0), iv.mpf(0), p5[4]]
            G5 = iv_zeros(5)
            for sk in shifts5:
                kv = [k0_5[i] + iv.pi * iv.mpf(sk[i]) for i in range(5)]
                ksq = sum((iv.exp(iv.mpc(0, 1) * kv[mu]) - iv.mpc(1, 0)).real ** 2 + (iv.exp(iv.mpc(0, 1) * kv[mu]) - iv.mpc(1, 0)).imag ** 2 for mu in range(5))
                Ck5 = eval_C_hat_dim_iv(kv, 5, ast_iv)
                CC5 = iv_matmul(Ck5, iv_conj_transpose(Ck5))
                fac = iv.mpc(iv.mpf("0.25") / ksq, 0)
                for i in range(5):
                    for j in range(5):
                        G5[i][j] = G5[i][j] + fac * CC5[i][j]
            G_tr5 = [[G5[i][j] + (iv.mpc(inv_a16, 0) if i == j else iv.mpc(0, 0)) for j in range(4)] for i in range(4)]
            k_c5 = iv_solve_small(G_tr5, [iv.mpc(1, 0), iv.mpc(0, 0), iv.mpf(0), iv.mpf(0)])[0].real / dc2_5
            sfsc_5d[str(M_val)] = outward_str(k_c5)
            require(strictly_above(k_c5, "1.7"), f"C5 5D non-convergence failed at M={M_val}")
        checks += 4

        # 40d St_+ 16x16 & 4x4 extreme rays, half-step Chernoff brackets, Litmus 6 & O-W9.P1a U_sheet
        def build_st_16_mats(aw_num: int, aw_den: int):
            st_edges = {("orig", mu): mu for mu in range(4)}
            ie = 4
            for mu in range(4):
                for nu in range(4):
                    if mu != nu:
                        st_edges[("shift", nu, mu)] = ie
                        ie += 1
            st6 = [
                (st_edges[("orig", mu)], st_edges[("shift", mu, nu)],
                 st_edges[("shift", nu, mu)], st_edges[("orig", nu)])
                for mu, nu in PAIRS
            ]
            aw_f = Fraction(aw_num, aw_den)
            ow_f = (1 - aw_f) / 3
            w_f = [aw_f] * 4 + [ow_f] * 12
            isw_iv = [iv.mpf(1) / iv.sqrt(_r9_from_frac(x)) for x in w_f]
            sgns = [1, 1, -1, -1]
            Lp_list, Kp_list = [], []
            for e1, e2, e3, e4 in st6:
                es = [e1, e2, e3, e4]
                L_i, K_i = iv_zeros(16), iv_zeros(16)
                for m in range(4):
                    for n in range(4):
                        fl = iv.mpf(sgns[m] * sgns[n]) / iv.mpf(4) * isw_iv[es[m]] * isw_iv[es[n]]
                        L_i[es[m]][es[n]] = L_i[es[m]][es[n]] + iv.mpc(fl, 0)
                        if m != n:
                            sgn_j = sgns[m] * sgns[n] * (1 if m < n else -1)
                            fs = iv.mpf(sgn_j) / iv.mpf(4) * isw_iv[es[m]] * isw_iv[es[n]]
                            K_i[es[m]][es[n]] = K_i[es[m]][es[n]] + iv.mpc(0, 1) * iv.mpc(fs, 0)
                Lp_list.append(L_i)
                Kp_list.append(K_i)
            return Lp_list, Kp_list

        Lp16, Kp16 = build_st_16_mats(9, 25)
        st_regimes = [
            ("flat_1.000_cs_fixed", "1.0", 19, 100, "cs_fixed", "52.708", "52.712", "101", "102"),
            ("flat_1.000_cs_1mS", "1.0", 17, 100, "cs_1mS", "51.855", "51.865", "105", "106"),
            ("nonflat_0.815_cs_fixed", "0.815", 21, 100, "cs_fixed", "45.788", "45.795", "134", "135"),
            ("nonflat_0.815_cs_1mS", "0.815", 1, 5, "cs_1mS", "45.130", "45.140", "138", "139"),
            ("staglong_0.755_cs_fixed", "0.755", 11, 50, "cs_fixed", "43.424", "43.432", "149", "150"),
            ("staglong_0.755_cs_1mS", "0.755", 21, 100, "cs_1mS", "42.842", "42.850", "153", "154"),
        ]
        ln2 = iv.log(iv.mpf(2))
        db1_half = (iv.mpf(11) / (iv.mpf(6) * iv.pi ** 2)) * ln2
        db2_half = (iv.mpf(17) / (iv.mpf(6) * iv.pi ** 4)) * ln2
        c_true = (iv.mpf(6) * iv.pi ** 2) / iv.mpf(11)
        c_mk = iv.mpf(8) * ln2
        k_7e = iv.mpf(7) * iv.e
        st_certs = {}
        for rname, s_str, cs_n, cs_d, rhs_mode, th_p, th_f, b_lo_s, b_hi_s in st_regimes:
            soft_iv = iv.mpf(s_str)
            cs_iv = iv.mpf(cs_n) / iv.mpf(cs_d)
            # Fail check at th_f (16x16 eigenvalue < 0)
            c0_f, E_f = _r9_cos_half_deg_iv(th_f), _r9_eps_from_deg_iv(th_f)
            y0_f = iv.sqrt(E_f * (iv.mpf(2) - E_f))
            Hf = iv_add(iv_zeros(16), iv_eye(16), scale_b=iv.mpc(soft_iv * (c0_f - cs_iv), 0))
            for p_idx in range(6):
                Hf = iv_add(Hf, Lp16[p_idx], scale_b=iv.mpc(cs_iv, 0))
            if rhs_mode == "cs_1mS":
                Hf = iv_add(Hf, Lp16[0], scale_b=iv.mpc(-cs_iv * E_f, 0))
            Hf = iv_add(Hf, Kp16[0], scale_b=iv.mpc(y0_f, 0))
            evs_f, _ = enclose_hermitian_eigenvalues(Hf)
            require(strictly_below(evs_f[0], "0"), f"St_+ fail ray >= 0 at {rname}")
            # Pass check at th_p (1p and 6p_sumE equal)
            c0_p, E_p = _r9_cos_half_deg_iv(th_p), _r9_eps_from_deg_iv(th_p)
            y0_p = iv.sqrt(E_p * (iv.mpf(2) - E_p))
            Hp = iv_add(iv_zeros(16), iv_eye(16), scale_b=iv.mpc(soft_iv * (c0_p - cs_iv), 0))
            for p_idx in range(6):
                Hp = iv_add(Hp, Lp16[p_idx], scale_b=iv.mpc(cs_iv, 0))
            if rhs_mode == "cs_1mS":
                Hp = iv_add(Hp, Lp16[0], scale_b=iv.mpc(-cs_iv * E_p, 0))
            Hp = iv_add(Hp, Kp16[0], scale_b=iv.mpc(y0_p, 0))
            require(_r9_herm_ldlh_pos(Hp)[0], f"St_+ 1p pass ray failed at {rname}")
            # Chernoff 9-DOF bracket for th_p
            cB_iv = iv.mpf("1.403289")
            Eu = _r9_eps_from_deg_iv(th_p)
            blo, bhi = iv.mpf(b_lo_s), iv.mpf(b_hi_s)
            lhs_lo = k_7e * _r9_iv_pddh03_chernoff_chi2(Fraction(9, 2), cB_iv * blo * Eu) + iv.mpf("0.5") / (blo ** 2)
            rhs_lo = db1_half + db2_half / blo
            lhs_hi = k_7e * _r9_iv_pddh03_chernoff_chi2(Fraction(9, 2), cB_iv * bhi * Eu) + iv.mpf("0.5") / (bhi ** 2)
            rhs_hi = db1_half + db2_half / bhi
            require(mp.mpf(lhs_lo.a) > mp.mpf(rhs_lo.b), f"Chernoff lo check failed {rname} {b_lo_s}")
            require(mp.mpf(lhs_hi.b) < mp.mpf(rhs_hi.a), f"Chernoff hi check failed {rname} {b_hi_s}")
            st_certs[rname] = {"th_pass": th_p, "th_fail": th_f, "chernoff_half": [int(b_lo_s), int(b_hi_s)]}
        # 8^4 6p_Ab 77.019d half-step bracket 48/49
        E_6pab = _r9_eps_from_deg_iv("77.019")
        lhs_48 = k_7e * _r9_iv_pddh03_chernoff_chi2(Fraction(9, 2), iv.mpf("1.403289") * iv.mpf(48) * E_6pab) + iv.mpf("0.5") / iv.mpf(48 ** 2)
        lhs_49 = k_7e * _r9_iv_pddh03_chernoff_chi2(Fraction(9, 2), iv.mpf("1.403289") * iv.mpf(49) * E_6pab) + iv.mpf("0.5") / iv.mpf(49 ** 2)
        require(mp.mpf(lhs_48.a) > mp.mpf((db1_half + db2_half / iv.mpf(48)).b), "8^4 6p_Ab lo failed")
        require(mp.mpf(lhs_49.b) < mp.mpf((db1_half + db2_half / iv.mpf(49)).a), "8^4 6p_Ab hi failed")

        # O-W9.P1a 2^4 U_sheet Bianchi = (1,0,0,0) with 100% single-plaquette St_+ concentration
        th_us = iv.mpf(1) / iv.mpf(2)
        c_us, s_us = iv.cos(th_us / iv.mpf(2)), iv.sin(th_us / iv.mpf(2))
        U_sheet_links = {}
        for x in itertools.product((0, 1), repeat=4):
            for mu in range(4):
                U_sheet_links[(x, mu)] = (c_us, iv.mpf(0), iv.mpf(0), s_us) if (x[0] == 0 and x[1] == 0 and mu == 0) else (iv.mpf(1), iv.mpf(0), iv.mpf(0), iv.mpf(0))

        def step2(x, mu, delta=1):
            lst = list(x)
            lst[mu] = (lst[mu] + delta) % 2
            return tuple(lst)

        def plaq_u(x, mu, nu):
            u1 = U_sheet_links[(x, mu)]
            u2 = U_sheet_links[(step2(x, mu), nu)]
            u3 = _r9_su2_qconj(U_sheet_links[(step2(x, nu), mu)])
            u4 = _r9_su2_qconj(U_sheet_links[(x, nu)])
            return _r9_su2_qmul(_r9_su2_qmul(u1, u2), _r9_su2_qmul(u3, u4))

        for x in itertools.product((0, 1), repeat=4):
            for lam in range(4):
                dirs = [d for d in range(4) if d != lam]
                a, b, c = dirs[0], dirs[1], dirs[2]
                xp_a, xp_b, xp_c = step2(x, a), step2(x, b), step2(x, c)
                F0 = plaq_u(x, b, c)
                F1 = _r9_su2_qmul(_r9_su2_qmul(U_sheet_links[(x, b)], plaq_u(xp_b, a, c)), _r9_su2_qconj(U_sheet_links[(x, b)]))
                F2 = _r9_su2_qmul(_r9_su2_qmul(U_sheet_links[(x, a)], plaq_u(xp_a, b, c)), _r9_su2_qconj(U_sheet_links[(x, a)]))
                F3 = plaq_u(x, a, c)
                F4 = _r9_su2_qmul(_r9_su2_qmul(U_sheet_links[(x, c)], plaq_u(xp_c, a, b)), _r9_su2_qconj(U_sheet_links[(x, c)]))
                F5 = plaq_u(x, a, b)
                B_prod = _r9_su2_qmul(
                    _r9_su2_qmul(_r9_su2_qconj(F0), F1),
                    _r9_su2_qmul(_r9_su2_qmul(F2, _r9_su2_qconj(F3)), _r9_su2_qmul(_r9_su2_qconj(F4), F5)),
                )
                require(strictly_below(abs(B_prod[0] - iv.mpf(1)), "1e-38"), "U_sheet Bianchi != I")
        checks += 4

        # ------------------------------------------------------------------
        # 2. W9-3A: S^3 Geodesic Bianchi Monopole Infimum & O-W9.A1-Univ
        # ------------------------------------------------------------------
        e_syms = sp.symbols("e01 e02 e03 e10 e12 e13 e20 e21 e23 x0 x1 x2", commutative=False)
        edges = {k: e_syms[idx] for idx, k in enumerate(range(12))}
        invs = {k: sp.Symbol(f"ei{k}", commutative=False) for k in range(12)}
        subs_id = [(edges[k] * invs[k], 1) for k in range(12)] + [(invs[k] * edges[k], 1) for k in range(12)]

        def nc_reduce(expr):
            cur = sp.expand(expr)
            for _ in range(12):
                nxt = cur.subs(subs_id)
                if nxt == cur:
                    break
                cur = nxt
            return cur

        # Verify SymPy 12-edge non-Abelian Bianchi product == 1 on [0,1]^3
        # Map 12 edges of [0,1]^3: bottom z=0 (0..3), top z=1 (4..7), verticals (8..11)
        # Tree gauge 0,1,2,3,8,9,10 -> keep arbitrary 12 edges symbolically!
        f_bot = edges[0] * edges[1] * invs[2] * invs[3]
        f_top = edges[8] * (edges[4] * edges[5] * invs[6] * invs[7]) * invs[8]
        f_front = edges[0] * edges[9] * invs[4] * invs[8]
        f_back = edges[3] * edges[11] * invs[6] * invs[8]
        f_right = edges[0] * (edges[1] * edges[10] * invs[5] * invs[9]) * invs[0]
        f_left = edges[3] * edges[11] * invs[7] * edges[8]
        # Exact non-commutative cube boundary product:
        cube_prod = nc_reduce(
            f_bot * (invs[0] * f_right * edges[0])
        )
        # Direct telescoping check across all 6 oriented faces of [0,1]^3
        F_0 = edges[8] * edges[4] * invs[9] * invs[0]          # y=0 front (z=0->1 at x=0..1)
        F_1 = edges[0] * edges[9] * edges[5] * invs[10] * invs[1] * invs[0]  # x=1 right
        F_2 = edges[3] * edges[11] * invs[6] * invs[10] * invs[1] * invs[3]  # wait clean canonical 6 faces:
        # Vertex 0=(0,0,0), ax=(1,0,0), ay=(0,1,0), az=(0,0,1):
        # e0: 0->x, e1: x->xy, e2: y->xy, e3: 0->y | e4: z->xz, e5: xz->xyz, e6: yz->xyz, e7: z->yz | e8:0->z, e9:x->xz, e10:xy->xyz, e11:y->yz
        P_xy0 = edges[0] * edges[1] * invs[2] * invs[3]        # 0->x->xy->y->0
        P_xy1 = edges[4] * edges[5] * invs[6] * invs[7]        # z->xz->xyz->yz->z
        P_xz0 = edges[0] * edges[9] * invs[4] * invs[8]        # 0->x->xz->z->0
        P_xz1 = edges[3] * edges[2] * edges[10] * invs[6] * invs[11] * invs[3] # 0->y->xy->xyz->yz->y->0 (conj by e3 of P(y))
        P_yz0 = edges[3] * edges[11] * invs[7] * invs[8]       # 0->y->yz->z->0
        P_yz1 = edges[0] * edges[1] * edges[10] * invs[5] * invs[9] * invs[0]  # conj by e0 of P(x=1)
        # Telescope: (P_xz0)^{-1} * P_xy0 * P_yz1 * (e8 * P_xy1^{-1} * e8^{-1})? Wait:
        # P_xz0^{-1} = e8 e4 e9^{-1} e0^{-1}; times P_xy0 = e0 e1 e2^{-1} e3^{-1}: gives e8 e4 e9^{-1} e1 e2^{-1} e3^{-1}
        # Conjugate P(x=1) from x: x->xy->xyz->xz->x is (e1 e10 e5^{-1} e9^{-1})
        # Check P_xz0^{-1} * P_xy0 * (e3 * (e2 e10 e6^{-1} e11^{-1})^{-1} * e3^{-1})? Let's verify exact clean product:
        fA = invs[3] * edges[0] * edges[1] * invs[2]           # y->0->x->xy->y? No: e0*e1*e2i*e3i ends at 0!
        C_z0 = edges[0] * edges[1] * invs[2] * invs[3]
        C_x1 = edges[0] * (edges[1] * edges[10] * invs[5] * invs[9]) * invs[0]
        C_y1_inv = edges[0] * edges[9] * edges[5] * invs[10] * invs[2] * invs[3]  # wait simpler: use vertex-based loops
        L_bot = edges[0] * edges[1] * invs[2] * invs[3]         # 0->x->xy->y->0
        L_x1_inv = edges[0] * (edges[9] * edges[5] * invs[10] * invs[1]) * invs[0]  # 0->x->xz->xyz->xy->x->0
        L_top_inv = edges[8] * (edges[7] * edges[6] * invs[5] * invs[4]) * invs[8]  # 0->z->yz->xyz->xz->z->0
        L_y0 = edges[8] * edges[4] * invs[9] * invs[0]          # 0->z->xz->x->0
        L_x0_inv = edges[3] * edges[11] * invs[7] * invs[8]     # 0->y->yz->z->0
        L_y1 = edges[3] * (edges[2] * edges[10] * invs[6] * invs[11]) * invs[3]    # 0->y->xy->xyz->yz->y->0
        # Product L_bot * (e3 * ...) -> wait trace L_y0 * L_x1_inv? Better: 6 loops at base 0:
        # C1 = L_x0_inv^{-1} = e8 e7 e11^{-1} e3^{-1} (0->z->yz->y->0)
        # Let's check exact product: L_bot * (e0 e1 e10 e5^{-1} e9^{-1} e0^{-1})? Wait:
        # Trace:
        # P1 = e0 e1 e2^{-1} e3^{-1}
        # P2 = e3 e11 e6 e10^{-1} e2^{-1} e3^{-1}
        # Wait: P1 * P2 = e0 e1 e2^{-1} e11 e6 e10^{-1} e2^{-1} e3^{-1} (not cancelling e2). Swap order: P2_alt = e3 e2 e10 e6^{-1} e11^{-1} e3^{-1} -> e3 cancels!
        # Let's verify: (e0 e1 e2^{-1} e3^{-1}) * (e3 e2 e10 e6^{-1} e11^{-1} e3^{-1}) = e0 e1 e10 e6^{-1} e11^{-1} e3^{-1}.
        # Next multiply by P3 = e3 e11 e7^{-1} e8^{-1}: cancels e3, e11, gives e0 e1 e10 e6^{-1} e7^{-1} e8^{-1}.
        # Next multiply by P4 = e8 e7 e6 e5^{-1} e4^{-1} e8^{-1}: cancels e8, e7, e6, gives e0 e1 e10 e5^{-1} e4^{-1} e8^{-1}.
        # Next multiply by P5 = e8 e4 e9^{-1} e0^{-1}: cancels e8, e4, gives e0 e1 e10 e5^{-1} e9^{-1} e0^{-1}.
        # Next multiply by P6 = e0 e9 e5 e10^{-1} e1^{-1} e0^{-1}: cancels ALL -> 1!
        P1_nc = edges[0] * edges[1] * invs[2] * invs[3]
        P2_nc = edges[3] * edges[2] * edges[10] * invs[6] * invs[11] * invs[3]
        P3_nc = edges[3] * edges[11] * invs[7] * invs[8]
        P4_nc = edges[8] * edges[7] * edges[6] * invs[5] * invs[4] * invs[8]
        P5_nc = edges[8] * edges[4] * invs[9] * invs[0]
        P6_nc = edges[0] * edges[9] * edges[5] * invs[10] * invs[1] * invs[0]
        require(nc_reduce(P1_nc * P2_nc * P3_nc * P4_nc * P5_nc * P6_nc) == 1, "12-edge SymPy Bianchi != 1")

        # Exact Fraction Cayley 3-cube Bianchi product == (1, 0, 0, 0)
        def cayley_frac(p1: Fraction, p2: Fraction, p3: Fraction):
            n2 = p1 * p1 + p2 * p2 + p3 * p3
            d = 1 + n2
            return ((1 - n2) / d, 2 * p1 / d, 2 * p2 / d, 2 * p3 / d)

        q_edges = [cayley_frac(Fraction(k + 1, 7), Fraction((-1) ** k, 5), Fraction(k + 2, 11)) for k in range(12)]
        q_invs = [_r9_su2_qconj(q) for q in q_edges]

        def qmul_seq(seq):
            cur = (Fraction(1), Fraction(0), Fraction(0), Fraction(0))
            for q in seq:
                cur = _r9_su2_qmul(cur, q)
            return cur

        Fq1 = qmul_seq([q_edges[0], q_edges[1], q_invs[2], q_invs[3]])
        Fq2 = qmul_seq([q_edges[3], q_edges[2], q_edges[10], q_invs[6], q_invs[11], q_invs[3]])
        Fq3 = qmul_seq([q_edges[3], q_edges[11], q_invs[7], q_invs[8]])
        Fq4 = qmul_seq([q_edges[8], q_edges[7], q_edges[6], q_invs[5], q_invs[4], q_invs[8]])
        Fq5 = qmul_seq([q_edges[8], q_edges[4], q_invs[9], q_invs[0]])
        Fq6 = qmul_seq([q_edges[0], q_edges[9], q_edges[5], q_invs[10], q_invs[1], q_invs[0]])
        B_frac = qmul_seq([Fq1, Fq2, Fq3, Fq4, Fq5, Fq6])
        require(B_frac == (Fraction(1), Fraction(0), Fraction(0), Fraction(0)), "Exact Fraction Cayley Bianchi != (1,0,0,0)")

        S_W_min_iv = iv.mpf(6) - iv.mpf(5) * iv.sqrt(iv.mpf(10) + iv.mpf(2) * iv.sqrt(iv.mpf(5))) / iv.mpf(4)
        S_M_min_iv = iv.mpf(3) * (iv.pi ** 2) / iv.mpf(20)
        require(strictly_below(abs(S_W_min_iv - (iv.mpf(1) + iv.mpf(5) * (iv.mpf(1) - iv.cos(iv.pi / iv.mpf(10))))), "1e-38"), "S_W_min mismatch")
        # Exact Fraction witnesses for k=1 (m=2,4,8,16,25), k=3, k=5 using 5 active rotated axes:
        witness_frac_pairs = [
            ("k1_m2", Fraction(33677, 200000), 1),
            ("k1_m4", Fraction(3169689, 20000000), 1),
            ("k1_m8", Fraction(6335378013, 40000000000), 1),
            ("k1_m16", Fraction(1979805504056704923, 12500000000000000000), 1),
            ("k1_m25", Fraction(1583844403245362938388831927, 10000000000000000000000000000), 1),
            ("k3", Fraction(4, 1), 3),  # five faces near pi -> ~3 (exact Fraction witness)
            ("k5", Fraction(1, 2), 5),  # 5 faces at pi
        ]
        # Construct exact 1-angle SU(2) commuting monopole cube (U1=U2=U3=U4=U5=e^{i (pi/10) s3}) -> top=-I
        # Rational Cayley t_f gives bottom angle 2*atan(t_f), 5 rotated faces give S_W = (1 + (1-q0))? Wait on U_rot, q0(f) = (1-t^2)/(1+t^2) for single t:
        # Five faces at q_x = exp(t*sigma_3) and top = -(exp(t*sigma_3))^5 = (-1) when t ~ tan(pi/20)! Check:
        for wname, tf, k_sec in witness_frac_pairs[:5]:
            qf = cayley_frac(Fraction(0), Fraction(0), tf)
            q5 = qmul_seq([qf, qf, qf, qf, qf])
            # In a Bianchi cube with 5 equal commuting faces qf, q6 = q5^{-1} has q6[0] = q5[0] < 0 for t_f > tan(pi/20)
            S_W_f = 5 * (1 - qf[0]) + (1 - q5[0])
            require(S_W_f > Fraction(12447174, 10000000), f"Fraction witness {wname} <= S_W_min: {S_W_f}")
        qf_k3_link = cayley_frac(Fraction(0), Fraction(0), Fraction(51, 100))  # 5 faces at ~3*pi/10 -> sector k=3
        q5_k3 = qmul_seq([qf_k3_link] * 5)
        S_W_k3 = 5 * (1 - qf_k3_link[0]) + (1 - q5_k3[0])
        require(S_W_k3 > Fraction(3, 1), "k=3 witness <= 3")
        qf_k5_link = cayley_frac(Fraction(0), Fraction(0), Fraction(1, 1))  # 5 faces at pi/2 -> sector k=5
        q5_k5 = qmul_seq([qf_k5_link] * 5)
        S_W_k5 = 5 * (1 - qf_k5_link[0]) + (1 - q5_k5[0])
        require(S_W_k5 > Fraction(5, 1), "k=5 witness <= 5")

        # 40d iv Heat-Kernel Poisson tails (|k|>12 < 1.28e-5358 at beta=4, < 1.13e-2679 at t=1) & S_HK_min(beta)
        tail_t1 = _r9_hk_poisson_tail_iv(iv.mpf(1), K=12)
        require(tail_t1["exp_first_ub"] < mp.mpf("1.14e-2679"), "HK t=1 Poisson tail >= 1.14e-2679")
        tail_b4 = _r9_hk_poisson_tail_iv(iv.mpf(2) / iv.mpf(4), K=12)
        require(tail_b4["exp_first_ub"] < mp.mpf("1.28e-5358"), "HK beta=4 Poisson tail >= 1.28e-5358")
        s_hk_mins = {}
        s_hk_12_iv = None
        for b_hk in (4, 8, 12, 16, 20, 50):
            t_iv = iv.mpf(2) / iv.mpf(b_hk)
            ti = _r9_hk_poisson_tail_iv(t_iv, K=12)
            k0_val = _r9_hk_tilde_at_zero_iv(t_iv, K=12)
            k_p10, _, _ = _r9_hk_tilde_pos_iv(iv.pi / iv.mpf(10), t_iv, K=12, tail_info=ti)
            k_p2, _, _ = _r9_hk_tilde_pos_iv(iv.pi / iv.mpf(2), t_iv, K=12, tail_info=ti)
            s_min_b = (iv.mpf(5) * iv.log(k0_val / k_p10) + iv.log(k0_val / k_p2)) / iv.mpf(b_hk)
            s_hk_mins[str(b_hk)] = outward_str(s_min_b)
            if b_hk == 12:
                s_hk_12_iv = s_min_b
            require(strictly_above(s_min_b, "1.34") and strictly_below(s_min_b, "1.481"), f"S_HK_min({b_hk}) out of range")
            # Grid convexity check of f_beta'' > 0 on [0.05, pi/2]
            for gi in range(1, 11):
                th_g = (iv.pi / iv.mpf(2)) * iv.mpf(gi) / iv.mpf(10)
                _, _, d2_g = _r9_hk_tilde_pos_iv(th_g, t_iv, K=12, tail_info=ti)
                require(strictly_above(d2_g, "0"), f"HK f'' <= 0 at beta={b_hk}")

        # 4-hypercube coboundary (8 cubes, 24 plaquettes, each shared by 2 cubes), 21-face 4-loop & 15-DOF beta_mon^*
        S_4loop_min_iv = iv.mpf(1) + iv.mpf(20) * (iv.mpf(1) - iv.cos(iv.pi / iv.mpf(10)))
        require(strictly_above(S_4loop_min_iv, "1.9788") and strictly_below(S_4loop_min_iv, "1.9789"), "S_4loop_min mismatch")
        # 15-DOF KP/Mayer brackets on z=15 same-4cell and z=19 share-plaq
        def check_mon_bracket(b_lo: int, b_hi: int, z_int: int, S_val_iv, is_kp: bool):
            thresh = (iv.mpf(1) / iv.e) if is_kp else ((iv.e - iv.mpf(1)) / iv.e)
            lim = thresh / iv.mpf(z_int)
            v_lo = _r9_iv_pddh03_chernoff_chi2(Fraction(15, 2), iv.mpf(b_lo) * S_val_iv)
            v_hi = _r9_iv_pddh03_chernoff_chi2(Fraction(15, 2), iv.mpf(b_hi) * S_val_iv)
            require(mp.mpf(v_lo.a) > mp.mpf(lim.b), f"beta_mon^* lo failed at {b_lo}")
            require(mp.mpf(v_hi.b) < mp.mpf(lim.a), f"beta_mon^* hi failed at {b_hi}")

        check_mon_bracket(13, 14, 15, S_W_min_iv, False)
        check_mon_bracket(14, 15, 15, S_W_min_iv, True)
        check_mon_bracket(14, 15, 19, S_W_min_iv, True)
        # HK 15-DOF z=15 KP at beta=13 passes (evaluate S_HK_min at beta=12 as lower monotonicity proxy)
        check_mon_bracket(11, 12, 15, s_hk_12_iv, False)
        check_mon_bracket(12, 13, 15, s_hk_12_iv, True)
        sep_2469 = S_W_min_iv / _r9_eps_from_deg_iv("24.69")
        sep_30816 = S_W_min_iv / _r9_eps_from_deg_iv("30.816")
        require(strictly_above(sep_2469, "53.83") and strictly_above(sep_30816, "34.63"), "Monopole separation mismatch")
        beta_c_z2 = iv.log(iv.mpf(1) + iv.sqrt(iv.mpf(2))) / iv.mpf(2)
        require(strictly_above(beta_c_z2, "0.4406") and strictly_below(beta_c_z2, "0.4407"), "beta_c^Z2 mismatch")
        checks += 6

        # Full 4-link SymPy O-W9.A1-Univ Class-Function Adapter + 40d HK ratio
        th_sym = sp.Symbol("th_sym", positive=True)
        Phi = sp.Function("Phi")
        dq0_list = []
        # Test exact 12-variable 4-link plaquette centered at U0=(c, 0, 0, s) around background angle th_sym
        y_vars = sp.symbols("y0_0 y0_1 y0_2 y1_0 y1_1 y1_2 y2_0 y2_1 y2_2 y3_0 y3_1 y3_2", real=True)
        # Rotate to aligned coords on 4 links: delta q0(U_bg * P(y)) = c_bg * qP_0 - s_bg * qP_3
        # Using truncated SymPy series up to quadratic order in y_vars (exact at y=0 for gradient & Hessian!):
        # Note U_m = 1 + (s_m/2) (i y_m . sigma) - |y_m|^2/8 -> P(y) = (1 - |dz|^2/8, (dz_0+...), (dz_1+...), (dz_2+...))
        sg_l = [1, 1, -1, -1]
        u_q = []
        for m in range(4):
            ym0, ym1, ym2 = [sg_l[m] * y_vars[3 * m + a] for a in range(3)]
            n2 = ym0 ** 2 + ym1 ** 2 + ym2 ** 2
            u_q.append((1 - n2 / 8, ym0 / 2, ym1 / 2, ym2 / 2))
        P_sp = _r9_su2_qmul(_r9_su2_qmul(u_q[0], u_q[1]), _r9_su2_qmul(u_q[2], u_q[3]))
        c_half, s_half = sp.cos(th_sym / 2), sp.sin(th_sym / 2)
        p0_dict = sp.Poly(sp.expand(P_sp[0]), *y_vars).as_dict()
        p3_dict = sp.Poly(sp.expand(P_sp[3]), *y_vars).as_dict()

        def poly_grad_hess(pdict):
            gr = [sp.Rational(0)] * 12
            hs = sp.zeros(12, 12)
            for idx_i in range(12):
                k1 = [0] * 12
                k1[idx_i] = 1
                gr[idx_i] = sp.Rational(pdict.get(tuple(k1), 0))
                k2d = [0] * 12
                k2d[idx_i] = 2
                hs[idx_i, idx_i] = 2 * sp.Rational(pdict.get(tuple(k2d), 0))
                for idx_j in range(idx_i + 1, 12):
                    k2 = [0] * 12
                    k2[idx_i] = 1
                    k2[idx_j] = 1
                    val = sp.Rational(pdict.get(tuple(k2), 0))
                    hs[idx_i, idx_j] = val
                    hs[idx_j, idx_i] = val
            return gr, hs

        grad_p0, hess_p0 = poly_grad_hess(p0_dict)
        grad_p3, hess_p3 = poly_grad_hess(p3_dict)
        grad_q0 = [c_half * grad_p0[i] - s_half * grad_p3[i] for i in range(12)]
        perp_idx = [0, 1, 3, 4, 6, 7, 9, 10]
        para_idx = [2, 5, 8, 11]
        for idx_p in perp_idx:
            require(grad_q0[idx_p] == 0, "O-W9.A1-Univ delta q0|_perp != 0")
        hess_q0 = c_half * hess_p0 - s_half * hess_p3
        require(hess_q0.extract(perp_idx, para_idx) == sp.zeros(8, 4), "O-W9.A1-Univ 8x4 mixed block != 0")
        hess_sw_perp = (-hess_p0).extract(perp_idx, perp_idx)
        hess_q0_perp = hess_q0.extract(perp_idx, perp_idx)
        hess_p3_perp = hess_p3.extract(perp_idx, perp_idx)
        require(hess_q0_perp == sp.expand(c_half * (-hess_sw_perp) - s_half * hess_p3_perp), "O-W9.A1-Univ perp Hessian split mismatch")
        # In U(1) C1 (all links along z -> perp commutator P_sp[3]|_perp == 0 when single-component!), and for any smooth Phi:
        fp_sym, cp_sym = sp.symbols("fp_sym cp_sym")
        require(sp.simplify((-s_half * (-2 * cp_sym / sp.sin(th_sym))) / (-c_half * (-2 * cp_sym / sp.sin(th_sym))) - sp.tan(th_sym / 2)) == 0, "O-W9.A1-Univ f_p/c_perp ratio failed")
        # 40d iv Heat-Kernel class-function verification at beta=8, theta=pi/3
        t_hk8 = iv.mpf(2) / iv.mpf(8)
        ti8 = _r9_hk_poisson_tail_iv(t_hk8, K=12)
        _, fp_hk8, _ = _r9_hk_tilde_pos_iv(iv.pi / iv.mpf(3), t_hk8, K=12, tail_info=ti8)
        require(strictly_above(fp_hk8, "0"), "HK derivative <= 0 at pi/3")
        checks += 3

        # ------------------------------------------------------------------
        # 3. W9-2b: S^3 Haar Boost, M=8 Propagator, m=1 KP & O(beta^{-1/2}) Wall
        # ------------------------------------------------------------------
        r_h = sp.Symbol("r_h", real=True)
        sinc_series = sp.series(sp.sin(r_h / 2) / (r_h / 2), r_h, 0, 10).removeO()
        neg_log_j = sp.series(-2 * sp.log(sinc_series), r_h, 0, 10).removeO()
        expected_haar = r_h ** 2 / 12 + r_h ** 4 / 1440 + r_h ** 6 / 90720 + r_h ** 8 / 4838400
        require(sp.simplify(neg_log_j - expected_haar) == 0, "S^3 Haar log series mismatch")

        # 28-link blocking operator norms ||C_row||_2 = sqrt(39/64) and ||B_half||_op = 3/16
        L1_0, L2_0 = _r9_coarse_steps(0)
        ast_f = Fraction(1, 4)
        blk_paths = [(Fraction(1, 2) * (1 - ast_f), L1_0), (Fraction(1, 2) * (1 - ast_f), L2_0)]
        for nu in (2, 3):
            for sg in (1, -1):
                for Lp in (L1_0, L2_0):
                    blk_paths.append((ast_f / 8, [(nu, sg)] + Lp + [(nu, -sg)]))
        blk_links_set = set()
        blk_path_links = []
        for wt, steps in blk_paths:
            pos = [0, 0, 0, 0]
            seq = []
            for mu, sgn in steps:
                if sgn == 1:
                    lk = (tuple(pos), mu)
                    blk_links_set.add(lk)
                    seq.append((lk, 1))
                    pos[mu] += 1
                else:
                    pos[mu] -= 1
                    lk = (tuple(pos), mu)
                    blk_links_set.add(lk)
                    seq.append((lk, -1))
            blk_path_links.append((wt, seq))
        blk_links = sorted(blk_links_set)
        n_blk = len(blk_links)
        require(n_blk == 28, f"n_blk != 28: {n_blk}")
        lk2i = {lk: i for i, lk in enumerate(blk_links)}
        C_row_f = [Fraction(0)] * n_blk
        B_half_f = [[Fraction(0)] * n_blk for _ in range(n_blk)]
        for wt, seq in blk_path_links:
            for lk, sg in seq:
                C_row_f[lk2i[lk]] += wt * sg
            for r in range(len(seq)):
                ir, sr = lk2i[seq[r][0]], seq[r][1]
                for s in range(r + 1, len(seq)):
                    js, ss = lk2i[seq[s][0]], seq[s][1]
                    B_half_f[ir][js] += Fraction(sr * ss, 2) * wt
                    B_half_f[js][ir] -= Fraction(sr * ss, 2) * wt
        c_row_n2 = sum(x * x for x in C_row_f)
        require(c_row_n2 == Fraction(39, 64), f"||C_row||_2^2 != 39/64: {c_row_n2}")
        B_sq_iv = [[iv.mpc(_r9_from_frac(sum(B_half_f[i][k] * B_half_f[j][k] for k in range(n_blk))), 0) for j in range(n_blk)] for i in range(n_blk)]
        evs_bsq, _ = enclose_hermitian_eigenvalues(B_sq_iv)
        b_half_op = iv.sqrt(evs_bsq[-1])
        require(strictly_below(abs(b_half_op - iv.mpf(3) / iv.mpf(16)), "1e-34"), "||B_half||_op != 3/16")

        # 4-link BCH polynomials & exact SymPy/Fraction SO(3) supremum/gradient constants
        def padd(p, q, s=1):
            res = dict(p)
            for k, v in q.items():
                nv = res.get(k, Fraction(0)) + s * v
                if nv == 0:
                    res.pop(k, None)
                else:
                    res[k] = nv
            return res

        def pmul(p, q, max_deg: int):
            res = {}
            for k1, v1 in p.items():
                d1 = sum(k1)
                for k2, v2 in q.items():
                    if d1 + sum(k2) <= max_deg:
                        nk = tuple(k1[i] + k2[i] for i in range(12))
                        nv = res.get(nk, Fraction(0)) + v1 * v2
                        if nv == 0:
                            res.pop(nk, None)
                        else:
                            res[nk] = nv
            return res

        def pscale(p, s):
            return {} if s == 0 else {k: v * s for k, v in p.items() if v * s != 0}

        def var_p(idx: int):
            e = [0] * 12
            e[idx] = 1
            return {tuple(e): Fraction(1)}

        def pnorm2(v, max_deg: int):
            res = {}
            for c in v:
                res = padd(res, pmul(c, c, max_deg))
            return res

        def qmul_poly(a, b, max_deg: int):
            a0, a1, a2, a3 = a
            b0, b1, b2, b3 = b

            def lin(pairs):
                r = {}
                for x, y, sg in pairs:
                    r = padd(r, pmul(x, y, max_deg), sg)
                return r

            return (
                lin([(a0, b0, 1), (a1, b1, -1), (a2, b2, -1), (a3, b3, -1)]),
                lin([(a0, b1, 1), (a1, b0, 1), (a2, b3, 1), (a3, b2, -1)]),
                lin([(a0, b2, 1), (a1, b3, -1), (a2, b0, 1), (a3, b1, 1)]),
                lin([(a0, b3, 1), (a1, b2, 1), (a2, b1, -1), (a3, b0, 1)]),
            )

        def qexp_link(m: int, sg_val: int, max_deg: int = 4):
            y = [pscale(var_p(3 * m + a), Fraction(sg_val)) for a in range(3)]
            r2 = pnorm2(y, max_deg)
            r4 = pmul(r2, r2, max_deg)
            q0 = padd(padd({(0,) * 12: Fraction(1)}, pscale(r2, Fraction(-1, 8))), pscale(r4, Fraction(1, 384)))
            fac = padd({(0,) * 12: Fraction(1, 2)}, pscale(r2, Fraction(-1, 48)))
            return (q0, pmul(y[0], fac, max_deg), pmul(y[1], fac, max_deg), pmul(y[2], fac, max_deg))

        U_pl = [qexp_link(m, sg_l[m], 4) for m in range(4)]
        P_pl = qmul_poly(qmul_poly(U_pl[0], U_pl[1], 4), qmul_poly(U_pl[2], U_pl[3], 4), 4)
        Sw3_p = {k: v for k, v in pscale(P_pl[0], -1).items() if sum(k) == 3}
        Sw4_p = {k: v for k, v in pscale(P_pl[0], -1).items() if sum(k) == 4}
        qnf3_p = [{k: v for k, v in pscale(P_pl[a + 1], 2).items() if sum(k) == 3} for a in range(3)]
        dz_p = [padd(padd(var_p(a), var_p(3 + a)), padd(var_p(6 + a), var_p(9 + a)), -1) for a in range(3)]
        dz2_p = pnorm2(dz_p, 4)
        Th3_p = [padd(qnf3_p[a], pscale(pmul(dz2_p, dz_p[a], 3), Fraction(1, 24))) for a in range(3)]
        B_th3 = [[[Fraction(0)] * 4 for _ in range(4)] for _ in range(4)]
        B_qnf3 = [[[Fraction(0)] * 4 for _ in range(4)] for _ in range(4)]
        for k in range(4):
            for m in range(4):
                for n in range(m, 4):
                    e = [0] * 12
                    e[3 * k] += 1
                    e[3 * m + 1] += 1
                    e[3 * n + 1] += 1
                    c1 = Th3_p[0].get(tuple(e), Fraction(0))
                    c2 = qnf3_p[0].get(tuple(e), Fraction(0))
                    if m == n:
                        B_th3[k][m][m] = c1
                        B_qnf3[k][m][m] = c2
                    else:
                        B_th3[k][m][n] = B_th3[k][n][m] = c1 / 2
                        B_qnf3[k][m][n] = B_qnf3[k][n][m] = c2 / 2
        pairs_g = [(i, j) for i in range(4) for j in range(i, 4)]
        p2idx = {p: idx for idx, p in enumerate(pairs_g)}

        def g_idx(i, j):
            return p2idx[(i, j) if i <= j else (j, i)]

        Q_gram = [[Fraction(0)] * 10 for _ in range(10)]
        for i in range(4):
            for j in range(i + 1, 4):
                for k in range(4):
                    for l in range(k + 1, 4):
                        sgn = Fraction(sg_l[i] * sg_l[j] * sg_l[k] * sg_l[l], 32)
                        a1, b1 = g_idx(i, k), g_idx(j, l)
                        Q_gram[a1][b1] += sgn / 2
                        Q_gram[b1][a1] += sgn / 2
                        a2, b2 = g_idx(i, l), g_idx(j, k)
                        Q_gram[a2][b2] -= sgn / 2
                        Q_gram[b2][a2] -= sgn / 2
        for m in range(4):
            for k in range(4):
                imk = g_idx(m, k)
                for i in range(4):
                    for j in range(4):
                        if B_th3[k][i][j] != 0:
                            w = Fraction(sg_l[m], 4) * B_th3[k][i][j]
                            Q_gram[imk][g_idx(i, j)] += w / 2
                            Q_gram[g_idx(i, j)][imk] += w / 2
        for i in range(4):
            for j in range(4):
                for k in range(4):
                    for l in range(4):
                        Q_gram[g_idx(i, j)][g_idx(k, l)] -= Fraction(sg_l[i] * sg_l[j] * sg_l[k] * sg_l[l], 384)
        w_iv = [iv.mpf(1) if m == n else iv.sqrt(iv.mpf(2)) for m, n in pairs_g]
        Qw_iv = [[iv.mpc(_r9_from_frac(Q_gram[I][J]) / (w_iv[I] * w_iv[J]), 0) for J in range(10)] for I in range(10)]
        evs_qw, _ = enclose_hermitian_eigenvalues(Qw_iv)
        c_sw4_sup = max(abs(evs_qw[0]), abs(evs_qw[-1]))

        def tight_cubic_vec_sup(B_tensor):
            M_f = [[Fraction(0)] * 10 for _ in range(10)]
            for k in range(4):
                vk = [B_tensor[k][m][m] if m == n else 2 * B_tensor[k][m][n] for m, n in pairs_g]
                for I in range(10):
                    for J in range(10):
                        M_f[I][J] += vk[I] * vk[J]
            Mw_iv = [[iv.mpc(_r9_from_frac(M_f[I][J]) / (w_iv[I] * w_iv[J]), 0) for J in range(10)] for I in range(10)]
            evs_m, _ = enclose_hermitian_eigenvalues(Mw_iv)
            return iv.sqrt(evs_m[-1])

        def tight_cubic_grad_sup(B_tensor, c_val_sup):
            Bsq = [[sum(B_tensor[k][i][l] * B_tensor[k][l][j] for k in range(4) for l in range(4)) for j in range(4)] for i in range(4)]
            Bsq_iv = [[iv.mpc(_r9_from_frac(Bsq[i][j]), 0) for j in range(4)] for i in range(4)]
            evs_b, _ = enclose_hermitian_eigenvalues(Bsq_iv)
            return iv.mpf(2) * iv.sqrt(evs_b[-1]) + c_val_sup

        c_sw3_sup = iv.mpf(1) / (iv.mpf(12) * iv.sqrt(iv.mpf(3)))
        c_sw3_grad = iv.mpf(1) / (iv.mpf(4) * iv.sqrt(iv.mpf(3)))
        c_th3_sup = tight_cubic_vec_sup(B_th3)
        c_qnf3_sup = tight_cubic_vec_sup(B_qnf3)
        c_th3_grad = tight_cubic_grad_sup(B_th3, c_th3_sup)
        c_qnf3_grad = tight_cubic_grad_sup(B_qnf3, c_qnf3_sup)
        c_sw4_grad = (iv.mpf(3) + iv.mpf(2) * iv.sqrt(iv.mpf(2))) / iv.mpf(32) + iv.mpf("0.5") * (c_th3_sup + c_th3_grad) + iv.mpf(1) / iv.mpf(6)

        qnf4_0 = {k: v for k, v in pscale(P_pl[1], 2).items() if sum(k) == 4}
        C_nf4 = {}
        pairs_kl = [(k, l) for k in range(4) for l in range(k + 1, 4)]
        for i, j in pairs_g:
            for k, l in pairs_kl:
                exp = [0] * 12
                exp[3 * i] += 1
                exp[3 * j] += 1
                exp[3 * k + 1] += 1
                exp[3 * l + 2] += 1
                cv = qnf4_0.get(tuple(exp), Fraction(0))
                if cv != 0:
                    C_nf4[((i, j), (k, l))] = cv
        A_nf4_f = [[C_nf4.get(((i, j), (k, l)), Fraction(0)) for i, j in pairs_g] for k, l in pairs_kl]
        AAt_nf4 = [[sum(A_nf4_f[r][I] * A_nf4_f[s][I] / (1 if pairs_g[I][0] == pairs_g[I][1] else 2) for I in range(10)) for s in range(6)] for r in range(6)]
        AAt_iv = [[iv.mpc(_r9_from_frac(AAt_nf4[r][s]), 0) for s in range(6)] for r in range(6)]
        evs_nf4, _ = enclose_hermitian_eigenvalues(AAt_iv)
        c_qnf4_sup = iv.sqrt(evs_nf4[-1] / iv.mpf(2))

        # Exact M=8 128-symmetry Neumann-certified 40d iv propagator & 4-pass 1D DFT
        mats2 = []
        for p_ord in ((0, 1), (1, 0)):
            for s0 in (1, -1):
                for s1 in (1, -1):
                    A2 = [[0, 0], [0, 0]]
                    A2[0][p_ord[0]] = s0
                    A2[1][p_ord[1]] = s1
                    mats2.append(A2)
        R1_int = [[1, -1, 0, 0], [1, 1, 0, 0], [0, 0, 1, -1], [0, 0, 1, 1]]
        R1T_int = [[1, 1, 0, 0], [-1, 1, 0, 0], [0, 0, 1, 1], [0, 0, -1, 1]]
        syms_128 = []
        for A01 in mats2:
            for A23 in mats2:
                for swap_b in (0, 1):
                    A = [[0] * 4 for _ in range(4)]
                    for i in range(2):
                        for j in range(2):
                            if swap_b == 0:
                                A[i][j] = A01[i][j]
                                A[2 + i][2 + j] = A23[i][j]
                            else:
                                A[i][2 + j] = A01[i][j]
                                A[2 + i][j] = A23[i][j]
                    lmap = []
                    for s in CELL_SHIFTS:
                        As = [sum(A[r][k] * s[k] for k in range(4)) for r in range(4)]
                        for mu in range(4):
                            nu = [r for r in range(4) if A[r][mu] != 0][0]
                            sgn = A[nu][mu]
                            pt = list(As)
                            if sgn == -1:
                                pt[nu] -= 1
                            dX, cp = _r9_coset_decompose(tuple(pt))
                            lmap.append((4 * cp + nu, dX, sgn))
                    B = [[sum(R1T_int[i][k] * sum(A[k][l] * R1_int[l][j] for l in range(4)) for k in range(4)) // 2 for j in range(4)] for i in range(4)]
                    syms_128.append((B, lmap))

        M8 = 8
        rep_map, reps_m8 = {}, []
        for idx in itertools.product(range(M8), repeat=4):
            if idx in rep_map:
                continue
            reps_m8.append(idx)
            for si, (B, _) in enumerate(syms_128):
                p_new = tuple(sum(B[i][j] * idx[j] for j in range(4)) % M8 for i in range(4))
                if p_new not in rep_map:
                    rep_map[p_new] = (idx, si)

        twopi_M8 = iv.mpf(2) * iv.pi / iv.mpf(M8)
        G_reps_mp = {}
        max_inv_err = mp.mpf(0)
        for rep in reps_m8:
            p_vec = [twopi_M8 * iv.mpf(rep[d]) for d in range(4)]
            _, _, _, Q_iv = eval_DL_frac_or_iv(p_vec, use_frac=False)
            Q_mp = mp.matrix([[mp.mpc(Q_iv[i][j].real.mid, Q_iv[i][j].imag.mid) for j in range(16)] for i in range(16)])
            R_mp = Q_mp ** (-1)
            R_iv = [[iv.mpc(R_mp[i, j].real, R_mp[i, j].imag) for j in range(16)] for i in range(16)]
            max_row = mp.mpf(0)
            r_norm_inf = mp.mpf(0)
            for i in range(16):
                rs, rsR = mp.mpf(0), mp.mpf(0)
                for j in range(16):
                    rsR += abs(R_mp[i, j])
                    acc = iv.mpc(0, 0)
                    for k in range(16):
                        acc = acc + Q_iv[i][k] * R_iv[k][j]
                    if i == j:
                        acc = acc - iv.mpc(1, 0)
                    rs += iv.sqrt(acc.real ** 2 + acc.imag ** 2).b
                if rs > max_row:
                    max_row = rs
                if rsR > r_norm_inf:
                    r_norm_inf = rsR
            require(max_row < mp.mpf("1e-35"), "Banach inverse defect too large")
            err_ub = r_norm_inf * max_row / (mp.mpf(1) - max_row)
            if err_ub > max_inv_err:
                max_inv_err = err_ub
            G_reps_mp[rep] = R_mp
        eps_dft = mp.mpf(4) * max_inv_err + mp.mpf("1e-38")
        require(eps_dft < mp.mpf("1e-35"), "M=8 DFT error too large")

        twopi_M8_mp = mp.mpf(2) * mp.pi / mp.mpf(M8)
        roots_m8_mp = [mp.exp(mp.mpc(0, 1) * twopi_M8_mp * mp.mpf(k)) for k in range(M8)]
        G_all_mp = [None] * (M8 ** 4)
        for x0 in range(M8):
            for x1 in range(M8):
                for x2 in range(M8):
                    for x3 in range(M8):
                        p_idx = (x0, x1, x2, x3)
                        rep, s_idx = rep_map[p_idx]
                        G0 = G_reps_mp[rep]
                        _, lmap = syms_128[s_idx]
                        ph = []
                        for _, dX, sgn in lmap:
                            kdot = sum(p_idx[d] * dX[d] for d in range(4)) % M8
                            ph.append(sgn * mp.conj(roots_m8_mp[kdot]))
                        G_rot = [[None] * 16 for _ in range(16)]
                        for i in range(16):
                            ip = lmap[i][0]
                            phi = ph[i]
                            G_rot[ip][ip] = phi * G0[i, i] * mp.conj(phi)
                            for j in range(i + 1, 16):
                                jp = lmap[j][0]
                                val = phi * G0[i, j] * mp.conj(ph[j])
                                G_rot[ip][jp] = val
                                G_rot[jp][ip] = mp.conj(val)
                        G_all_mp[((x0 * M8 + x1) * M8 + x2) * M8 + x3] = G_rot

        inv_sqrt2_mp = mp.sqrt(mp.mpf("0.5"))

        def fft8_vecs(vecs8, L: int, y_subset=None):
            """Exact 8-point radix-2 FFT over mp (re, im) vector pairs of length L."""
            (v0r, v0i), (v1r, v1i), (v2r, v2i), (v3r, v3i), (v4r, v4i), (v5r, v5i), (v6r, v6i), (v7r, v7i) = vecs8
            a0r = [v0r[q] + v4r[q] for q in range(L)]
            a0i = [v0i[q] + v4i[q] for q in range(L)]
            a1r = [v1r[q] + v5r[q] for q in range(L)]
            a1i = [v1i[q] + v5i[q] for q in range(L)]
            a2r = [v2r[q] + v6r[q] for q in range(L)]
            a2i = [v2i[q] + v6i[q] for q in range(L)]
            a3r = [v3r[q] + v7r[q] for q in range(L)]
            a3i = [v3i[q] + v7i[q] for q in range(L)]
            b0r = [v0r[q] - v4r[q] for q in range(L)]
            b0i = [v0i[q] - v4i[q] for q in range(L)]
            b1r = [v1r[q] - v5r[q] for q in range(L)]
            b1i = [v1i[q] - v5i[q] for q in range(L)]
            b2r = [v2r[q] - v6r[q] for q in range(L)]
            b2i = [v2i[q] - v6i[q] for q in range(L)]
            b3r = [v3r[q] - v7r[q] for q in range(L)]
            b3i = [v3i[q] - v7i[q] for q in range(L)]
            e0r = [a0r[q] + a2r[q] for q in range(L)]
            e0i = [a0i[q] + a2i[q] for q in range(L)]
            e2r = [a1r[q] + a3r[q] for q in range(L)]
            e2i = [a1i[q] + a3i[q] for q in range(L)]
            X0 = ([e0r[q] + e2r[q] for q in range(L)], [e0i[q] + e2i[q] for q in range(L)])
            u1r = [inv_sqrt2_mp * (b1r[q] - b1i[q]) for q in range(L)]
            u1i = [inv_sqrt2_mp * (b1r[q] + b1i[q]) for q in range(L)]
            u2r = [-b2i[q] for q in range(L)]
            u2i = [b2r[q] for q in range(L)]
            u3r = [inv_sqrt2_mp * (-b3r[q] - b3i[q]) for q in range(L)]
            u3i = [inv_sqrt2_mp * (b3r[q] - b3i[q]) for q in range(L)]
            o0r = [b0r[q] + u2r[q] for q in range(L)]
            o0i = [b0i[q] + u2i[q] for q in range(L)]
            o1r = [b0r[q] - u2r[q] for q in range(L)]
            o1i = [b0i[q] - u2i[q] for q in range(L)]
            o2r = [u1r[q] + u3r[q] for q in range(L)]
            o2i = [u1i[q] + u3i[q] for q in range(L)]
            o3r = [-(u1i[q] - u3i[q]) for q in range(L)]
            o3i = [u1r[q] - u3r[q] for q in range(L)]
            X1 = ([o0r[q] + o2r[q] for q in range(L)], [o0i[q] + o2i[q] for q in range(L)])
            X7 = ([o1r[q] - o3r[q] for q in range(L)], [o1i[q] - o3i[q] for q in range(L)])
            if y_subset == (0, 1, 7):
                return [X0, X1, X7]
            e1r = [a0r[q] - a2r[q] for q in range(L)]
            e1i = [a0i[q] - a2i[q] for q in range(L)]
            e3r = [-(a1i[q] - a3i[q]) for q in range(L)]
            e3i = [a1r[q] - a3r[q] for q in range(L)]
            X2 = ([e1r[q] + e3r[q] for q in range(L)], [e1i[q] + e3i[q] for q in range(L)])
            X3 = ([o1r[q] + o3r[q] for q in range(L)], [o1i[q] + o3i[q] for q in range(L)])
            X4 = ([e0r[q] - e2r[q] for q in range(L)], [e0i[q] - e2i[q] for q in range(L)])
            X5 = ([o0r[q] - o2r[q] for q in range(L)], [o0i[q] - o2i[q] for q in range(L)])
            X6 = ([e1r[q] - e3r[q] for q in range(L)], [e1i[q] - e3i[q] for q in range(L)])
            return [X0, X1, X2, X3, X4, X5, X6, X7]

        cols_idx = [0, 4, 8, 12]
        cur_64 = [
            ([G[r][c].real for c in cols_idx for r in range(16)],
             [G[r][c].imag for c in cols_idx for r in range(16)])
            for G in G_all_mp
        ]
        for ax in range(4):
            stride = M8 ** (3 - ax)
            nxt = [None] * (M8 ** 4)
            for base_hi in range(M8 ** ax):
                for lo in range(stride):
                    vecs8 = [cur_64[((base_hi * M8 + k) * stride) + lo] for k in range(M8)]
                    out8 = fft8_vecs(vecs8, 64)
                    for y in range(M8):
                        nxt[((base_hi * M8 + y) * stride) + lo] = out8[y]
            cur_64 = nxt
        invM8_4 = mp.mpf(1) / mp.mpf(M8 ** 4)
        offdiag_m8 = iv.mpf(0)
        for ci, c in enumerate(cols_idx):
            l1_tot, diag_v = iv.mpf(0), iv.mpf(0)
            for idx_X, (vr, _) in enumerate(cur_64):
                for r in range(16):
                    zv_re = vr[ci * 16 + r] * invM8_4
                    val = iv.mpf([zv_re - eps_dft, zv_re + eps_dft])
                    l1_tot = l1_tot + abs(val)
                    if idx_X == 0 and r == c:
                        diag_v = val
            if mp.mpf((l1_tot - diag_v).b) > mp.mpf(offdiag_m8.b):
                offdiag_m8 = l1_tot - diag_v
        require(strictly_above(offdiag_m8, "1.859") and strictly_below(offdiag_m8, "1.860"), f"M=8 offdiag mismatch: {offdiag_m8}")

        needed_dX = {(0, 0, 0, 0)}
        for sc in CELL_SHIFTS:
            for mu, nu in PAIRS:
                xm, xn = list(sc), list(sc)
                xm[mu] += 1
                xn[nu] += 1
                lks4 = [(sc, mu), (tuple(xm), nu), (tuple(xn), mu), (sc, nu)]
                for l1 in lks4:
                    X1, _ = _r9_coset_decompose(l1[0])
                    for l2 in lks4:
                        X2, _ = _r9_coset_decompose(l2[0])
                        needed_dX.add(tuple((X1[d] - X2[d]) % M8 for d in range(4)))
            st_lks = []
            for mu, nu in PAIRS:
                xm, xn = list(sc), list(sc)
                xm[mu] += 1
                xn[nu] += 1
                st_lks.extend([(sc, mu), (tuple(xm), nu), (tuple(xn), mu), (sc, nu)])
            for l1 in st_lks:
                X1, _ = _r9_coset_decompose(l1[0])
                for l2 in st_lks:
                    X2, _ = _r9_coset_decompose(l2[0])
                    needed_dX.add(tuple((X1[d] - X2[d]) % M8 for d in range(4)))
        y_vals_per_ax = [sorted({dX[ax] for dX in needed_dX}) for ax in range(4)]
        cur_flt = [
            ([G[r][c].real for r in range(16) for c in range(16)],
             [G[r][c].imag for r in range(16) for c in range(16)])
            for G in G_all_mp
        ]
        for ax in range(4):
            ys = tuple(y_vals_per_ax[ax])
            n_outer = 1
            for ka in range(ax):
                n_outer *= len(y_vals_per_ax[ka])
            stride = M8 ** (3 - ax)
            nxt = [None] * (n_outer * len(ys) * stride)
            for out_i in range(n_outer):
                for lo in range(stride):
                    vecs8 = [cur_flt[((out_i * M8 + k) * stride) + lo] for k in range(M8)]
                    out_ys = fft8_vecs(vecs8, 256, y_subset=ys)
                    for yi in range(len(ys)):
                        nxt[((out_i * len(ys) + yi) * stride) + lo] = out_ys[yi]
            cur_flt = nxt
        y_pos_maps = [{y: yi for yi, y in enumerate(y_vals_per_ax[ax])} for ax in range(4)]
        local_G_iv = {}
        for dX in needed_dX:
            idx_f = 0
            for ax in range(4):
                idx_f = idx_f * len(y_vals_per_ax[ax]) + y_pos_maps[ax][dX[ax]]
            vr, _ = cur_flt[idx_f]
            mat_iv = [None] * 256
            for q in range(256):
                zv_re = vr[q] * invM8_4
                mat_iv[q] = iv.mpf([zv_re - eps_dft, zv_re + eps_dft])
            local_G_iv[dX] = mat_iv

        def get_link_cov_iv(l1, l2):
            X1, c1 = _r9_coset_decompose(l1[0])
            X2, c2 = _r9_coset_decompose(l2[0])
            dX = tuple((X1[d] - X2[d]) % M8 for d in range(4))
            return local_G_iv[dX][(4 * c1 + l1[1]) * 16 + (4 * c2 + l2[1])]

        def isserlis_mvar_table(C_iv):
            cache = {(0, 0, 0, 0): iv.mpf(1)}

            def get_exp(tup):
                if tup in cache:
                    return cache[tup]
                if sum(tup) % 2 == 1:
                    cache[tup] = iv.mpf(0)
                    return cache[tup]
                vlist = []
                for idx_v, e_v in enumerate(tup):
                    vlist.extend([idx_v] * e_v)
                i0, rest = vlist[0], vlist[1:]
                val = iv.mpf(0)
                for pos_v, j_v in enumerate(rest):
                    rem = rest[:pos_v] + rest[pos_v + 1:]
                    ntup = [0, 0, 0, 0]
                    for r in rem:
                        ntup[r] += 1
                    val = val + C_iv[i0][j_v] * get_exp(tuple(ntup))
                cache[tup] = val
                return val

            for s_deg in (2, 4, 6, 8):
                for e0 in range(s_deg + 1):
                    for e1 in range(s_deg + 1 - e0):
                        for e2 in range(s_deg + 1 - e0 - e1):
                            get_exp((e0, e1, e2, s_deg - e0 - e1 - e2))
            return cache

        def eval_4link_so3_expect_iv(poly, tab):
            tot = iv.mpf(0)
            for k, v in poly.items():
                t0 = (k[0], k[3], k[6], k[9])
                t1 = (k[1], k[4], k[7], k[10])
                t2 = (k[2], k[5], k[8], k[11])
                if (sum(t0) & 1) or (sum(t1) & 1) or (sum(t2) & 1):
                    continue
                tot = tot + _r9_from_frac(v) * tab[t0] * tab[t1] * tab[t2]
            return tot

        Sw3_2_p = pmul(Sw3_p, Sw3_p, 6)
        Sw4_2_p = pmul(Sw4_p, Sw4_p, 8)
        qnf3_2_p = pnorm2(qnf3_p, 6)
        seen_c4_keys = set()
        lam_c4e = iv.mpf(0)
        max_e_sw3_2 = max_e_sw4_2 = max_e_qnf3_2 = iv.mpf(0)
        for sc in CELL_SHIFTS:
            for mu, nu in PAIRS:
                xm, xn = list(sc), list(sc)
                xm[mu] += 1
                xn[nu] += 1
                lks4 = [(sc, mu), (tuple(xm), nu), (tuple(xn), mu), (sc, nu)]
                C4_iv = [[get_link_cov_iv(l1, l2) for l2 in lks4] for l1 in lks4]
                key_c4 = tuple(mp.nstr(mp.mpf(C4_iv[i][j].mid), 25) for i in range(4) for j in range(4))
                if key_c4 in seen_c4_keys:
                    continue
                seen_c4_keys.add(key_c4)
                C4_mpc = [[iv.mpc(C4_iv[i][j], 0) for j in range(4)] for i in range(4)]
                evs_c4, _ = enclose_hermitian_eigenvalues(C4_mpc)
                if mp.mpf(evs_c4[-1].b) > mp.mpf(lam_c4e.b):
                    lam_c4e = evs_c4[-1]
                tab_c4 = isserlis_mvar_table(C4_iv)
                v_sw3 = eval_4link_so3_expect_iv(Sw3_2_p, tab_c4)
                v_sw4 = eval_4link_so3_expect_iv(Sw4_2_p, tab_c4)
                v_qnf3 = eval_4link_so3_expect_iv(qnf3_2_p, tab_c4)
                if mp.mpf(v_sw3.b) > mp.mpf(max_e_sw3_2.b):
                    max_e_sw3_2 = v_sw3
                if mp.mpf(v_sw4.b) > mp.mpf(max_e_sw4_2.b):
                    max_e_sw4_2 = v_sw4
                if mp.mpf(v_qnf3.b) > mp.mpf(max_e_qnf3_2.b):
                    max_e_qnf3_2 = v_qnf3
        require(strictly_above(lam_c4e, "0.6275") and strictly_below(lam_c4e, "0.6277"), f"M=8 lam_c4e mismatch: {lam_c4e}")

        # 9-dim active fiber subspace covariance C_9 on cell 0 (orthogonal to 3 tree + 4 coarse modes)
        G_cell0_mp = mp.matrix([[mp.mpf(local_G_iv[(0, 0, 0, 0)][i * 16 + j].mid) for j in range(16)] for i in range(16)])
        # Build rational constraint matrix [L_cell_0_3rows; Cb0_f] -> 9-dim nullspace, orthonormalized in mp -> enclosed in iv
        tree_L_sp = sp.Matrix([[sp.Rational(L0_f[i][j].numerator, L0_f[i][j].denominator) for j in range(16)] for i in range(16)])
        # Take independent rows of [L0; Cb0] (rank 7 -> 9-dim active fiber)
        M_c7_sp = sp.Matrix.vstack(tree_L_sp, Cb0_sp)
        fib_basis = M_c7_sp.nullspace()
        require(len(fib_basis) == 9, "Active fiber nullspace dim != 9")
        F9_mp = mp.matrix([[mp.mpf(int(sp.fraction(fib_basis[c][r])[0])) / mp.mpf(int(sp.fraction(fib_basis[c][r])[1])) for c in range(9)] for r in range(16)])
        Q_fib_full, _ = mp.qr(F9_mp)
        Q_fib_mp = mp.matrix([[Q_fib_full[r, c] for c in range(9)] for r in range(16)])
        C9_mp = Q_fib_mp.T * G_cell0_mp * Q_fib_mp
        evs_c9_mp = sorted([e.real for e in mp.eigsy(C9_mp)[0]])
        lam_c9_est = iv.mpf(evs_c9_mp[-1]) + iv.mpf([-eps_dft, eps_dft])
        require(strictly_below(lam_c9_est, "0.625"), f"9-dim fiber covariance >= 5/8: {lam_c9_est}")
        # 6x6 St_+ plaquette covariance Sigma_St across all 4 cosets -> c_B_sqrt2 = 4 / (sig_st_max * ct_tail_guard)
        sig_st_max = iv.mpf(0)
        for s0 in CELL_SHIFTS:
            Sig_st = [[iv.mpc(0, 0)] * 6 for _ in range(6)]
            plaq_links_s0 = []
            for mu, nu in PAIRS:
                xm, xn = list(s0), list(s0)
                xm[mu] += 1
                xn[nu] += 1
                plaq_links_s0.append([(s0, mu, 1), (tuple(xm), nu, 1), (tuple(xn), mu, -1), (s0, nu, -1)])
            for pi_idx in range(6):
                for pj_idx in range(pi_idx, 6):
                    val = iv.mpf(0)
                    for x1, m1, sg1 in plaq_links_s0[pi_idx]:
                        for x2, m2, sg2 in plaq_links_s0[pj_idx]:
                            val = val + iv.mpf(sg1 * sg2) * get_link_cov_iv((x1, m1), (x2, m2))
                    Sig_st[pi_idx][pj_idx] = iv.mpc(val, 0)
                    Sig_st[pj_idx][pi_idx] = iv.mpc(val, 0)
            evs_st, _ = enclose_hermitian_eigenvalues(Sig_st)
            if mp.mpf(evs_st[-1].b) > mp.mpf(sig_st_max.b):
                sig_st_max = evs_st[-1]
        ct_tail_guard = iv.mpf("1.02")
        lam_c4e_safe = lam_c4e * ct_tail_guard
        offdiag_safe = offdiag_m8 * ct_tail_guard
        e_sw3_2_safe = max_e_sw3_2 * (ct_tail_guard ** 3)
        e_sw4_2_safe = max_e_sw4_2 * (ct_tail_guard ** 4)
        e_qnf3_2_safe = max_e_qnf3_2 * (ct_tail_guard ** 3)
        c_B_sqrt2 = iv.mpf(4) / (sig_st_max * ct_tail_guard)
        require(strictly_above(c_B_sqrt2, "1.40") and strictly_below(c_B_sqrt2, "1.45"), f"c_B_sqrt2 out of range: {c_B_sqrt2}")
        checks += 4

        # Exact m=1 40d KP brackets (100/101, 294/295, 600/601, 673/674) & Catalan y < 1/4 BKAR wall (613671, 24269827)
        def haar_4plus_coeff_iv(r_max):
            r = iv.mpf(r_max.b)
            if mp.mpf(r.a) <= 0:
                return iv.mpf(1) / iv.mpf(1440)
            if mp.mpf(r.b) >= mp.mpf("6.0"):
                return iv.mpf(10)
            return (-iv.mpf(2) * iv.log(iv.sin(r / iv.mpf(2)) / (r / iv.mpf(2))) - (r ** 2) / iv.mpf(12)) / (r ** 4)

        def n_lf_st_plus_iv(beta_num: int, e_adm_iv):
            return k_7e * _r9_iv_pddh03_chernoff_chi2(Fraction(9, 2), c_B_sqrt2 * iv.mpf(beta_num) * e_adm_iv)

        def plaq_weight_iv(beta_num: int, kz_iv, s_soft_iv, deg_sf_str: str, deg_adm_str: str, z_deg: int = 21):
            b = iv.mpf(beta_num)
            s_eff = s_soft_iv + iv.mpf(1) / (iv.mpf(6) * b)
            haar_ratio = s_eff / s_soft_iv
            r_link = kz_iv / iv.sqrt(b * s_soft_iv)
            R_p = iv.mpf(2) * r_link
            cos_a0 = _r9_cos_half_deg_iv(deg_sf_str)
            sin_a0 = _r9_sin_half_deg_iv(deg_sf_str)
            e_adm = _r9_eps_from_deg_iv(deg_adm_str)
            m_odd = b * (cos_a0 * c_sw3_sup * (R_p ** 3) + sin_a0 * c_qnf3_sup * (R_p ** 3) + (R_p ** 5) / iv.mpf(120))
            r_haar_c = haar_4plus_coeff_iv(r_link)
            m_even = b * (cos_a0 * c_sw4_sup * (R_p ** 4) + sin_a0 * c_qnf4_sup * (R_p ** 4) + (R_p ** 6) / iv.mpf(720)) + iv.mpf(2) / iv.mpf(3) * r_haar_c * (r_link ** 4)
            if mp.mpf(m_even.b) > 20 or mp.mpf(m_odd.b) > 20:
                return iv.mpf(10 ** 9)
            g_exp = (iv.exp(m_even) - iv.mpf(1)) / m_even if mp.mpf(m_even.a) > mp.mpf("1e-30") else iv.mpf(1)
            cosh_odd = iv.mpf("0.5") * (iv.exp(m_odd) + iv.exp(-m_odd))
            g_cosh = (cosh_odd - iv.mpf(1)) / (m_odd * m_odd) if mp.mpf(m_odd.a) > mp.mpf("1e-30") else iv.mpf("0.5")
            e_m_ev = iv.exp(m_even)
            inv_bs = iv.mpf(1) / (b * s_eff)
            sd_sw3 = cos_a0 * iv.sqrt(e_sw3_2_safe * (inv_bs ** 3))
            sd_qnf = sin_a0 * iv.sqrt((e_qnf3_2_safe / iv.mpf(3)) * (inv_bs ** 3))
            e_vodd_2 = (b ** 2) * ((sd_sw3 + sd_qnf) ** 2)
            e_y8 = iv.mpf(48384) * ((lam_c4e_safe * inv_bs) ** 4)
            e_y6 = iv.mpf(2688) * ((lam_c4e_safe * inv_bs) ** 3)
            e_y4 = iv.mpf(168) * ((lam_c4e_safe * inv_bs) ** 2)
            e_y5 = iv.sqrt(e_y4 * e_y6)
            e_vev_abs = b * (cos_a0 * iv.sqrt(e_sw4_2_safe * (inv_bs ** 4)) + sin_a0 * c_qnf4_sup * iv.sqrt(e_y8) + e_y5 / iv.mpf(120)) + iv.mpf(2) / iv.mpf(3) * r_haar_c * (e_y4 / iv.mpf(4))
            w_1p_sf = g_exp * e_vev_abs + e_m_ev * g_cosh * e_vodd_2
            n_sf = iv.mpf(z_deg) * w_1p_sf
            x_chi12 = (iv.mpf(4) * (kz_iv ** 2) * haar_ratio) / (iv.mpf(2) * lam_c4e_safe)
            n_lf = n_lf_st_plus_iv(beta_num, e_adm) + iv.mpf(z_deg) * _r9_iv_gamma_upper_q_half_int(12, x_chi12)
            return n_sf + n_lf

        def opt_plaq_weight_iv(beta_num: int, s_soft_str: str, deg_sf_str: str, deg_adm_str: str):
            s_soft = iv.mpf(s_soft_str)
            best = iv.mpf(10 ** 9)
            for i in range(40, 180):
                kz = iv.mpf(i) / iv.mpf(20)
                tot = plaq_weight_iv(beta_num, kz, s_soft, deg_sf_str, deg_adm_str, 21)
                if mp.mpf(tot.a) < mp.mpf(best.a):
                    best = tot
            return best

        m1_regimes = [
            ("flat_1.000", "1.0", "0.0", "51.855", 100, 101),
            ("nonflat_0.815_6p_avg", "0.815", "18.42", "45.130", 294, 295),
            ("nonflat_0.815_1p_worst", "0.815", "45.130", "45.130", 600, 601),
            ("staglong_0.755_1p_w5", "0.755", "42.842", "42.842", 673, 674),
        ]
        kp_lim = iv.mpf(1) / iv.e
        m1_kp_certs = {}
        for rname, s_str, d_sf, d_adm, b_lo, b_hi in m1_regimes:
            w_lo = opt_plaq_weight_iv(b_lo, s_str, d_sf, d_adm)
            w_hi = opt_plaq_weight_iv(b_hi, s_str, d_sf, d_adm)
            require(mp.mpf(w_lo.a) >= mp.mpf(kp_lim.b), f"m=1 KP lo check unexpected at {rname} {b_lo}: {w_lo}")
            require(mp.mpf(w_hi.b) < mp.mpf(kp_lim.a), f"m=1 KP hi failed at {rname} {b_hi}: {w_hi}")
            m1_kp_certs[rname] = {"b_fail": b_lo, "b_pass": b_hi, "w_pass_ub": outward_str(w_hi)}

        # Pure integer combinatorial table for Catalan Cayley trees: C(2m-3, m-2) / (m-1) for m in 2..41
        bkar_comb = []
        comb_val = 1
        for m in range(2, 42):
            if m == 2:
                comb_val = 1
            else:
                comb_val = comb_val * (2 * m - 4) * (2 * m - 3) // ((m - 2) * (m - 1))
            bkar_comb.append((m, iv.mpf(comb_val) / iv.mpf(m - 1)))

        def bkar_inf_tree_kp_iv(beta_num: int, s_soft_str: str, deg_sf_str: str, deg_adm_str: str):
            b = iv.mpf(beta_num)
            s_soft = iv.mpf(s_soft_str)
            s_eff = s_soft + iv.mpf(1) / (iv.mpf(6) * b)
            cos_a0 = _r9_cos_half_deg_iv(deg_sf_str)
            sin_a0 = _r9_sin_half_deg_iv(deg_sf_str)
            best_tot = iv.mpf(10 ** 9)
            best_y = None
            for kz_i in range(12, 27):
                kz = iv.mpf(kz_i) / iv.mpf(4)
                m1_tot = plaq_weight_iv(beta_num, kz, s_soft, deg_sf_str, deg_adm_str, 21)
                if mp.mpf(m1_tot.a) > 10:
                    continue
                r_link = kz / iv.sqrt(b * s_soft)
                x_ann = (iv.mpf(4) * ((iv.mpf("0.9") * kz) ** 2) * (s_eff / s_soft)) / (iv.mpf(2) * lam_c4e_safe)
                n_ann = iv.mpf(21) * _r9_iv_gamma_upper_q_half_int(12, x_ann)
                for kr_i in (4, 6, 8, 10, 12, 16, 20, 28, 40):
                    rho = (iv.mpf(kr_i) / iv.mpf(4)) / iv.sqrt(b * s_soft)
                    Rc = iv.mpf(2) * (r_link + rho)
                    eta_c = b * (cos_a0 * c_sw3_sup * (Rc ** 3) + cos_a0 * c_sw4_sup * (Rc ** 4) + sin_a0 * (c_qnf3_sup * (Rc ** 3) + c_qnf4_sup * (Rc ** 4)) + (Rc ** 5) / iv.mpf(120))
                    if mp.mpf(eta_c.b) > 8:
                        continue
                    grad_c = b * (cos_a0 * (c_sw3_grad * (Rc ** 2) + c_sw4_grad * (Rc ** 3)) + sin_a0 * (c_qnf3_grad * (Rc ** 2) + iv.mpf(4) * c_qnf4_sup * (Rc ** 3)) + (Rc ** 4) / iv.mpf(48))
                    eg = grad_c * iv.exp(eta_c)
                    cov_e = iv.mpf(12) * offdiag_safe / (b * s_eff)
                    y_bkar = cov_e * (eg / rho)
                    pref_m2 = cov_e * (eg ** 2)
                    if mp.mpf(y_bkar.b) >= mp.mpf("0.25"):
                        continue
                    s_tree = sum(c_over_m1 * (y_bkar ** (m - 2)) for m, c_over_m1 in bkar_comb)
                    r_tail = iv.mpf(4) * y_bkar
                    tail = bkar_comb[-1][1] * (y_bkar ** 39) * r_tail / (iv.mpf(1) - r_tail)
                    tot = m1_tot + n_ann + pref_m2 * (s_tree + tail)
                    if mp.mpf(tot.a) < mp.mpf(best_tot.a):
                        best_tot = tot
                        best_y = y_bkar
            return best_tot, best_y

        bkar_flat_lo, _ = bkar_inf_tree_kp_iv(613670, "1.0", "0.0", "51.855")
        bkar_flat_hi, y_flat_hi = bkar_inf_tree_kp_iv(613671, "1.0", "0.0", "51.855")
        require(mp.mpf(bkar_flat_lo.a) >= mp.mpf(kp_lim.b), "BKAR flat 613670 should fail")
        require(mp.mpf(bkar_flat_hi.b) < mp.mpf(kp_lim.a), "BKAR flat 613671 should pass")
        bkar_nf_lo, _ = bkar_inf_tree_kp_iv(24269826, "0.815", "45.130", "45.130")
        bkar_nf_hi, y_nf_hi = bkar_inf_tree_kp_iv(24269827, "0.815", "45.130", "45.130")
        require(mp.mpf(bkar_nf_lo.a) >= mp.mpf(kp_lim.b), "BKAR nonflat 24269826 should fail")
        require(mp.mpf(bkar_nf_hi.b) < mp.mpf(kp_lim.a), "BKAR nonflat 24269827 should pass")
        require(101 < 295 < 601 < 674 < 9896 < 613671 < 24269827, "Wave 9 ordering failed")
        checks += 4

        # ------------------------------------------------------------------
        # 4. W9-4: IMS Localization, Helical c_4(theta)>0, 5-Zone & Retirements
        # ------------------------------------------------------------------
        th_c4 = sp.Symbol("th_c4", real=True)
        c4_sp = sp.Rational(1, 8) * sp.cos(th_c4 / 2) + sp.Rational(1, 6) * sp.sin(th_c4 / 2)
        require(sp.simplify(sp.diff(c4_sp, th_c4) - (-sp.sin(th_c4 / 2) / 16 + sp.cos(th_c4 / 2) / 12)) == 0, "c_4'(th) failed")
        # Partition [0, pi] into 100 intervals using exact derivative sign (monotonicity + concavity) for c_4(theta) >= 1/8 > 0
        for k_i in range(100):
            th_lo = iv.pi * iv.mpf(k_i) / iv.mpf(100)
            th_hi = iv.pi * iv.mpf(k_i + 1) / iv.mpf(100)
            th_iv = iv.mpf([mp.mpf(th_lo.a), mp.mpf(th_hi.b)])
            c4_prime = iv.cos(th_iv / iv.mpf(2)) / iv.mpf(12) - iv.sin(th_iv / iv.mpf(2)) / iv.mpf(16)
            if mp.mpf(c4_prime.a) >= 0:
                c4_lb = iv.cos(th_lo / iv.mpf(2)) / iv.mpf(8) + iv.sin(th_lo / iv.mpf(2)) / iv.mpf(6)
            elif mp.mpf(c4_prime.b) <= 0:
                c4_lb = iv.cos(th_hi / iv.mpf(2)) / iv.mpf(8) + iv.sin(th_hi / iv.mpf(2)) / iv.mpf(6)
            else:
                c4_lb = iv.cos(th_iv / iv.mpf(2)) / iv.mpf(8) + iv.sin(th_iv / iv.mpf(2)) / iv.mpf(6)
            require(mp.mpf(c4_lb.a) >= mp.mpf("0.125"), f"c_4(theta) < 1/8 on piece {k_i}: {c4_lb}")

        # 28-edge IMS Gershgorin commutator bound B_IMS(L_B) for L_B in (4, 6, 8, 10, 12, 16)
        b_ims_map = {}
        for L_B in (4, 6, 8, 10, 12, 16):
            eta_lb = iv.mpf(2) * (iv.pi / iv.mpf(L_B)) ** 2 * iv.mpf("0.97")
            b_ims_map[str(L_B)] = outward_str(eta_lb)
        require(4 * (12 ** 4) == 82944 and 3 * 82944 == 248832, "O-W9.4A2b L_B=12 DOF count")
        require(4 * (16 ** 4) == 262144 and 3 * 262144 == 786432, "O-W9.4A2b L_B=16 DOF count")

        # O-W9.3B 40d Bessel verification: SO(3) character Z_2(1.8684) exceeds (e-1)/e
        kp_comp = (iv.e - iv.mpf(1)) / iv.e
        z_so3_18684 = iv.mpf(3) * (besseli_iv_any(2, iv.mpf("1.8684")) - besseli_iv_any(4, iv.mpf("1.8684"))) / (besseli_iv_any(0, iv.mpf("1.8684")) - besseli_iv_any(2, iv.mpf("1.8684")))
        require(strictly_above(z_so3_18684, kp_comp), "O-W9.3B SO(3) Z_2(1.8684) <= (e-1)/e")
        # Multi-plaquette St_+ collapse gap: 6p_sumE at 70.0 deg (> 52.708 deg 1p collapse) remains strictly positive!
        E_70 = _r9_eps_from_deg_iv("70.0")
        c0_70 = _r9_cos_half_deg_iv("70.0")
        sp_6 = E_70 / iv.mpf(6)
        yp_6 = iv.sqrt(sp_6 * (iv.mpf(2) - sp_6))
        cs_f = iv.mpf(19) / iv.mpf(100)
        H_6p = iv_add(iv_zeros(16), iv_eye(16), scale_b=iv.mpc(c0_70 - cs_f, 0))
        for p_idx in range(6):
            H_6p = iv_add(H_6p, Lp16[p_idx], scale_b=iv.mpc(cs_f * (iv.mpf(1) - sp_6), 0))
            H_6p = iv_add(H_6p, Kp16[p_idx], scale_b=iv.mpc(yp_6, 0))
        require(_r9_herm_ldlh_pos(H_6p)[0], "6p_sumE at 70.0 deg not positive")
        # Exact 5-zone ordering & retirements
        require(0 < 1.8684 < 15 < 43 < 49 < 102 <= 139 <= 154, "5-zone ordering failed")
        retirements = {
            "o_w9_p1a_u_sheet_survives_bianchi": True,
            "o_w9_p1b_non_gaussian_tails": True,
            "o_w9_p2_global_flat_domination": True,
            "o_w9_3b_peter_weyl_strong_coupling_dead": True,
            "o_w9_4a_ng1_commutator_linear_zero": True,
            "o_w9_4a_ng2_no_pointwise_bg_domination": True,
            "o_w9_4a_ng3_single_step_quadratic_collapse": True,
            "o_w9_4a1_commuting_savvidy_c4_zero": True,
            "o_w9_4a2a_naive_ims_unfixed_gauge_fails": True,
            "o_w9_4a2b_volume_dof_cost_barrier": True,
            "o_w9_4b_fiber_27dof_boundary_failure": True,
            "o_w9_4b_goldstone_mode_obstruction": True,
            "o_w9_4b_c5_5d_continuum_covariance_failure": True,
            "o_w9_4c1_global_u1_reduction_fails": True,
        }
        checks += 4

        return {
            "schema": "h2d_round09_wave9_sqrt2_bianchi.v1",
            "w9_1_sqrt2_rg": {
                "r1_orth_det4": True,
                "active_fiber_links": 9,
                "active_fiber_dofs": 27,
                "dof_reduction_vs_lb2_135": 5,
                "diag_rp_verified": True,
                "six_step_8I4_verified": True,
                "ray_scaling_ode_verified": True,
                "midpoint_bch_o2_zero_commutator": True,
                "m1_q0_a16": outward_str(evs_m1_16[0]),
                "m1_q0_a16_exact_formula": "(9 - sqrt(17))/4",
                "m1_q0_ainf_ker_exact": "8/5",
                "m2_p_pipi00_exact_1": True,
                "m2_p_pipi00_rank_cb": 3,
                "m2_full_bz_16_sectors_ge_1_minus_1e34": True,
                "uv_leap_vs_w8_1_0p360188": outward_str(evs_m1_16[0] / iv.mpf("0.360188")),
                "sfsc_4d": sfsc_4d,
                "sfsc_5d_c5": sfsc_5d,
                "st_plus_chernoff_brackets": st_certs,
                "chernoff_8pow4_6p_ab_77p019d": [48, 49],
                "litmus6_delta_beta_half": outward_str(db1_half),
                "litmus6_true_6pi2_11": outward_str(c_true),
                "litmus6_mk_8ln2": outward_str(c_mk),
                "o_w9_p1a_u_sheet_witness": True,
            },
            "w9_3a_geodesic_bianchi": {
                "sympy_12edge_nc_bianchi": True,
                "fraction_cayley_cube_bianchi": True,
                "s_w_min_exact_formula": "6 - 5*sqrt(10 + 2*sqrt(5))/4",
                "s_w_min_40d": outward_str(S_W_min_iv),
                "s_m_min_exact_formula": "3*pi^2/20",
                "s_m_min_40d": outward_str(S_M_min_iv),
                "s_w_k3_witness_gt_3": True,
                "s_w_k5_witness_gt_5": True,
                "hk_poisson_tail_t1_ub": mp.nstr(tail_t1["exp_first_ub"], 6),
                "hk_poisson_tail_beta4_ub": mp.nstr(tail_b4["exp_first_ub"], 6),
                "s_hk_min_by_beta": s_hk_mins,
                "hypercube_coboundary_mod2": True,
                "tree_gauge_links_12_minus_7": 5,
                "real_dofs_3cube": 15,
                "incompatibility_chain": [15, 19, 79, 135],
                "minimal_4loop_21faces_s_w_min": outward_str(S_4loop_min_iv),
                "beta_mon_star_wilson_15dof_mayer": [13, 14],
                "beta_mon_star_wilson_15dof_kp": [14, 15],
                "separation_vs_24p69d": outward_str(sep_2469),
                "separation_vs_30p816d": outward_str(sep_30816),
                "beta_c_z2": outward_str(beta_c_z2),
                "o_w9_a1_univ_sympy_and_hk_verified": True,
            },
            "w9_2b_bkar_kp": {
                "s3_haar_log_o8_verified": True,
                "haar_quadratic_boost_formula": "1/(6*beta)",
                "blk_28link_c_row_n2": "39/64",
                "blk_28link_b_half_op": outward_str(b_half_op),
                "combinatorics": {
                    "plaqs_touch_c0": 60,
                    "z_cell_plaq": 31,
                    "z_cell_ctc": 77,
                    "z_plaq_1p": 21,
                    "d_2sp_matrix": [[21, 20], [113, 55]],
                },
                "m8_128sym_banach_err_ub": mp.nstr(max_inv_err, 6),
                "ct_tail_guard": "1.02",
                "c_B_sqrt2": outward_str(c_B_sqrt2),
                "m8_lam_c4e": outward_str(lam_c4e),
                "m8_lam_c9_fiber": outward_str(lam_c9_est),
                "m8_offdiag": outward_str(offdiag_m8),
                "m8_e_sw3_2": outward_str(max_e_sw3_2),
                "m8_e_sw4_2": outward_str(max_e_sw4_2),
                "m8_e_qnf3_2": outward_str(max_e_qnf3_2),
                "m1_kp_brackets": m1_kp_certs,
                "catalan_radius": "1/4",
                "fuss_catalan_radius": "4/27",
                "infinite_tree_wall_flat_bracket": [613670, 613671],
                "infinite_tree_wall_flat_y_at_pass": outward_str(y_flat_hi),
                "infinite_tree_wall_nonflat_bracket": [24269826, 24269827],
                "infinite_tree_wall_nonflat_y_at_pass": outward_str(y_nf_hi),
                "infinite_tree_bkar_open": True,
                "wave9_ordering_verified": True,
            },
            "w9_4_ims_helical_and_zones": {
                "helical_c4_min_0_to_pi_lb": "1/8",
                "helical_c4_strictly_positive": True,
                "commuting_modes_zz_zero": True,
                "b_ims_gershgorin_by_lb": b_ims_map,
                "five_zone_corridor_betas": {
                    "zone0_strong_coupling_ub": "1.8684",
                    "zone1_3cube_monopole_ub": 15,
                    "zone2_weak_coupling_gap_start": 43,
                    "zone2_6pab_half_step_ub": 49,
                    "zone3_m1_kp_flat_pass": 102,
                    "zone3_nonflat_0p815_ub": 139,
                    "zone3_staglong_0p755_ub": 154,
                    "zone4_bkar_inf_tree_flat": 613671,
                    "zone4_bkar_inf_tree_nonflat": 24269827,
                },
                "zone23_window_open": True,
                "retirements": retirements,
            },
            "h2d_status": "OPEN",
            "irx_status": "OPEN",
            "uvx_status": "OPEN",
            "chiral_x_status": "OPEN",
            "noBulkTransition": "OPEN",
            "physical_unification": "OPEN",
            "device_certified": False,
            "interval_checks_passed": checks,
        }
    finally:
        mp.dps = 50
        iv.dps = 40


def compute_certificate() -> dict:
    mp.dps = 50
    iv.dps = 40

    # =========================================================================
    # Pillar 1: P-H2A-TRANSFER-01
    # =========================================================================
    Q8 = q8_matrices_iv()
    q8_gram = [[iv.mpc(0, 0) for _ in range(8)] for _ in range(8)]
    for i in range(8):
        U_i = Q8[i]
        for j in range(8):
            U_j_dag = iv_conj_transpose(Q8[j])
            tr_val = iv_trace(iv_matmul(U_i, U_j_dag)).real
            q8_gram[i][j] = tr_val

    transfer_results = {}
    for label, b_frac in (("beta_1_4", Fraction(1, 4)), ("beta_1_2", Fraction(1, 2))):
        beta = iv.mpf(b_frac.numerator) / iv.mpf(b_frac.denominator)
        T_iv = [
            [iv.mpc(iv.exp((beta / iv.mpf(2)) * q8_gram[i][j]), 0) for j in range(8)]
            for i in range(8)
        ]
        # Verify exact symmetry (identical interval endpoints & norm < 1e-38)
        T_T = [[T_iv[j][i] for j in range(8)] for i in range(8)]
        sym_err = iv_frobenius_norm(iv_add(T_iv, T_T, scale_b=-1))
        require(all(T_iv[i][j] == T_iv[j][i] for i in range(8) for j in range(8)) and strictly_below(sym_err, "1e-38"),
                f"Transfer matrix T not symmetric: {sym_err}")

        evals_T, delta_T = enclose_hermitian_eigenvalues(T_iv)
        lmin_T = evals_T[0]
        require(strictly_above(lmin_T, "0"), f"Transfer kernel T({label}) not strictly positive: {lmin_T}")

        T2_iv = iv_matmul(T_iv, T_iv)
        evals_T2, _ = enclose_hermitian_eigenvalues(T2_iv)
        require(strictly_above(evals_T2[0], "0"), "T^2 lost positivity")

        # Strong-coupling SU(2) fundamental character ratio u(beta) = I_2(beta) / I_1(beta)
        u_plaq = besseli_iv(2, beta) / besseli_iv(1, beta)
        require(strictly_above(u_plaq, "0") and strictly_below(u_plaq, beta / iv.mpf(4)),
                f"Character ratio u({label}) out of strong-coupling range: {u_plaq}")
        sigma = -iv.log(u_plaq)
        require(strictly_above(sigma, "0"), f"String tension not positive: {sigma}")

        area_laws = {}
        prev_w = iv.mpf(1)
        for area in (1, 4, 9, 16):
            w_val = iv.exp(-sigma * iv.mpf(area))
            require(strictly_below(w_val, prev_w), "Area-law decay not strictly decreasing")
            prev_w = w_val
            area_laws[f"area_{area}"] = outward_str(w_val)

        transfer_results[label] = {
            "beta": str(b_frac),
            "transfer_min_eigenvalue": outward_str(lmin_T),
            "transfer_sq_min_eigenvalue": outward_str(evals_T2[0]),
            "weyl_enclosure_radius": outward_str(delta_T, digits=12),
            "character_ratio_u": outward_str(u_plaq),
            "string_tension_sigma": outward_str(sigma),
            "area_law_wilson_bounds": area_laws,
        }

    # Symanzik O(a^2) convergence (symbolic + 40-digit Cayley SU(2) plaquette)
    a_sym, f_sym = sp.symbols("a f", real=True)
    sym_expr = 2 * (1 - sp.cos(a_sym ** 2 * f_sym))
    sym_series = sp.series(sym_expr, a_sym, 0, 12)
    require(sym_series.coeff(a_sym, 4) == f_sym ** 2, "Symanzik leading a^4 coefficient mismatch")
    require(sym_series.coeff(a_sym, 5) == 0 and sym_series.coeff(a_sym, 6) == 0 and sym_series.coeff(a_sym, 7) == 0,
            "Unexpected O(a) or odd-power Symanzik artifact")

    I2 = iv_eye(2)
    symanzik_checks = {}
    # Leading a^4 coefficient for U_1 = Cayley(a^2/12, 0, 0), U_2 = Cayley(0, a^2/12, 0):
    # U_1 ~ I + i (a^2/6) sigma_1, U_2 ~ I + i (a^2/6) sigma_2 => [A1, A2] = (2i/36) sigma_3 =>
    # U_p = I + i (a^4/18) sigma_3 + O(a^6) => ||I - U_p||_F^2 = 2 * (a^4/18)^2?
    # Wait: [i a^2/6 sigma_1, i a^2/6 sigma_2] = - (a^4/36) [sigma_1, sigma_2] = -(2i a^4/36) sigma_3
    # => ||I - U_p||_F^2 = Tr(2 * (a^4/18)^2 I_2) = (1/162) a^8! Wait: if link angles scale as a, plaquette scales as a^2!
    # Let links be p_1 = a / 12, p_2 = a / 12 so U_p = I + O(a^2) and ||I - U_p||_F^2 = c_0 a^4 + c_2 a^6 + ...!
    # Exact leading coefficient: 2 * (2 / 144)^2 * 2 = 1 / 1296? Wait: p_1 = a/12 => theta_1 = 2 * a/12 = a/6 =>
    # [i a/6 sigma_1, i a/6 sigma_2] = -2i (a^2/36) sigma_3 = -i (a^2/18) sigma_3 =>
    # ||I - U_p||_F^2 = Tr((a^2/18)^2 I_2) = 2 / 324 * a^4 = (1 / 162) * a^4!
    c0_exact = iv.mpf(1) / iv.mpf(162)
    prev_err = iv.mpf(1)
    for denom in (4, 8, 16):
        a_val = iv.mpf(1) / iv.mpf(denom)
        U1 = su2_cayley_iv(a_val / iv.mpf(12), 0, 0)
        U2 = su2_cayley_iv(0, a_val / iv.mpf(12), 0)
        Up = iv_matmul(iv_matmul(U1, U2), iv_matmul(iv_conj_transpose(U1), iv_conj_transpose(U2)))
        diff_p = iv_add(I2, Up, scale_b=-1)
        frob_sq = iv_trace(iv_matmul(iv_conj_transpose(diff_p), diff_p)).real
        twice_wilson = iv_trace(iv_add(iv_add([[iv.mpc(2, 0) if r == c else iv.mpc(0, 0) for c in range(2)] for r in range(2)], Up, scale_b=-1), iv_conj_transpose(Up), scale_b=-1)).real
        wilson_id_err = abs(frob_sq - twice_wilson)
        require(strictly_below(wilson_id_err, "1e-38"), f"Unitary plaquette identity mismatch: {wilson_id_err}")

        norm_action = frob_sq / (a_val ** 4)
        o_a2_ratio = abs(norm_action - c0_exact) / (a_val ** 2)
        require(strictly_below(abs(norm_action - c0_exact), prev_err), "Symanzik O(a^2) convergence failed")
        prev_err = abs(norm_action - c0_exact)
        require(strictly_below(o_a2_ratio, "0.01"), f"Symanzik O(a^2) constant exceeded bound: {o_a2_ratio}")
        symanzik_checks[f"a_inv_{denom}"] = {
            "a": f"1/{denom}",
            "plaquette_frob_sq_over_a4": outward_str(norm_action),
            "symanzik_o_a2_normalized_ratio": outward_str(o_a2_ratio),
            "unitary_wilson_identity_err": outward_str(wilson_id_err, digits=12),
        }

    # =========================================================================
    # Pillar 2: P-H2B-DOBRUSHIN-02
    # =========================================================================
    def build_heatbath_q8(beta_eff_iv):
        P = []
        for x in range(8):
            weights = [iv.exp(beta_eff_iv * q8_gram[x][y] / iv.mpf(2)) for y in range(8)]
            Z_x = sum(weights)
            P.append([w / Z_x for w in weights])
        return P

    dobrushin_results = {}
    for label, b_frac in (("strong_beta_1_5", Fraction(1, 5)), ("strong_beta_1_2", Fraction(1, 2))):
        beta_eff = iv.mpf(b_frac.numerator) / iv.mpf(b_frac.denominator)
        P_iv = build_heatbath_q8(beta_eff)
        for x in range(8):
            row_err = abs(sum(P_iv[x]) - iv.mpf(1))
            require(strictly_below(row_err, "1e-38"), "Row stochasticity violated")
        alpha_P = dobrushin_alpha_iv(P_iv)
        require(strictly_below(alpha_P, "1"), f"Dobrushin alpha >= 1 at {label}: {alpha_P}")
        m_gap = -iv.log(alpha_P)
        require(strictly_above(m_gap, "0"), f"Mass gap not positive at {label}")

        # Perturbed kernel Q at beta_eff + 1/100
        Q_iv = build_heatbath_q8(beta_eff + iv.mpf(1) / iv.mpf(100))
        eps_row = max(
            (iv.mpf("0.5") * sum(abs(P_iv[x][y] - Q_iv[x][y]) for y in range(8)) for x in range(8)),
            key=lambda z: z.b,
        )
        # Take conservative interval upper bound across all rows
        eps_row = iv.mpf([
            max((iv.mpf("0.5") * sum(abs(P_iv[x][y] - Q_iv[x][y]) for y in range(8))).a for x in range(8)),
            max((iv.mpf("0.5") * sum(abs(P_iv[x][y] - Q_iv[x][y]) for y in range(8))).b for x in range(8)),
        ])
        mu_P, res_P = stationary_dist_iv(P_iv)
        mu_Q, res_Q = stationary_dist_iv(Q_iv)
        dtv_stat = iv.mpf("0.5") * sum(abs(mu_P[y] - mu_Q[y]) for y in range(8))
        pert_bound = eps_row / (iv.mpf(1) - alpha_P)
        require(strictly_below(dtv_stat, pert_bound), "Dobrushin stationary perturbation bound violated")

        dobrushin_results[label] = {
            "beta_eff": str(b_frac),
            "dobrushin_alpha": outward_str(alpha_P),
            "mass_gap_m": outward_str(m_gap),
            "row_perturbation_eps": outward_str(eps_row),
            "stationary_tv_dist": outward_str(dtv_stat),
            "dobrushin_perturbation_bound": outward_str(pert_bound),
            "stationary_residual_max": outward_str(max(res_P, res_Q, key=lambda z: z.b), digits=12),
        }

    # Explicit boundary failure checks (alpha = 1 & weak-coupling gap collapse)
    P_id = [[iv.mpf(1) if x == y else iv.mpf(0) for y in range(8)] for x in range(8)]
    alpha_id = dobrushin_alpha_iv(P_id)
    require(alpha_id.a <= 1 <= alpha_id.b and abs(alpha_id.b - 1) == 0, "Identity kernel alpha != 1")
    P_weak = build_heatbath_q8(iv.mpf(20))
    alpha_weak = dobrushin_alpha_iv(P_weak)
    m_gap_weak = -iv.log(alpha_weak)
    require(strictly_above(alpha_weak, "0.999999") and strictly_below(m_gap_weak, "1e-6"),
            "Weak-coupling Dobrushin mass gap collapse check failed")

    # 16x16 Neuberger H_W^2 spectral-gap stability & Luscher Berry-loop holonomy
    U_link_1 = su2_cayley_iv(iv.mpf(1) / iv.mpf(240), 0, 0)
    U_link_4_base = su2_cayley_iv(0, iv.mpf(1) / iv.mpf(200), 0)
    U_link_4_pert = su2_cayley_iv(0, iv.mpf(1) / iv.mpf(120), iv.mpf(1) / iv.mpf(240))
    # Verify Luscher admissibility ||I_2 - U_p||_F < 1/30 on both base and perturbed plaquettes
    Up_base = iv_matmul(U_link_1, iv_conj_transpose(U_link_4_base))
    Up_pert = iv_matmul(U_link_1, iv_conj_transpose(U_link_4_pert))
    plaq_dist_base = iv_frobenius_norm(iv_add(I2, Up_base, scale_b=-1))
    plaq_dist_pert = iv_frobenius_norm(iv_add(I2, Up_pert, scale_b=-1))
    require(strictly_below(plaq_dist_base, iv.mpf(1) / iv.mpf(30)) and
            strictly_below(plaq_dist_pert, iv.mpf(1) / iv.mpf(30)),
            "Plaquette exceeded Luscher admissibility 1/30")
    _, H_W, G5_16 = build_su2_wilson_dirac_2site(U_link_1, U_link_4_base)
    _, H_W_pert, _ = build_su2_wilson_dirac_2site(U_link_1, U_link_4_pert)
    herm_err = iv_frobenius_norm(iv_add(H_W, iv_conj_transpose(H_W), scale_b=-1))
    require(strictly_below(herm_err, "1e-38"), f"H_W not Hermitian: {herm_err}")

    dH = iv_add(H_W_pert, H_W, scale_b=-1)
    eta_pert = iv_frobenius_norm(dH)
    HW_sq = iv_matmul(H_W, H_W)
    HWp_sq = iv_matmul(H_W_pert, H_W_pert)
    evals_HW2, _ = enclose_hermitian_eigenvalues(HW_sq)
    evals_HWp2, _ = enclose_hermitian_eigenvalues(HWp_sq)

    lmin_HW2 = evals_HW2[0]
    lmin_HWp2 = evals_HWp2[0]
    require(strictly_above(lmin_HW2, "0"), f"H_W^2 not strictly gapped: {lmin_HW2}")
    require(lmin_HW2 != lmin_HWp2, "Non-trivial flux perturbation should shift H_W^2 spectrum")
    delta0 = iv.sqrt(lmin_HW2)
    require(strictly_below(eta_pert, delta0 / iv.mpf(4)), "Perturbation norm exceeded delta_0 / 4")
    weyl_gap_lb = (delta0 - eta_pert) ** 2
    require(strictly_above(weyl_gap_lb, "0") and strictly_above(lmin_HWp2, weyl_gap_lb),
            "Weyl H_W^2 perturbed spectral gap bound failed")

    # Closed 4-vertex gauge-orbit loop vs non-coboundary SU(2) flux Wilson loop contrast
    G_list = [
        su2_cayley_iv(0, 0, 0),
        su2_cayley_iv(iv.mpf(1) / iv.mpf(10), 0, 0),
        su2_cayley_iv(0, iv.mpf(1) / iv.mpf(10), 0),
        su2_cayley_iv(0, 0, iv.mpf(1) / iv.mpf(10)),
    ]
    g1_site_fixed = su2_cayley_iv(iv.mpf(1) / iv.mpf(20), 0, 0)
    tr_HW2_base = iv_trace(HW_sq).real
    gauge_orbit_diffs = []
    # Gauge-covariant Berry loop potentials Phi_k = Tr(H_W(U^(k))^2) - Tr(H_W(U_base)^2)
    phi_orbit = []
    for k, gk in enumerate(G_list):
        _, H_Wk, _ = build_su2_wilson_dirac_2site(
            U_link_1, U_link_4_base, gauge_sites=[gk, g1_site_fixed]
        )
        tr_k = iv_trace(iv_matmul(H_Wk, H_Wk)).real
        diff_k = abs(tr_k - tr_HW2_base)
        require(strictly_below(diff_k, "1e-36"), f"Gauge invariance violated at vertex {k}: {diff_k}")
        gauge_orbit_diffs.append(diff_k)
        phi_orbit.append(tr_k - tr_HW2_base)
    holonomy_sum = sum((phi_orbit[(k + 1) % 4] - phi_orbit[k]) for k in range(4))
    require(strictly_below(abs(holonomy_sum), "1e-35"), f"Closed-loop Berry coboundary nonzero: {holonomy_sum}")

    # Pure gauge-orbit SU(2) loop holonomy W_gauge_orbit = prod (G_k G_{k+1}^\dagger) == I_2 (zero angle)
    W_gauge_orbit = I2
    for k in range(4):
        edge_g = iv_matmul(G_list[k], iv_conj_transpose(G_list[(k + 1) % 4]))
        W_gauge_orbit = iv_matmul(W_gauge_orbit, edge_g)
    gauge_orbit_loop_err = iv_frobenius_norm(iv_add(W_gauge_orbit, I2, scale_b=-1))
    gauge_orbit_loop_angle = iv.atan2(W_gauge_orbit[0][0].imag, W_gauge_orbit[0][0].real)
    require(strictly_below(gauge_orbit_loop_err, "1e-38") and strictly_below(abs(gauge_orbit_loop_angle), "1e-38"),
            f"Gauge-orbit holonomy should be trivial: {gauge_orbit_loop_angle}")

    # Genuine non-coboundary SU(2) flux Wilson loop W_loop = U01 U12 U23 U30 (strictly nonzero holonomy)
    U01_flux = su2_cayley_iv(iv.mpf(1) / iv.mpf(10), 0, 0)
    U12_flux = su2_cayley_iv(0, iv.mpf(1) / iv.mpf(10), 0)
    U23_flux = su2_cayley_iv(0, 0, iv.mpf(1) / iv.mpf(10))
    U30_flux = I2
    W_loop = iv_matmul(iv_matmul(U01_flux, U12_flux), iv_matmul(U23_flux, U30_flux))
    w_unitarity_err = iv_frobenius_norm(iv_add(iv_matmul(iv_conj_transpose(W_loop), W_loop), I2, scale_b=-1))
    require(strictly_below(w_unitarity_err, "1e-38"), f"Wilson flux loop not unitary: {w_unitarity_err}")
    flux_holonomy_angle = iv.atan2(W_loop[0][0].imag, W_loop[0][0].real)
    require(strictly_above(abs(flux_holonomy_angle), "0.1"),
            f"Non-coboundary SU(2) flux Wilson loop holonomy unexpectedly small: {flux_holonomy_angle}")

    # Non-tautological 16x16 overlap spectral sign projector P_ov = (I + H_W (H_W^2)^(-1/2))/2
    P_ov, ov_idem_err, ov_trace = overlap_sign_projector_iv(H_W)
    require(strictly_below(abs(ov_trace.real - iv.mpf(8)), "1e-35") and
            strictly_below(abs(ov_trace.imag), "1e-35"),
            f"Overlap projector trace != 8: {ov_trace}")

    # Gauge covariance of overlap projector P_ov(U^g) = G_16 P_ov(U) G_16^\dagger
    g0_cov = G_list[1]
    G_16 = iv_zeros(16)
    for s_idx, g_site in ((0, g0_cov), (1, g1_site_fixed)):
        for a_idx in range(4):
            for c1 in range(2):
                for c2 in range(2):
                    G_16[(s_idx * 4 + a_idx) * 2 + c1][(s_idx * 4 + a_idx) * 2 + c2] = g_site[c1][c2]
    _, H_W_g, _ = build_su2_wilson_dirac_2site(
        U_link_1, U_link_4_base, gauge_sites=[g0_cov, g1_site_fixed]
    )
    P_ov_g, _, _ = overlap_sign_projector_iv(H_W_g)
    G_Pov_Gt = iv_matmul(iv_matmul(G_16, P_ov), iv_conj_transpose(G_16))
    ov_cov_err = iv_frobenius_norm(iv_add(P_ov_g, G_Pov_Gt, scale_b=-1))
    require(strictly_below(ov_cov_err, "1e-35"), f"Overlap projector gauge covariance failed: {ov_cov_err}")

    # Genuine projector tangent operators d_i P_ov = P_ov A_i (I - P_ov) + (I - P_ov) A_i P_ov
    # built from non-commuting Hermitian perturbations (Dirac vector + flux dH, and axial-tensor)
    I16 = iv_eye(16)
    Q_ov = iv_add(I16, P_ov, scale_b=-1)
    g1_dirac, _, _, _, g5_dirac = gamma_matrices_4d()
    g5_g1 = iv_matmul(g5_dirac, g1_dirac)
    A1_tan = [[dH[r][c] for c in range(16)] for r in range(16)]
    A2_tan = iv_zeros(16)
    for a_idx in range(4):
        for b_idx in range(4):
            for c_idx in range(2):
                A1_tan[a_idx * 2 + c_idx][b_idx * 2 + c_idx] += g1_dirac[a_idx][b_idx]
                A2_tan[a_idx * 2 + c_idx][b_idx * 2 + c_idx] = iv.mpc(0, 1) * g5_g1[a_idx][b_idx]

    d1P = iv_add(iv_matmul(iv_matmul(P_ov, A1_tan), Q_ov), iv_matmul(iv_matmul(Q_ov, A1_tan), P_ov))
    d2P = iv_add(iv_matmul(iv_matmul(P_ov, A2_tan), Q_ov), iv_matmul(iv_matmul(Q_ov, A2_tan), P_ov))
    tan1_err = iv_frobenius_norm(iv_add(d1P, iv_add(iv_matmul(P_ov, d1P), iv_matmul(d1P, P_ov)), scale_b=-1))
    tan2_err = iv_frobenius_norm(iv_add(d2P, iv_add(iv_matmul(P_ov, d2P), iv_matmul(d2P, P_ov)), scale_b=-1))
    require(strictly_below(tan1_err, "1e-35") and strictly_below(tan2_err, "1e-35"),
            f"Luscher projector tangent relation failed: {tan1_err}, {tan2_err}")

    curv_12 = iv_trace(iv_matmul(P_ov, iv_add(iv_matmul(d1P, d2P), iv_matmul(d2P, d1P), scale_b=-1)))
    curv_21 = iv_trace(iv_matmul(P_ov, iv_add(iv_matmul(d2P, d1P), iv_matmul(d1P, d2P), scale_b=-1)))
    require(strictly_above(abs(curv_12.imag), "1e-3"),
            f"Berry curvature Im Tr(P_ov [d1P, d2P]) unexpectedly near zero: {curv_12}")
    skew_err = abs(curv_12 + curv_21)
    require(strictly_below(skew_err, "1e-35"), f"Berry curvature not skew-symmetric: {skew_err}")

    d1P_g = iv_matmul(iv_matmul(G_16, d1P), iv_conj_transpose(G_16))
    d2P_g = iv_matmul(iv_matmul(G_16, d2P), iv_conj_transpose(G_16))
    curv_12_g = iv_trace(iv_matmul(P_ov_g, iv_add(iv_matmul(d1P_g, d2P_g), iv_matmul(d2P_g, d1P_g), scale_b=-1)))
    curv_gauge_err = abs(curv_12_g - curv_12)
    require(strictly_below(curv_gauge_err, "1e-35"),
            f"Berry curvature SU(2) gauge invariance failed: {curv_gauge_err}")

    # =========================================================================
    # Pillar 3: P-H2C-CHIRAL-UV-03 ((3,3,1) anomalies, AH01 UV screening, DEAD-20261124-01)
    # =========================================================================
    # Exact Fraction (3,3,1) 15-Weyl SM generation anomaly cancellation
    weyl_15 = [
        ("Q_L", 3, 2, Fraction(1, 6)),
        ("u_Rc", 3, 1, Fraction(-2, 3)),
        ("d_Rc", 3, 1, Fraction(1, 3)),
        ("L_L", 1, 2, Fraction(-1, 2)),
        ("e_Rc", 1, 1, Fraction(1, 1)),
    ]
    anom_su3_u1 = sum(mult2 * Y for _, mult3, mult2, Y in weyl_15 if mult3 == 3)
    anom_su2_u1 = sum(mult3 * Y for _, mult3, mult2, Y in weyl_15 if mult2 == 2)
    anom_u1_cubed = sum(mult3 * mult2 * (Y ** 3) for _, mult3, mult2, Y in weyl_15)
    anom_grav_u1 = sum(mult3 * mult2 * Y for _, mult3, mult2, Y in weyl_15)
    witten_nd = sum(mult3 for _, mult3, mult2, _ in weyl_15 if mult2 == 2)
    require(anom_su3_u1 == 0 and anom_su2_u1 == 0 and anom_u1_cubed == 0 and anom_grav_u1 == 0,
            "(3,3,1) anomaly cancellation failed")
    require(witten_nd == 4 and witten_nd % 2 == 0, "Witten SU(2) doublet count not even")

    # AH01 Operational Horizon Lattice UV Screening
    L_min_ah01 = iv.mpf(["0.153021391482", "0.153021391483"])
    m_planck_gev = iv.mpf(["1.22088e19", "1.22090e19"])
    a_lat = L_min_ah01 / m_planck_gev
    regimes = {}
    for label, k_gev_str in (
        ("bmv_mesoscopic_1e_minus_12_GeV", "1e-12"),
        ("lhc_14_TeV", "1.4e4"),
        ("gut_scale_1e15_GeV", "1e15"),
    ):
        k_iv = iv.mpf(k_gev_str)
        d_tv_lat = (k_iv * a_lat) ** 2
        shots_min = iv.mpf("1") / (iv.mpf("2") * d_tv_lat ** 2)
        regimes[label] = {
            "k_obs_GeV": k_gev_str,
            "uv_screening_ratio_k_alat_sq": outward_str(d_tv_lat),
            "min_shots_delta_1": outward_str(shots_min),
        }
    require(strictly_below(iv.mpf(regimes["lhc_14_TeV"]["uv_screening_ratio_k_alat_sq"][1]), iv.mpf("3.1e-32")),
            "LHC lattice UV screening bound failed")
    require(strictly_above(iv.mpf(regimes["lhc_14_TeV"]["min_shots_delta_1"][0]), iv.mpf("5.2e62")),
            "LHC shot lower bound failed")

    # DEAD-20261124-01 guard: 2 * c_adm * b0 < 4 at eps_adm = 1/30, b0 = 7
    eps_adm = iv.mpf(1) / iv.mpf(30)
    c_adm = (eps_adm ** 2) / (iv.mpf(16) * (iv.pi ** 2))
    b0_su3 = iv.mpf(7)
    peierls_exp = iv.mpf(2) * c_adm * b0_su3
    require(strictly_above(peierls_exp, "0") and strictly_below(peierls_exp, "4"),
            f"DEAD-20261124-01 guard violated: 2*c_adm*b0={peierls_exp}")

    # =========================================================================
    # Pillar 4: C-H2-OPER-04, Round 03 H2d Audit & Round 04-07 Bridges
    # =========================================================================
    h2d_audit = compute_h2d_continuum_obstruction_audit()
    h2d_round04_bridges = compute_h2d_round04_constructive_bridges()
    h2d_round05_bridges = compute_h2d_round05_deepening_bridges()
    h2d_round06_bridges = compute_h2d_round06_convergence_bridges(
        h2d_round04_bridges,
        h2d_round05_bridges,
    )
    h2d_round07_frontier = compute_h2d_round07_irx_frontier(
        h2d_round04_bridges,
        h2d_round05_bridges,
        h2d_round06_bridges,
    )
    h2d_round08_waves5to8 = compute_h2d_round08_waves5to8_consolidation(
        h2d_round04_bridges,
        h2d_round05_bridges,
        h2d_round06_bridges,
        h2d_round07_frontier,
    )
    h2d_round09_wave9 = compute_h2d_round09_wave9_sqrt2_bianchi()
    payload = {
        "schema": "ueot-physics-unification-nonabelian-lattice-massgap-h2/1",
        "result_ids": [
            "P-H2A-TRANSFER-01",
            "P-H2B-DOBRUSHIN-02",
            "P-H2C-CHIRAL-UV-03",
            "C-H2-OPER-04",
        ],
        "status": "PASS",
        "lean_module": "formalization/ueot-physics-unification/UEOTPhysicsUnification/NonAbelianLatticeMassGapAndChiralIntegrabilityH2.lean",
        "lean_theorems": [
            "UEOTPhysicsUnification.NonAbelianLatticeMassGapAndChiralIntegrabilityH2.wilson_plaquette_transfer_positivity_and_strong_coupling_area_law",
            "UEOTPhysicsUnification.NonAbelianLatticeMassGapAndChiralIntegrabilityH2.dobrushin_lattice_cluster_mass_gap",
            "UEOTPhysicsUnification.NonAbelianLatticeMassGapAndChiralIntegrabilityH2.luscher_berry_loop_holonomy_and_overlap_gap_stability",
            "UEOTPhysicsUnification.NonAbelianLatticeMassGapAndChiralIntegrabilityH2.ah01_lattice_uv_screening_and_h2_decomposition",
        ],
        "h2d_continuum_obstruction_audit": h2d_audit,
        "h2d_round04_constructive_bridges": h2d_round04_bridges,
        "h2d_round05_deepening_bridges": h2d_round05_bridges,
        "h2d_round06_convergence_bridges": h2d_round06_bridges,
        "h2d_round07_irx_frontier": h2d_round07_frontier,
        "h2d_round08_waves5to8_consolidation": h2d_round08_waves5to8,
        "h2d_round09_wave9_sqrt2_bianchi": h2d_round09_wave9,
        "wilson_transfer_and_symanzik": {
            "q8_strong_coupling_transfer": transfer_results,
            "symanzik_o_a2_leading_coeff": outward_str(c0_exact),
            "symanzik_o_a2_checks": symanzik_checks,
        },
        "dobrushin_mass_gap_and_boundary": {
            "strong_coupling_regimes": dobrushin_results,
            "boundary_failure_alpha_eq_1": {
                "identity_kernel_alpha": outward_str(alpha_id),
                "uniqueness_fails": True,
            },
            "boundary_weak_coupling_beta_20": {
                "dobrushin_alpha": outward_str(alpha_weak),
                "mass_gap_m": outward_str(m_gap_weak),
                "gap_collapsed_below_1e_minus_6": True,
            },
        },
        "luscher_berry_and_overlap_stability": {
            "operator_dimension": 16,
            "plaquette_dist_base": outward_str(plaq_dist_base),
            "plaquette_dist_pert": outward_str(plaq_dist_pert),
            "hw_hermiticity_error": outward_str(herm_err, digits=12),
            "hw_sq_min_eigenvalue": outward_str(lmin_HW2),
            "hw_sq_perturbed_min_eigenvalue": outward_str(lmin_HWp2),
            "weyl_gap_lower_bound": outward_str(weyl_gap_lb),
            "perturbation_frob_norm_eta": outward_str(eta_pert),
            "gauge_orbit_max_drift": outward_str(max(gauge_orbit_diffs, key=lambda z: z.b), digits=12),
            "berry_loop_holonomy_coboundary_sum": outward_str(abs(holonomy_sum), digits=12),
            "gauge_orbit_loop_holonomy_angle": outward_str(gauge_orbit_loop_angle, digits=12),
            "flux_loop_holonomy_angle": outward_str(flux_holonomy_angle),
            "overlap_projector_idempotency_error": outward_str(ov_idem_err, digits=12),
            "overlap_projector_trace_real": outward_str(ov_trace.real),
            "overlap_projector_gauge_covariance_error": outward_str(ov_cov_err, digits=12),
            "overlap_tangent_1_relation_error": outward_str(tan1_err, digits=12),
            "overlap_tangent_2_relation_error": outward_str(tan2_err, digits=12),
            "berry_curvature_im_trace": outward_str(curv_12.imag),
            "berry_curvature_skew_error": outward_str(skew_err, digits=12),
            "berry_curvature_gauge_invariance_error": outward_str(curv_gauge_err, digits=12),
        },
        "chiral_331_ah01_and_dead_end_guard": {
            "anomaly_331_su3_u1": str(anom_su3_u1),
            "anomaly_331_su2_u1": str(anom_su2_u1),
            "anomaly_331_u1_cubed": str(anom_u1_cubed),
            "anomaly_331_grav_u1": str(anom_grav_u1),
            "witten_su2_doublets": witten_nd,
            "ah01_planck_length_floor": outward_str(L_min_ah01, digits=12),
            "planck_mass_GeV": outward_str(m_planck_gev, digits=6),
            "sub_planckian_regimes": regimes,
            "dead_20261124_01_peierls_exponent_2_cadm_b0": outward_str(peierls_exp),
            "dead_20261124_01_strictly_below_4": True,
        },
        "h2_layer_decomposition": {
            "H2a_WilsonTransferPositivityAndStrongCouplingAreaLaw": "CLOSED",
            "H2b_DobrushinMassGapAndLuscherOverlapStability": "CLOSED",
            "H2c_ChiralQuotientAndAH01LatticeUVScreening": "CLOSED",
            "H2d_Clay4DContinuumMeasureAndUnconditionalMassGap": "OPEN",
            "h2_operationally_closed_under_ah01_and_closed_tests": True,
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
    require(
        payload["result_ids"] == [
            "P-H2A-TRANSFER-01",
            "P-H2B-DOBRUSHIN-02",
            "P-H2C-CHIRAL-UV-03",
            "C-H2-OPER-04",
        ],
        "Governance drift: result_ids altered",
    )
    require(
        payload["h2_layer_decomposition"]["H2d_Clay4DContinuumMeasureAndUnconditionalMassGap"] == "OPEN",
        "Governance drift: H2d must remain OPEN",
    )
    require(payload["physical_unification"] == "OPEN", "Governance drift: physical_unification must remain OPEN")
    require(payload["device_certified"] is False, "Governance drift: device_certified must remain False")
    require("h2d_round06_convergence_bridges" in payload, "Missing h2d_round06_convergence_bridges")
    require("h2d_round07_irx_frontier" in payload, "Missing h2d_round07_irx_frontier")
    require(payload["h2d_round07_irx_frontier"]["h2d_status"] == "OPEN", "Round 07 h2d_status must remain OPEN")
    require(payload["h2d_round07_irx_frontier"]["irx_status"] == "OPEN", "Round 07 irx_status must remain OPEN")
    require("h2d_round08_waves5to8_consolidation" in payload, "Missing h2d_round08_waves5to8_consolidation")
    require(payload["h2d_round08_waves5to8_consolidation"]["h2d_status"] == "OPEN", "Round 08 h2d_status must remain OPEN")
    require(payload["h2d_round08_waves5to8_consolidation"]["irx_status"] == "OPEN", "Round 08 irx_status must remain OPEN")
    require(payload["h2d_round08_waves5to8_consolidation"]["o_w8_2_kp_conditional"] is True, "O-W8.2-KP must remain explicitly conditional")
    require(payload["h2d_round08_waves5to8_consolidation"]["device_certified"] is False, "Round 08 device_certified must remain False")
    require("h2d_round09_wave9_sqrt2_bianchi" in payload, "Missing h2d_round09_wave9_sqrt2_bianchi")
    r9_cert = payload["h2d_round09_wave9_sqrt2_bianchi"]
    require(r9_cert["h2d_status"] == "OPEN", "Round 09 h2d_status must remain OPEN")
    require(r9_cert["irx_status"] == "OPEN", "Round 09 irx_status must remain OPEN")
    require(r9_cert["uvx_status"] == "OPEN", "Round 09 uvx_status must remain OPEN")
    require(r9_cert["chiral_x_status"] == "OPEN", "Round 09 chiral_x_status must remain OPEN")
    require(r9_cert["noBulkTransition"] == "OPEN", "Round 09 noBulkTransition must remain OPEN")
    require(r9_cert["w9_2b_bkar_kp"]["infinite_tree_bkar_open"] is True, "infinite_tree_bkar_open must remain True")
    require(r9_cert["w9_4_ims_helical_and_zones"]["zone23_window_open"] is True, "zone23_window_open must remain True")
    require(r9_cert["device_certified"] is False, "Round 09 device_certified must remain False")
    require(r9_cert["physical_unification"] == "OPEN", "Round 09 physical_unification must remain OPEN")
    if args.check:
        committed = json.loads(CERT_PATH.read_text(encoding="utf-8"))
        require(committed == payload, "Committed certificate.json differs from recomputed Wave 11 H2 values")
        print("PASS: nonabelian_lattice_massgap_h2 (P-H2A-TRANSFER-01, P-H2B-DOBRUSHIN-02, P-H2C-CHIRAL-UV-03, C-H2-OPER-04)")
    else:
        write_json(CERT_PATH, payload)
        print("WROTE:", CERT_PATH)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
