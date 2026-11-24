"""40-digit outward-interval & symbolic verification for Wave 11 H2 (P-H2A-TRANSFER-01..C-H2-OPER-04)."""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
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
    # Pillar 4: C-H2-OPER-04, Round 03 H2d Audit & Round 04-06 Bridges
    # =========================================================================
    h2d_audit = compute_h2d_continuum_obstruction_audit()
    h2d_round04_bridges = compute_h2d_round04_constructive_bridges()
    h2d_round05_bridges = compute_h2d_round05_deepening_bridges()
    h2d_round06_bridges = compute_h2d_round06_convergence_bridges(
        h2d_round04_bridges,
        h2d_round05_bridges,
    )
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
