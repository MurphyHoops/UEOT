#!/usr/bin/env python3
"""Standalone, zero-dependency Python 3 verifier for:
'Separating Fluctuation Attenuation from Signed Causal Response in Correlated
Quantum Baths: Certified Process Instruments and Local-Field Microcausality'

Uses ONLY the Python 3 standard library (`cmath`, `fractions`, `itertools`,
`json`, `math`, `sys`) and performs zero external file reads or writes:

    python3 verify_standalone.py

What this verifier computes independently from scratch:
  1. Ramsey Equivalence & Causal-Break Response on D = [1/5, 2/5] x {|c| <= n <= 3/5}:
     - Verifies P1 = (3/10, 1/2, 1/4) and P2 = (1/3, 31/100, 81/400) share exact
       (u, v) = (9/50, 9/400) and all free Ramsey decay means m(t) (with
       m(3/4) = 0.730531651137 and m(3/2) = 0.360071794945), while splitting on:
       * causal-break Im z_+(2/3, 3/4): 0.119850748164 (P1) vs 0.147616987004 (P2),
         sharing invariant modulus |z_+| = 0.735275955165;
       * stopped 3-slot Bell event P(ppp, YZ-) at eta = 0.96 by 0.001730089430
         (original timing) and 0.001581344541 (swapped timing).
     - Verifies aligned-Y two-model holdout boundary threshold at a = 1, b = 3/4:
       upper_P1 = 0.600885224763 < threshold = 0.605581355419 < lower_P2 = 0.610277486074,
       confirming synthetic holdout frequency 71,816/120,000 = 0.598466666667 < threshold.
     - Computes Ramsey determinant det M(3/4, 3/2) = -1.162022859636, causal-break
       sensitivity F(2/3, 3/4) = 1.819240198557, and whole-domain inverse
       Lipschitz bounds (u: 51.240114, v: 31.421917, w: 2.965319, lam: 7.413296,
       n: 722.047690, c: 830.027702).
  2. Exact Rational Total-Number Cutoff & Duhamel Propagation Bounds:
     - Evaluates the exact arbitrary-precision Fraction upper bound B_K (with
       upward integer square-root rounding at 10^-12) across K in {4, 8, 12, 13,
       14, 16, 20, 24}, reproducing 0.011677620430 (K=16) and 0.002098904698 (K=20).
  3. Compactly Supported Scalar Field on R x S^1 (Exact Two-Mode Matching vs. Microcausality):
     - Verifies omega_1 = 3/2, g_1 = 3/5 matching (with g_0 = 1) via the C^2 four-box
       convolution profile f_j on L = 4*pi/sqrt(5), geometric spacelike gap L/2 - 2R > 2/5,
       timelike co-located phase (two-mode 0.163731618 vs. full field 0.209161320),
       spacelike antipodal cancellation (two-mode 0.001330794 rad vs. full field |Phi|
       < 2.486e-12 rad at M=160), bare energy gains (0.296126 and 0.071709), and
       the two-qubit bath-reuse excitation excess (+0.0375 from 3/20 energy deposit).
"""
from __future__ import annotations

from fractions import Fraction as Q
import cmath
import itertools
import json
import math
import sys


# ---------------------------------------------------------------------------
# Helpers for outward-rounded exact Fraction square roots (for Duhamel B_K)
# ---------------------------------------------------------------------------
def isqrt_frac_ceil(x: Q, scale: int = 10 ** 12) -> Q:
    """Return an exact Fraction >= sqrt(x) rounded upward at precision 1/scale."""
    assert x >= 0
    if x == 0:
        return Q(0)
    num = x.numerator * (scale ** 2)
    den = x.denominator
    k = math.isqrt(num // den)
    while k * k * den < num:
        k += 1
    return Q(k, scale)


def exp_taylor_upper(x: Q, terms: int = 24) -> Q:
    """Upper bound on e^x for x >= 0 using partial sum + Lagrange remainder."""
    total = Q(0)
    fact = 1
    pow_x = Q(1)
    for k in range(terms):
        if k > 0:
            fact *= k
            pow_x *= x
        total += pow_x / fact
    # Remainder <= e^x * x^terms / terms! ; since x <= 1, e^x < 3
    rem = Q(3) * (pow_x * x) / (fact * terms)
    return total + rem


# ---------------------------------------------------------------------------
# Part 1: Correlated Two-Mode Bath Weyl Formula & Ramsey Ambiguity Witness
# ---------------------------------------------------------------------------
OMEGA = (1.0, 1.5)
G_COUP = (1.0, 0.6)
TIMINGS = {
    "original": (2.0 / 3.0, 3.0 / 4.0, 0.5),
    "swapped": (3.0 / 4.0, 2.0 / 3.0, 0.5),
}
RECORDS = ("f", "pf", "ppf", "ppp")


def mat_mul(A, B):
    n = len(A)
    return [[sum(A[i][k] * B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]


def mat_conj_T(A):
    n = len(A)
    return [[A[j][i].conjugate() for j in range(n)] for i in range(n)]


def mat_trace(A):
    return sum(A[i][i] for i in range(len(A)))


def kron2(A, B):
    out = [[0j] * 4 for _ in range(4)]
    for i in range(2):
        for j in range(2):
            for k in range(2):
                for l in range(2):
                    out[2 * i + k][2 * j + l] = A[i][j] * B[k][l]
    return out


I2 = [[1 + 0j, 0j], [0j, 1 + 0j]]
X2 = [[0j, 1 + 0j], [1 + 0j, 0j]]
Y2 = [[0j, -1j], [1j, 0j]]
Z2 = [[1 + 0j, 0j], [0j, -1 + 0j]]
PAULIS = {"I": I2, "X": X2, "Y": Y2, "Z": Z2}

FAIL_OP = [[math.sqrt(1 / 8), 0.0], [0.0, math.sqrt(1 / 4)]]
PASS_DIAG = [math.sqrt(7 / 8), math.sqrt(3 / 4)]
RY_PI2 = [[1 / math.sqrt(2), -1 / math.sqrt(2)], [1 / math.sqrt(2), 1 / math.sqrt(2)]]
RX_PI3 = [[math.sqrt(3) / 2, -0.5j], [-0.5j, math.sqrt(3) / 2]]
PASS_OPS = (
    mat_mul(RY_PI2, [[PASS_DIAG[0], 0j], [0j, PASS_DIAG[1]]]),
    mat_mul(RX_PI3, [[PASS_DIAG[0], 0j], [0j, PASS_DIAG[1]]]),
    [[complex(PASS_DIAG[0]), 0j], [0j, complex(PASS_DIAG[1])]],
)


def ramsey_coeffs(t: float) -> tuple[float, float]:
    """Return (A_ram, B_ram) such that m(t) = eta * exp(-(A_ram * u + B_ram * v))."""
    d0 = (G_COUP[0] / OMEGA[0]) * (1.0 - cmath.exp(1j * OMEGA[0] * t))
    d1 = (G_COUP[1] / OMEGA[1]) * (1.0 - cmath.exp(1j * OMEGA[1] * t))
    A = 2.0 * (abs(d0) ** 2 + abs(d1) ** 2)
    B = 8.0 * (d0.conjugate() * d1).real
    return A, B


def causal_break_coeffs(a: float, b: float) -> tuple[float, float, float]:
    """Return (A_break, B_break, F_sensitivity) at prep window a and probe window b.
    For initial pointer state s0 = s0' = s in {+1, -1} over [0, a] followed by pi/2
    pulse at t = a to superposition (s1=+1, s1'=-1) over [a, a+b]:
        z_s = exp(-(A_break * u + B_break * v) + i * s * w * F_sensitivity).
    """
    y0 = cmath.exp(1j * OMEGA[0] * a) * (G_COUP[0] / OMEGA[0]) * (1.0 - cmath.exp(1j * OMEGA[0] * b))
    y1 = cmath.exp(1j * OMEGA[1] * a) * (G_COUP[1] / OMEGA[1]) * (1.0 - cmath.exp(1j * OMEGA[1] * b))
    A = 2.0 * (abs(y0) ** 2 + abs(y1) ** 2)
    B = 8.0 * (y0.conjugate() * y1).real
    F = 4.0 * sum(
        (G_COUP[k] / OMEGA[k]) ** 2 * (math.sin(OMEGA[k] * a) + math.sin(OMEGA[k] * b) - math.sin(OMEGA[k] * (a + b)))
        for k in (0, 1)
    )
    return A, B, F


def z_causal_break(lam: float, n: float, c: float, s: int, a: float = 2.0 / 3.0, b: float = 3.0 / 4.0) -> complex:
    u = (lam ** 2) * (2.0 * n + 1.0)
    v = (lam ** 2) * c
    w = lam ** 2
    A_br, B_br, F_val = causal_break_coeffs(a, b)
    return cmath.exp(-(A_br * u + B_br * v) + 1j * s * w * F_val)


def bell_blocks(lam: float, n: float, c: float, timing: str = "original") -> dict[str, list[list[complex]]]:
    """Compute exact unnormalized 4x4 terminal SR Choi blocks on normalized Bell input."""
    times_all = TIMINGS[timing]
    u = (lam ** 2) * (2.0 * n + 1.0)
    v = (lam ** 2) * c
    w = lam ** 2
    rho_bell = [[0.5 if (i in (0, 3) and j in (0, 3)) else 0.0 + 0j for j in range(4)] for i in range(4)]
    blocks: dict[str, list[list[complex]]] = {}

    for rec in RECORDS:
        ts = times_all[: len(rec)]
        T_tot = sum(ts)
        histories = list(itertools.product((0, 1), repeat=len(rec)))
        A_mats = []
        betas = []
        phases = []
        for h in histories:
            A_op = [[1 + 0j, 0j], [0j, 1 + 0j]]
            beta = [0j, 0j]
            phi = 0.0
            for j, (idx, dt) in enumerate(zip(h, ts)):
                sgn = 1.0 - 2.0 * idx
                rot = [cmath.exp(-1j * OMEGA[k] * dt) for k in (0, 1)]
                xi = [sgn * (G_COUP[k] / OMEGA[k]) * (rot[k] - 1.0) for k in (0, 1)]
                prev = [rot[k] * beta[k] for k in (0, 1)]
                phi += sum((prev[k].conjugate() * xi[k]).imag for k in (0, 1))
                beta = [prev[k] + xi[k] for k in (0, 1)]
                K_step = FAIL_OP if rec[j] == "f" else PASS_OPS[j]
                proj_K = [[K_step[r][idx] * A_op[idx][c_i] for c_i in range(2)] for r in range(2)]
                A_op = proj_K
            A_mats.append(A_op)
            betas.append(beta)
            phases.append(phi)

        B_out = [[0j] * 4 for _ in range(4)]
        for Ah, bh, ph in zip(A_mats, betas, phases):
            Ah_SR = kron2(Ah, I2)
            for Ahp, bhp, php in zip(A_mats, betas, phases):
                d0 = (bh[0] - bhp[0]) * cmath.exp(1j * OMEGA[0] * T_tot)
                d1 = (bh[1] - bhp[1]) * cmath.exp(1j * OMEGA[1] * T_tot)
                sq = abs(d0) ** 2 + abs(d1) ** 2
                cross = 2.0 * (d0.conjugate() * d1).real
                ex_phase = ph - php + sum((bhp[k].conjugate() * bh[k]).imag for k in (0, 1))
                L = cmath.exp(-u * sq / 2.0 - v * cross + 1j * w * ex_phase)
                Ahp_SR_dag = mat_conj_T(kron2(Ahp, I2))
                term = mat_mul(mat_mul(Ah_SR, rho_bell), Ahp_SR_dag)
                for r in range(4):
                    for col in range(4):
                        B_out[r][col] += L * term[r][col]
        blocks[rec] = B_out
    return blocks


def bell_events_from_blocks(blocks: dict, eta: float, obs_name: str) -> list[float]:
    obs = kron2(PAULIS[obs_name[0]], PAULIS[obs_name[1]])
    probs = []
    for rec in RECORDS:
        b = blocks[rec]
        wt = mat_trace(b).real
        mom = mat_trace(mat_mul(obs, b)).real
        probs.extend([(wt - eta * mom) / 2.0, (wt + eta * mom) / 2.0])
    return probs


def verify_part1_ramsey_and_break() -> dict:
    # Exact Ramsey ambiguity witness on 1/5 <= lam <= 2/5, |c| <= n <= 3/5
    l1, n1, c1 = Q(3, 10), Q(1, 2), Q(1, 4)
    l2, n2, c2 = Q(1, 3), Q(31, 100), Q(81, 400)
    assert l1 ** 2 * (2 * n1 + 1) == Q(9, 50) == l2 ** 2 * (2 * n2 + 1)
    assert l1 ** 2 * c1 == Q(9, 400) == l2 ** 2 * c2
    u0, v0 = Q(9, 50), Q(9, 400)
    w_min = max(Q(1, 25), u0 / Q(11, 5))
    w_max = min(Q(4, 25), u0 - 2 * abs(v0))
    assert (w_min, w_max) == (Q(9, 110), Q(27, 200))

    # Free Ramsey decay values at (u0, v0)
    A1, B1 = ramsey_coeffs(0.75)
    A2, B2 = ramsey_coeffs(1.5)
    m_short = math.exp(-(A1 * float(u0) + B1 * float(v0)))
    m_long = math.exp(-(A2 * float(u0) + B2 * float(v0)))
    assert abs(m_short - 0.730531651137) < 1e-12
    assert abs(m_long - 0.360071794945) < 1e-12

    det_M = A1 * B2 - A2 * B1
    assert -1.16202286 < det_M < -1.16202285

    Ab, Bb, F_val = causal_break_coeffs(2.0 / 3.0, 0.75)
    assert 1.819240198557 < F_val < 1.819240198558

    z_p1 = z_causal_break(float(l1), float(n1), float(c1), +1)
    z_p2 = z_causal_break(float(l2), float(n2), float(c2), +1)
    assert abs(abs(z_p1) - abs(z_p2)) < 1e-15
    assert abs(abs(z_p1) - 0.735275955165) < 1e-12
    assert abs(z_p1.imag - 0.119850748164) < 1e-12
    assert abs(z_p2.imag - 0.147616987004) < 1e-12

    # Aligned-Y discrimination check at holdout window (a=1, b=3/4)
    A_hold, B_hold, F_hold = causal_break_coeffs(1.0, 0.75)
    amp_hold = math.exp(-(A_hold * float(u0) + B_hold * float(v0)))
    err_hold = 0.001 / 2.0 + 2.0 ** (-40)
    upper_p1 = (1.0 + amp_hold * math.sin(float(l1 ** 2) * F_hold)) / 2.0 + err_hold
    lower_p2 = (1.0 + 0.9 * amp_hold * math.sin(float(l2 ** 2) * F_hold) * math.cos(0.02)) / 2.0 - err_hold
    align_thresh = (upper_p1 + lower_p2) / 2.0
    assert abs(align_thresh - 0.605581355419) < 1e-12
    assert 71816 / 120000 < upper_p1 < align_thresh < lower_p2

    # Whole-domain Lipschitz upper bounds on 1/5 <= lam <= 2/5, |c| <= n <= 3/5, 0.9 <= eta <= 1
    h_u = (B2 / det_M, -B1 / det_M)
    h_v = (-A2 / det_M, A1 / det_M)
    eta_min = 0.9
    m1_floor = eta_min * math.exp(-0.544 * A1)
    m2_floor = eta_min * math.exp(-0.544 * A2)
    r_floor = eta_min * math.exp(-0.544 * Ab)
    assert 0.411787795 < m1_floor < 0.411787797
    assert 0.067589590 < m2_floor < 0.067589592
    L_u = abs(h_u[0] + h_u[1]) / eta_min + abs(h_u[0]) / m1_floor + abs(h_u[1]) / m2_floor
    L_v = abs(h_v[0] + h_v[1]) / eta_min + abs(h_v[0]) / m1_floor + abs(h_v[1]) / m2_floor
    L_w = math.pi * math.sqrt(2.0) / (2.0 * r_floor * F_val)
    L_lam = L_w / 0.4
    L_n = (L_u + 2.2 * L_w) / 0.08
    L_c = (L_v + 0.6 * L_w) / 0.04
    assert 51.24011 < L_u < 51.24012
    assert 31.42191 < L_v < 31.42192
    assert 2.96531 < L_w < 2.96532
    assert 7.41329 < L_lam < 7.41330
    assert 722.0476 < L_n < 722.0478
    assert 830.0277 < L_c < 830.0278

    # Stopped Bell event separation between Ramsey-equivalent P1 and P2 at eta = 0.96
    diffs = {}
    for t_name in ("original", "swapped"):
        b1 = bell_blocks(float(l1), float(n1), float(c1), t_name)
        b2 = bell_blocks(float(l2), float(n2), float(c2), t_name)
        ev1 = bell_events_from_blocks(b1, 0.96, "YZ")
        ev2 = bell_events_from_blocks(b2, 0.96, "YZ")
        assert abs(sum(ev1) - 1.0) < 1e-14 and abs(sum(ev2) - 1.0) < 1e-14
        diffs[t_name] = {
            "p1_ppp_YZ_minus": round(ev1[6], 12),
            "p2_ppp_YZ_minus": round(ev2[6], 12),
            "gap": round(abs(ev1[6] - ev2[6]), 12),
        }
    assert abs(diffs["original"]["gap"] - 0.001730089430) < 1e-11
    assert abs(diffs["swapped"]["gap"] - 0.001581344541) < 1e-11

    return {
        "ramsey_equivalent_u_v": [str(u0), str(v0)],
        "w_fiber_interval": [str(w_min), str(w_max)],
        "ramsey_means_P1_P2": {"m_short": round(m_short, 12), "m_long": round(m_long, 12)},
        "causal_break_P1_P2": {
            "modulus_invariant": round(abs(z_p1), 12),
            "im_z_plus_P1": round(z_p1.imag, 12),
            "im_z_plus_P2": round(z_p2.imag, 12),
        },
        "aligned_Y_threshold": round(align_thresh, 12),
        "ramsey_det": round(det_M, 12),
        "causal_break_F": round(F_val, 12),
        "lipschitz_upper": {
            "u": round(L_u, 6), "v": round(L_v, 6), "w": round(L_w, 6),
            "lambda": round(L_lam, 6), "n": round(L_n, 6), "c": round(L_c, 6),
        },
        "stopped_bell_splitting_YZ_minus_eta096": diffs,
    }


# ---------------------------------------------------------------------------
# Part 2: Exact Rational Total-Number Cutoff & Duhamel Propagation Bounds (B_K)
# ---------------------------------------------------------------------------
def exact_duhamel_cutoff_bound(K: int) -> Q:
    """Exact outward-rounded Fraction upper bound B_K on half trace distance
    across all inputs and both timings on 1/5 <= lam <= 2/5, |c| <= n <= 3/5.
    """
    a_star = Q(6, 11)
    b_star = Q(3, 8)
    x = Q(9, 10)  # lam_max * ||g||_2 * T_max = (2/5) * sqrt(34/25) * (23/12) < 9/10
    assert (Q(2, 5) ** 2) * Q(34, 25) * (Q(23, 12) ** 2) < x ** 2
    inv_one_minus = Q(1) / (Q(1) - (x ** 2) / 2)  # 200/119 >= exp(x^2/2)
    assert exp_taylor_upper((x ** 2) / 2) < inv_one_minus
    assert math.exp(float((x ** 2) / 2)) < float(inv_one_minus)

    f_vals: list[Q] = []
    for s in range(K + 1):
        d = K - s
        radicand = Q(math.factorial(K + 1), math.factorial(s))
        root_up = isqrt_frac_ceil(radicand, 10 ** 12)
        series = Q(0)
        for l in range(s + 1):
            term = Q(math.comb(s, l)) * (x ** (2 * l)) / (math.factorial(d + l) * (d + 2 * l + 1))
            series += term
        val = (x ** (d + 1)) * root_up * inv_one_minus * series
        f_vals.append(min(Q(1), val))

    # Monotone envelope h_s = max_{j <= s} f_j
    h_vals: list[Q] = []
    cur = Q(0)
    for fv in f_vals:
        cur = max(cur, fv)
        h_vals.append(cur)

    # Exact total occupation distribution under dominating (a_star, b_star)
    survived_sum = Q(0)
    pref = (1 - a_star) * (1 - b_star)
    for s in range(K + 1):
        ps = pref * sum((a_star ** i) * (b_star ** (s - i)) for i in range(s + 1))
        survived_sum += ps * (Q(1) - h_vals[s])
    return Q(1) - survived_sum


def verify_part2_cutoff_bounds() -> dict:
    expected = {
        4: 0.629532048416,
        8: 0.221934875279,
        12: 0.055985832631,
        13: 0.038466572543,
        14: 0.025259114053,
        16: 0.011677620430,
        20: 0.002098904698,
        24: 0.000357107093,
    }
    out = {}
    for K, exp_val in expected.items():
        b_k = exact_duhamel_cutoff_bound(K)
        # Outward 12-decimal ceiling
        b_dec = math.ceil(float(b_k) * 10 ** 12) / (10 ** 12)
        assert abs(b_dec - exp_val) <= 2e-12, (K, b_dec, exp_val)
        out[str(K)] = b_dec
    return {"uniform_duhamel_half_trace_upper": out}


# ---------------------------------------------------------------------------
# Part 3: Scalar KG Field on R x S^1 (Two-Mode Matching vs. Microcausality)
# ---------------------------------------------------------------------------
def verify_part3_local_field() -> dict:
    beta = math.sqrt(5.0) / 2.0
    length = 2.0 * math.pi / beta  # L = 4*pi / sqrt(5)
    lam, n_occ, c_corr = 0.3, 0.5, 0.25

    x1 = math.pi / 80.0
    sinc1 = math.sin(x1) / x1
    target = 0.6 * math.sqrt(0.75)
    p_mix = 2.0 * (1.0 - target / (sinc1 ** 4))
    assert 0.0 < p_mix < 1.0

    # Check exact two-mode match at j = 1 (with non-degenerate zero-mode g0 = f0 / sqrt(w0) = 1
    # and standing cosine normal modes j >= 1 carrying factor sqrt(2 / w_j))
    w1 = math.sqrt(1.0 + beta ** 2)
    f1 = (sinc1 ** 4) * (1.0 - p_mix + p_mix * math.cos(math.pi / 3.0))
    g1 = math.sqrt(2.0 / w1) * f1
    assert abs(w1 - 1.5) < 1e-14 and abs(g1 - 0.6) < 1e-14

    # Geometric spacelike separation for antipodal probes with half-width R = (1/6 + 1/40) * L
    supp_R = (1.0 / 6.0 + 1.0 / 40.0) * length
    gap_dist = length / 2.0 - 2.0 * supp_R
    assert gap_dist > 0.4  # exceeds a+b = 2/5 => strictly spacelike

    def run_field(modes: int, a: float, b: float, opposite: bool) -> dict:
        phase = 0.0
        damping = 0.0
        energy = 0.0
        low_d = []
        for j in range(modes + 1):
            if j == 0:
                wj, gj = 1.0, 1.0
            else:
                xj = math.pi * j / 80.0
                fj = ((math.sin(xj) / xj) ** 4) * (1.0 - p_mix + p_mix * math.cos(math.pi * j / 3.0))
                wj = math.sqrt(1.0 + (beta * j) ** 2)
                gj = math.sqrt(2.0 / wj) * fj
            par = (-1.0) ** j if opposite else 1.0
            phase += 4.0 * (lam ** 2) * (gj ** 2) * par * (math.sin(wj * a) + math.sin(wj * b) - math.sin(wj * (a + b))) / (wj ** 2)
            re_d = gj * par * (math.cos(wj * a) - math.cos(wj * (a + b))) / wj
            im_d = gj * par * (math.sin(wj * a) - math.sin(wj * (a + b))) / wj
            damping += 4.0 * (lam ** 2) * (gj ** 2) * (1.0 - math.cos(wj * b)) / (wj ** 2)
            if j <= 1:
                low_d.append((re_d, im_d))
            energy += 2.0 * (lam ** 2) * (gj ** 2) * (2.0 - math.cos(wj * a) - math.cos(wj * b)) / wj
        (r0, i0), (r1, i1) = low_d
        damping += 4.0 * (lam ** 2) * n_occ * (r0 * r0 + i0 * i0 + r1 * r1 + i1 * i1)
        damping += 8.0 * (lam ** 2) * c_corr * (r0 * r1 + i0 * i1)
        tail_sum = 2.0 * ((80.0 / math.pi) ** 8) / (10.0 * (beta ** 3) * (modes ** 10))
        phase_tail = 12.0 * (lam ** 2) * tail_sum
        return {
            "phase_rad": phase,
            "phase_tail_upper": phase_tail,
            "im_z_plus": math.exp(-damping) * math.sin(phase),
            "bare_energy_gain": energy,
        }

    two_mode_tl = run_field(1, 2.0 / 3.0, 0.75, False)
    full_tl = run_field(160, 2.0 / 3.0, 0.75, False)
    two_mode_sl = run_field(1, 0.2, 0.2, True)
    full_sl = run_field(160, 0.2, 0.2, True)

    assert abs(two_mode_tl["phase_rad"] - 0.163731618) < 1e-9
    assert abs(full_tl["phase_rad"] - 0.209161320) < 1e-9
    assert abs(full_tl["im_z_plus"] - 0.145988513) < 1e-9
    assert abs(full_tl["bare_energy_gain"] - 0.296125651) < 1e-8
    assert abs(two_mode_sl["phase_rad"] - 0.001330794) < 1e-9
    assert abs(full_sl["phase_rad"]) <= full_sl["phase_tail_upper"] < 2.486e-12
    assert abs(full_sl["bare_energy_gain"] - 0.071708942) < 1e-8

    # Two-qubit resonant energy-exchange bath reuse check (exact rational sin^2(pi/6) = 1/4)
    p_sys_init = Q(4, 5)
    q_bath_init = Q(1, 5)
    sin2_swap = Q(1, 4)
    cos2_swap = Q(3, 4)
    p_sys_after = q_bath_init + (p_sys_init - q_bath_init) * cos2_swap
    q_bath_after = q_bath_init + (p_sys_init - q_bath_init) * sin2_swap
    assert p_sys_after == Q(13, 20) and q_bath_after == Q(7, 20)
    assert p_sys_after + q_bath_after == p_sys_init + q_bath_init
    p_sys_reuse = q_bath_after + (p_sys_init - q_bath_after) * cos2_swap
    reuse_excess = p_sys_reuse - p_sys_after
    assert reuse_excess == (q_bath_after - q_bath_init) * sin2_swap == Q(3, 80)
    assert reuse_excess == Q(375, 10000)

    return {
        "p_mix": round(p_mix, 12),
        "spacelike_gap": round(gap_dist, 9),
        "timelike_colocated": {
            "two_mode_phase": round(two_mode_tl["phase_rad"], 9),
            "full_field_phase": round(full_tl["phase_rad"], 9),
            "im_z_plus": round(full_tl["im_z_plus"], 9),
            "bare_energy_gain": round(full_tl["bare_energy_gain"], 6),
        },
        "spacelike_antipodal": {
            "two_mode_spurious_phase": round(two_mode_sl["phase_rad"], 9),
            "full_field_160_phase": full_sl["phase_rad"],
            "phase_tail_upper_M160": full_sl["phase_tail_upper"],
            "bare_energy_gain": round(full_sl["bare_energy_gain"], 6),
        },
        "two_qubit_reuse_excitation_excess": str(reuse_excess),
    }


def run_all_standalone_checks() -> dict:
    p1 = verify_part1_ramsey_and_break()
    p2 = verify_part2_cutoff_bounds()
    p3 = verify_part3_local_field()
    return {
        "status": "PASS",
        "part1_ramsey_ambiguity_and_causal_break": p1,
        "part2_duhamel_total_number_cutoff": p2,
        "part3_local_kg_field_vs_two_mode": p3,
    }


if __name__ == "__main__":
    print(json.dumps(run_all_standalone_checks(), indent=2))
    sys.exit(0)
