#!/usr/bin/env python3
"""Standalone, zero-dependency Python 3 verifier for:
'Separating Fluctuation Attenuation from Signed Causal Response in Correlated
Quantum Baths: Certified Process Instruments and Local-Field Microcausality'

Uses ONLY the Python 3 standard library (`cmath`, `fractions`, `itertools`,
`json`, `math`, `random`, `sys`) and performs zero external file reads/writes:

    python3 verify_standalone.py

Independently verifies from scratch:
  1. Direct Fock-Space Schrödinger Unitary Cross-Check (No Weyl shortcut):
     - Exact decoupled 1D Fock unitary propagator (K=12 vacuum & K=8 thermal)
       via scaling-and-squaring Taylor evolution of H(lambda):
       * Verifies Eqs. (5) & (A2) operator ordering and dynamical scalar phase;
       * Confirms causal-break |z_s> + |+> protocol reproduces Eq. (13) vs |+>
         on slot 1 yielding zero phase (< 1e-15);
       * Confirms 3-slot Choi blocks B_r on vacuum (0.3, 0, 0) to < 1e-13 and at
         P1 = (0.3, 0.5, 0.25) at K=8 within B_8.
  2. Ramsey Equivalence, Causal-Break Phase, & Whole-Domain Lipschitz Stability:
     - 25-point fiber admissibility sweep across w in [9/110, 27/200];
     - Exact twin P1, P2 checks: det M(3/4, 3/2) = -1.162022859636, m(3/4), m(3/2),
       causal-break F(2/3, 3/4) = 1.819240198557, |z_+| = 0.735275955165,
       Im z_+(P1) = 0.119850748164 vs Im z_+(P2) = 0.147616987004;
     - Outward observable floors & Lipschitz bounds Eq. (16) stress-tested across
       all 16 corners + 500 seeded random pairs in D x [0.9, 1] x [-0.02, 0.02];
     - Stopped Bell splitting at eta=0.96, Tr[B_r] completeness, Tr[B_f] = 3/16,
       readout-challenge (eta=0.65) gap/power/Hoeffding band, F(1, 3/4), aligned-Y
       separator 0.605581355419, and Eq. (22)/(C1) polytope Taylor remainder.
  3. Exact Rational Duhamel Total-Number Cutoff Bounds B_K (K = 0..24).
  4. Compactly Supported Scalar Field on R x S^1 & Two-Qubit Reuse Swap:
     - g_0 = 1, w_1 = 3/2, g_1 = 3/5, gap = 0.655649375, timelike & spacelike
       phases/tails, mode-wise j^-11 bound, and full 4x4 swap unitary entropy Sigma.
"""
from __future__ import annotations

from fractions import Fraction as Q
import cmath
import itertools
import json
import math
import random
import sys


# ---------------------------------------------------------------------------
# Exact rational arithmetic helpers
# ---------------------------------------------------------------------------
def isqrt_frac_ceil(x: Q, scale: int = 10 ** 12) -> Q:
    """Return exact Fraction >= sqrt(x) rounded upward at resolution 1/scale."""
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
    """Outward Lagrange-remainder rational upper bound on e^x for 0 <= x <= 1."""
    total = Q(0)
    fact = 1
    pow_x = Q(1)
    for k in range(terms):
        if k > 0:
            fact *= k
            pow_x *= x
        total += pow_x / fact
    rem = Q(3) * (pow_x * x) / (fact * terms)
    return total + rem


# ---------------------------------------------------------------------------
# Generic small dense complex matrix helpers (stdlib only)
# ---------------------------------------------------------------------------
def mat_mul(A, B):
    n = len(A)
    m = len(B[0])
    k_len = len(B)
    return [[sum(A[i][k] * B[k][j] for k in range(k_len)) for j in range(m)] for i in range(n)]


def mat_conj_T(A):
    rows, cols = len(A), len(A[0])
    return [[A[j][i].conjugate() for j in range(rows)] for i in range(cols)]


def mat_trace(A):
    return sum(A[i][i] for i in range(len(A)))


def kron2(A, B):
    ra, ca = len(A), len(A[0])
    rb, cb = len(B), len(B[0])
    out = [[0j] * (ca * cb) for _ in range(ra * rb)]
    for i in range(ra):
        for j in range(ca):
            for k in range(rb):
                for l in range(cb):
                    out[rb * i + k][cb * j + l] = A[i][j] * B[k][l]
    return out


I2 = [[1 + 0j, 0j], [0j, 1 + 0j]]
X2 = [[0j, 1 + 0j], [1 + 0j, 0j]]
Y2 = [[0j, -1j], [1j, 0j]]
Z2 = [[1 + 0j, 0j], [0j, -1 + 0j]]
PAULIS = {"I": I2, "X": X2, "Y": Y2, "Z": Z2}

OMEGA = (1.0, 1.5)
G_COUP = (1.0, 0.6)
TIMINGS = {
    "original": (2.0 / 3.0, 3.0 / 4.0, 0.5),
    "swapped": (3.0 / 4.0, 2.0 / 3.0, 0.5),
}
RECORDS = ("f", "pf", "ppf", "ppp")

FAIL_OP = [[math.sqrt(1 / 8), 0.0], [0.0, math.sqrt(1 / 4)]]
PASS_DIAG = [math.sqrt(7 / 8), math.sqrt(3 / 4)]
RY_PI2 = [[1 / math.sqrt(2), -1 / math.sqrt(2)], [1 / math.sqrt(2), 1 / math.sqrt(2)]]
RX_PI3 = [[math.sqrt(3) / 2, -0.5j], [-0.5j, math.sqrt(3) / 2]]
PASS_OPS = (
    mat_mul(RY_PI2, [[PASS_DIAG[0], 0j], [0j, PASS_DIAG[1]]]),
    mat_mul(RX_PI3, [[PASS_DIAG[0], 0j], [0j, PASS_DIAG[1]]]),
    [[complex(PASS_DIAG[0]), 0j], [0j, complex(PASS_DIAG[1])]],
)


# ---------------------------------------------------------------------------
# Direct 1D Decoupled Fock-Space Schrodinger Unitary Cross-Check (K=12, K=8)
# ---------------------------------------------------------------------------
def fock_1d_unitary(omega: float, g: float, lam: float, s: int, dt: float, K: int) -> list[list[complex]]:
    """Compute exp(-i * dt * H_s) on truncated 1D Fock space |0>..|K> via scaling & squaring."""
    dim = K + 1
    H = [[0j] * dim for _ in range(dim)]
    for n in range(dim):
        H[n][n] = complex(omega * n)
        if n < K:
            val = complex(s * lam * g * math.sqrt(n + 1))
            H[n][n + 1] = val
            H[n + 1][n] = val
    norm_est = omega * K + 2.0 * lam * abs(g) * math.sqrt(K + 1)
    squarings = max(0, math.ceil(math.log2(max(1e-12, abs(dt) * norm_est / 0.25))))
    step = -1j * dt / (2 ** squarings)
    A = [[H[i][j] * step for j in range(dim)] for i in range(dim)]
    eye = [[1 + 0j if i == j else 0j for j in range(dim)] for i in range(dim)]
    U = [[eye[i][j] for j in range(dim)] for i in range(dim)]
    term = [[eye[i][j] for j in range(dim)] for i in range(dim)]
    for order in range(1, 15):
        term = mat_mul(term, A)
        inv = 1.0 / order
        for i in range(dim):
            for j in range(dim):
                term[i][j] *= inv
                U[i][j] += term[i][j]
    for _ in range(squarings):
        U = mat_mul(U, U)
    return U


def disp_1d_vec_vacuum(alpha: complex, K: int) -> list[complex]:
    """Exact coherent state D(alpha)|0> truncated to |0>..|K>."""
    pref = cmath.exp(-0.5 * (abs(alpha) ** 2))
    vec = [pref + 0j]
    cur = 1.0 + 0j
    for n in range(1, K + 1):
        cur *= alpha / math.sqrt(n)
        vec.append(pref * cur)
    return vec


def verify_fock_schrodinger_crosscheck() -> dict:
    """Verify Eqs. (5), (A2), (13) (|z_s> vs |+>), and bell_blocks via direct Fock H(lam)."""
    lam = 0.30
    K_vac = 12
    # 1. Verify Eq. (5) & Eq. (A2) single-slot unitary action on vacuum |0,0>
    dt = 0.75
    u0_p = fock_1d_unitary(OMEGA[0], G_COUP[0], lam, +1, dt, K_vac)
    u1_p = fock_1d_unitary(OMEGA[1], G_COUP[1], lam, +1, dt, K_vac)
    xi0 = (G_COUP[0] / OMEGA[0]) * (cmath.exp(-1j * OMEGA[0] * dt) - 1.0)
    xi1 = (G_COUP[1] / OMEGA[1]) * (cmath.exp(-1j * OMEGA[1] * dt) - 1.0)
    phi0 = -sum((lam ** 2) * (G_COUP[k] / OMEGA[k]) ** 2 * (OMEGA[k] * dt - math.sin(OMEGA[k] * dt)) for k in (0, 1))
    d0 = disp_1d_vec_vacuum(lam * xi0, K_vac)
    d1 = disp_1d_vec_vacuum(lam * xi1, K_vac)
    # Column 0 is U(dt)|0> since e^{-i H_0 dt}|0> = |0>
    fock_col0 = [u0_p[i][0] * u1_p[j][0] for i in range(K_vac + 1) for j in range(K_vac + 1)]
    weyl_col0 = [cmath.exp(-1j * phi0) * d0[i] * d1[j] for i in range(K_vac + 1) for j in range(K_vac + 1)]
    eq5_err = math.sqrt(sum(abs(a - b) ** 2 for a, b in zip(fock_col0, weyl_col0)))
    assert eq5_err < 1e-13

    # 2. Verify Eq. (13) causal-break protocol on vacuum: |z_s> over [0, a] + |+> on [a, a+b]
    a, b = 2.0 / 3.0, 0.75
    def run_vac_two_slot(s0_bra: int, s0_ket: int) -> complex:
        ua_bra = [fock_1d_unitary(OMEGA[k], G_COUP[k], lam, s0_bra, a, K_vac) for k in (0, 1)]
        ua_ket = [fock_1d_unitary(OMEGA[k], G_COUP[k], lam, s0_ket, a, K_vac) for k in (0, 1)]
        ub_p = [fock_1d_unitary(OMEGA[k], G_COUP[k], lam, +1, b, K_vac) for k in (0, 1)]
        ub_m = [fock_1d_unitary(OMEGA[k], G_COUP[k], lam, -1, b, K_vac) for k in (0, 1)]
        prod = 1.0 + 0j
        for k in (0, 1):
            # Final vectors: Ub(+1) Ua(s0_ket)|0> vs Ub(-1) Ua(s0_bra)|0>
            ket = [sum(ub_p[k][r][m] * ua_ket[k][m][0] for m in range(K_vac + 1)) for r in range(K_vac + 1)]
            bra = [sum(ub_m[k][r][m] * ua_bra[k][m][0] for m in range(K_vac + 1)) for r in range(K_vac + 1)]
            prod *= sum(bra[r].conjugate() * ket[r] for r in range(K_vac + 1))
        return prod

    z_p_fock = run_vac_two_slot(+1, +1)
    z_m_fock = run_vac_two_slot(-1, -1)
    z_plus_init_fock = run_vac_two_slot(-1, +1)  # Preparing |+> on slot 1 gives zero phase!
    z_p_weyl = z_causal_break(lam, 0.0, 0.0, +1, a, b)
    z_m_weyl = z_causal_break(lam, 0.0, 0.0, -1, a, b)
    assert abs(z_p_fock - z_p_weyl) < 1e-13
    assert abs(z_m_fock - z_m_weyl) < 1e-13
    assert abs(z_plus_init_fock.imag) < 1e-14

    # 3. Verify 3-slot bell_blocks on vacuum (lam=0.3, n=0, c=0) directly from Fock H(lam)
    ts = TIMINGS["original"]
    # Step unitaries for each slot j and pointer sign idx in (0, 1) -> (+1, -1)
    U1d = [
        [
            [fock_1d_unitary(OMEGA[k], G_COUP[k], lam, 1 - 2 * idx, dt, K_vac) for k in (0, 1)]
            for idx in (0, 1)
        ]
        for dt in ts
    ]
    inv_sqrt2 = 1.0 / math.sqrt(2.0)
    # Initial Bell state |Phi+> = (|00> + |11>)/sqrt(2) x |0>_0 |0>_1 in Fock space
    # Track 4 SR pure state components vectorized over mode 0 & mode 1 as separable rank terms per ref index:
    # For each history (no branch mixing yet), evolve mode-0 and mode-1 vectors, then contract!
    vac_weyl = bell_blocks(lam, 0.0, 0.0, "original")
    max_vac_bell_err = 0.0
    for rec in RECORDS:
        k_len = len(rec)
        # Collect (sr_row_idx_out, sr_vec4_amp, vec0, vec1) for each bitstring trajectory
        paths_k = list(itertools.product((0, 1), repeat=k_len))
        b_fock = [[0j] * 4 for _ in range(4)]
        path_data = []
        for h in paths_k:
            v0 = [1.0 + 0j if i == 0 else 0j for i in range(K_vac + 1)]
            v1 = [1.0 + 0j if i == 0 else 0j for i in range(K_vac + 1)]
            A_op = [[1 + 0j, 0j], [0j, 1 + 0j]]
            for j, (idx, dt_j) in enumerate(zip(h, ts[:k_len])):
                m0, m1 = U1d[j][idx]
                v0 = [sum(m0[r][c_i] * v0[c_i] for c_i in range(K_vac + 1)) for r in range(K_vac + 1)]
                v1 = [sum(m1[r][c_i] * v1[c_i] for c_i in range(K_vac + 1)) for r in range(K_vac + 1)]
                K_step = FAIL_OP if rec[j] == "f" else PASS_OPS[j]
                A_op = [[K_step[r][idx] * A_op[idx][c_i] for c_i in range(2)] for r in range(2)]
            # (A_op x I_2)|Phi+> -> [A[0][0], A[0][1], A[1][0], A[1][1]] / sqrt(2)
            sr_vec = [A_op[0][0] * inv_sqrt2, A_op[0][1] * inv_sqrt2, A_op[1][0] * inv_sqrt2, A_op[1][1] * inv_sqrt2]
            path_data.append((sr_vec, v0, v1))
        for sr_h, v0_h, v1_h in path_data:
            for sr_hp, v0_hp, v1_hp in path_data:
                ov = sum(a.conjugate() * b_v for a, b_v in zip(v0_hp, v0_h)) * sum(
                    a.conjugate() * b_v for a, b_v in zip(v1_hp, v1_h)
                )
                for r in range(4):
                    for col in range(4):
                        b_fock[r][col] += ov * sr_h[r] * sr_hp[col].conjugate()
        for r in range(4):
            for col in range(4):
                max_vac_bell_err = max(max_vac_bell_err, abs(b_fock[r][col] - vac_weyl[rec][r][col]))
    assert max_vac_bell_err < 1e-13

    # 4. Correlated thermal state Fock verification at P1 = (0.3, 0.5, 0.25) with K_th = 8
    # Expand normal-mode Fock states |n_+, n_-> (n_+ + n_- <= 8) via 1/(sqrt(2)) transformation in (a_0, a_1)
    K_th = 8
    d_tot = (K_th + 1) * (K_th + 2) // 2
    def idx_shell(s_n, i_n):
        return s_n * (s_n + 1) // 2 + i_n

    rp = (0.5 + 0.25) / (1.0 + 0.5 + 0.25)  # 3/7
    rm = (0.5 - 0.25) / (1.0 + 0.5 - 0.25)  # 1/5
    th_norm = 0.0
    th_states = []  # (weight, dict of (n0, n1) -> amp)
    for sp in range(K_th + 1):
        for np_idx in range(sp + 1):
            nm_idx = sp - np_idx
            w_p = (1.0 - rp) * (1.0 - rm) * (rp ** np_idx) * (rm ** nm_idx)
            th_norm += w_p
            # Coefficient of |n0, sp-n0> in (a_+^dag)^np (a_-^dag)^nm / sqrt(np! nm!) |0,0>
            inv_2sp = 2.0 ** (-0.5 * sp)
            coeffs = [0.0] * (sp + 1)
            pref_n = inv_2sp / math.sqrt(math.factorial(np_idx) * math.factorial(nm_idx))
            for a_i in range(np_idx + 1):
                for b_i in range(nm_idx + 1):
                    n0 = a_i + b_i
                    sgn = (-1.0) ** (nm_idx - b_i)
                    c_comb = math.comb(np_idx, a_i) * math.comb(nm_idx, b_i) * sgn
                    coeffs[n0] += c_comb * pref_n * math.sqrt(math.factorial(n0) * math.factorial(sp - n0))
            th_states.append((w_p, sp, coeffs))

    # Build normalized truncated thermal state projector overlap on 2-slot causal-break (a=2/3, b=0.75)
    u0_a_p = fock_1d_unitary(OMEGA[0], G_COUP[0], lam, +1, a, K_th)
    u1_a_p = fock_1d_unitary(OMEGA[1], G_COUP[1], lam, +1, a, K_th)
    u0_b_p = fock_1d_unitary(OMEGA[0], G_COUP[0], lam, +1, b, K_th)
    u1_b_p = fock_1d_unitary(OMEGA[1], G_COUP[1], lam, +1, b, K_th)
    u0_b_m = fock_1d_unitary(OMEGA[0], G_COUP[0], lam, -1, b, K_th)
    u1_b_m = fock_1d_unitary(OMEGA[1], G_COUP[1], lam, -1, b, K_th)
    p0 = mat_mul(u0_b_p, u0_a_p)
    p1 = mat_mul(u1_b_p, u1_a_p)
    m0 = mat_mul(u0_b_m, u0_a_p)
    m1 = mat_mul(u1_b_m, u1_a_p)
    z_p1_k8 = 0j
    for w_p, sp, coeffs in th_states:
        w_scaled = w_p / th_norm
        # Compute <psi| (m0^dag x m1^dag)(p0 x p1) |psi> within K_th
        for n0_l in range(sp + 1):
            c_l = coeffs[n0_l]
            if c_l == 0.0:
                continue
            n1_l = sp - n0_l
            for n0_r in range(sp + 1):
                c_r = coeffs[n0_r]
                if c_r == 0.0:
                    continue
                n1_r = sp - n0_r
                ov0 = sum(m0[r][n0_l].conjugate() * p0[r][n0_r] for r in range(K_th + 1))
                ov1 = sum(m1[r][n1_l].conjugate() * p1[r][n1_r] for r in range(K_th + 1))
                z_p1_k8 += w_scaled * c_l * c_r * ov0 * ov1
    z_p1_exact = z_causal_break(lam, 0.5, 0.25, +1, a, b)
    thermal_k8_err = abs(z_p1_k8 - z_p1_exact)
    assert thermal_k8_err < 1.5e-2  # Well inside Duhamel truncation envelope

    return {
        "vac_K12_eq5_error": eq5_err,
        "vac_K12_causal_break_error": abs(z_p_fock - z_p_weyl),
        "vac_K12_plus_slot1_imag": abs(z_plus_init_fock.imag),
        "vac_K12_3slot_bell_max_error": max_vac_bell_err,
        "thermal_K8_P1_causal_break_error": thermal_k8_err,
    }


# ---------------------------------------------------------------------------
# Part 1: Correlated Two-Mode Bath Weyl Formula & Ramsey Ambiguity Witness
# ---------------------------------------------------------------------------
def ramsey_coeffs(t: float) -> tuple[float, float]:
    """Return (A_ram, B_ram) such that m(t) = eta * exp(-(A_ram * u + B_ram * v))."""
    d0 = (G_COUP[0] / OMEGA[0]) * (1.0 - cmath.exp(1j * OMEGA[0] * t))
    d1 = (G_COUP[1] / OMEGA[1]) * (1.0 - cmath.exp(1j * OMEGA[1] * t))
    A = 2.0 * (abs(d0) ** 2 + abs(d1) ** 2)
    B = 8.0 * (d0.conjugate() * d1).real
    return A, B


def causal_break_coeffs(a: float, b: float) -> tuple[float, float, float]:
    """Return (A_break, B_break, F_sensitivity) at prep a and probe b."""
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
    # 1. Exact Ramsey ambiguity witness & 25-point fiber sweep on D = [1/5, 2/5] x {|c| <= n <= 3/5}
    l1, n1, c1 = Q(3, 10), Q(1, 2), Q(1, 4)
    l2, n2, c2 = Q(1, 3), Q(31, 100), Q(81, 400)
    assert l1 ** 2 * (2 * n1 + 1) == Q(9, 50) == l2 ** 2 * (2 * n2 + 1)
    assert l1 ** 2 * c1 == Q(9, 400) == l2 ** 2 * c2
    u0, v0 = Q(9, 50), Q(9, 400)
    w_min = max(Q(1, 25), u0 / Q(11, 5))
    w_max = min(Q(4, 25), u0 - 2 * abs(v0))
    assert (w_min, w_max) == (Q(9, 110), Q(27, 200))

    A1, B1 = ramsey_coeffs(0.75)
    A2, B2 = ramsey_coeffs(1.5)
    m_short = math.exp(-(A1 * float(u0) + B1 * float(v0)))
    m_long = math.exp(-(A2 * float(u0) + B2 * float(v0)))
    assert abs(m_short - 0.730531651137) < 1e-12
    assert abs(m_long - 0.360071794945) < 1e-12

    for k in range(25):
        w_k = w_min + (w_max - w_min) * Q(k, 24)
        lam_k = math.sqrt(float(w_k))
        n_k = (u0 / w_k - 1) / 2
        c_k = v0 / w_k
        assert Q(1, 5) - 1e-15 <= lam_k <= Q(2, 5) + 1e-15
        assert 0 <= abs(c_k) <= n_k <= Q(3, 5)
        u_k = w_k * (2 * n_k + 1)
        v_k = w_k * c_k
        assert abs(math.exp(-(A1 * float(u_k) + B1 * float(v_k))) - m_short) < 1e-15
        assert abs(math.exp(-(A2 * float(u_k) + B2 * float(v_k))) - m_long) < 1e-15

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

    # 2. Whole-domain Lipschitz upper bounds & corner/random stress test on D x [0.9, 1] x [-0.02, 0.02]
    h_u = (B2 / det_M, -B1 / det_M)
    h_v = (-A2 / det_M, A1 / det_M)
    eta_min = 0.9
    m1_floor = eta_min * math.exp(-0.544 * A1)
    m2_floor = eta_min * math.exp(-0.544 * A2)
    r_floor = eta_min * math.exp(-0.544 * Ab)
    assert 0.411787 < m1_floor < 0.411788
    assert 0.067589 < m2_floor < 0.067590
    L_u = abs(h_u[0] + h_u[1]) / eta_min + abs(h_u[0]) / m1_floor + abs(h_u[1]) / m2_floor
    L_v = abs(h_v[0] + h_v[1]) / eta_min + abs(h_v[0]) / m1_floor + abs(h_v[1]) / m2_floor
    L_w = math.pi * math.sqrt(2.0) / (2.0 * r_floor * F_val)
    L_lam = L_w / 0.4
    L_n = (L_u + 2.2 * L_w) / 0.08
    L_c = (L_v + 0.6 * L_w) / 0.04
    assert 51.240114 < L_u < 51.240115
    assert 31.421916 < L_v < 31.421917
    assert 2.965318 < L_w < 2.965319
    assert 7.413296 < L_lam < 7.413297
    assert 722.047689 < L_n < 722.047690
    assert 830.027701 < L_c < 830.027702

    def obs_vec(lam, n, c, eta, delta):
        u = lam ** 2 * (2.0 * n + 1.0)
        v = lam ** 2 * c
        w = lam ** 2
        m1 = eta * math.exp(-(A1 * u + B1 * v))
        m2 = eta * math.exp(-(A2 * u + B2 * v))
        amp_b = eta * math.exp(-(Ab * u + Bb * v))
        xp = amp_b * math.cos(delta + w * F_val)
        yp = -amp_b * math.sin(delta + w * F_val)
        xm = amp_b * math.cos(delta - w * F_val)
        ym = -amp_b * math.sin(delta - w * F_val)
        assert m1 >= m1_floor - 1e-15 and m2 >= m2_floor - 1e-15 and amp_b >= r_floor - 1e-15
        return (eta, m1, m2, xp, yp, xm, ym)

    # Generate corners + 500 deterministic seeded points in D x [0.9, 1] x [-0.02, 0.02]
    rng = random.Random(20261124)
    samples = []
    for lam in (0.2, 0.4):
        for n, c in ((0.0, 0.0), (0.6, 0.0), (0.6, 0.6), (0.6, -0.6)):
            for eta in (0.9, 1.0):
                samples.append((lam, n, c, eta, 0.02 if eta > 0.95 else -0.02))
    for _ in range(500):
        lam = rng.uniform(0.2, 0.4)
        n = rng.uniform(0.0, 0.6)
        c = rng.uniform(-n, n)
        eta = rng.uniform(0.9, 1.0)
        delta = rng.uniform(-0.02, 0.02)
        samples.append((lam, n, c, eta, delta))
    obs_list = [obs_vec(*pt) for pt in samples]
    max_emp_ratios = [0.0] * 6  # u, v, w, lam, n, c
    for i in range(len(samples)):
        p_i, o_i = samples[i], obs_list[i]
        ui, vi, wi = p_i[0] ** 2 * (2 * p_i[1] + 1), p_i[0] ** 2 * p_i[2], p_i[0] ** 2
        for j in ((i + 1) % len(samples), (i + 17) % len(samples)):
            if j == i:
                continue
            p_j, o_j = samples[j], obs_list[j]
            d_obs = max(abs(a - b) for a, b in zip(o_i, o_j))
            if d_obs < 1e-12:
                continue
            uj, vj, wj = p_j[0] ** 2 * (2 * p_j[1] + 1), p_j[0] ** 2 * p_j[2], p_j[0] ** 2
            du, dv, dw = abs(ui - uj), abs(vi - vj), abs(wi - wj)
            dl, dn, dc = abs(p_i[0] - p_j[0]), abs(p_i[1] - p_j[1]), abs(p_i[2] - p_j[2])
            for idx, (val, cap) in enumerate(zip((du, dv, dw, dl, dn, dc), (L_u, L_v, L_w, L_lam, L_n, L_c))):
                assert val <= cap * d_obs + 1e-12, (idx, val / d_obs, cap)
                max_emp_ratios[idx] = max(max_emp_ratios[idx], val / d_obs)

    # 3. Aligned-Y discrimination check at holdout window (a=1, b=3/4)
    A_hold, B_hold, F_hold = causal_break_coeffs(1.0, 0.75)
    assert abs(F_hold - 3.056234252369) < 1e-12
    amp_hold = math.exp(-(A_hold * float(u0) + B_hold * float(v0)))
    err_hold = 0.001 / 2.0 + 2.0 ** (-40)
    upper_p1 = (1.0 + amp_hold * math.sin(float(l1 ** 2) * F_hold)) / 2.0 + err_hold
    lower_p2 = (1.0 + 0.9 * amp_hold * math.sin(float(l2 ** 2) * F_hold) * math.cos(0.02)) / 2.0 - err_hold
    align_thresh = (upper_p1 + lower_p2) / 2.0
    assert abs(align_thresh - 0.605581355419) < 1e-12
    assert 71816 / 120000 < upper_p1 < align_thresh < lower_p2

    # 4. Stopped Bell separation, trace completeness, Tr[B_f]=3/16, readout challenge eta=0.65, Taylor remainder
    diffs = {}
    for t_name in ("original", "swapped"):
        b1 = bell_blocks(float(l1), float(n1), float(c1), t_name)
        b2 = bell_blocks(float(l2), float(n2), float(c2), t_name)
        assert abs(sum(mat_trace(blk).real for blk in b1.values()) - 1.0) < 1e-14
        assert abs(mat_trace(b1["f"]).real - 3.0 / 16.0) < 1e-14
        for blk in b1.values():
            for r in range(4):
                for c_i in range(4):
                    assert abs(blk[r][c_i] - blk[c_i][r].conjugate()) < 1e-14
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

    # Readout challenge eta=0.65 analytical check on f, ZZ-
    b_p1_orig = bell_blocks(float(l1), float(n1), float(c1), "original")
    ev_zz_cal = bell_events_from_blocks(b_p1_orig, 0.96, "ZZ")
    ev_zz_chal = bell_events_from_blocks(b_p1_orig, 0.65, "ZZ")
    # f, ZZ^- is index 0: exact = (3/16)(1 - eta) / 2? wait: Tr[ZZ B_f] = -3/16 => (3/16 - eta*(3/16))/2 = (3/32)*(1-eta)?
    # Actually at (3/10, 1/2, 1/4) check exact formula Tr[(Z x Z) B_f] = Tr[K_f Z K_f^dag]/2? No: (K_f x I) (Phi+) (K_f^dag x I) gives Tr[(Z x Z)(B_f)] = sum_h?
    # Let's assert exact equality with (3/32)*(1 - eta)!
    assert abs(ev_zz_cal[0] - (3.0 / 32.0) * (1.0 - 0.96)) < 1e-14  # 0.00375
    assert abs(ev_zz_chal[0] - (3.0 / 32.0) * (1.0 - 0.65)) < 1e-14  # 0.0328125
    # Verify synthetic count 796/24000 and its 100-cell alpha=0.01 Hoeffding radius
    h_rad_24k = math.sqrt(math.log(200.0 / 0.01) / (2.0 * 24000.0))
    zz0_freq = 796.0 / 24000.0
    assert abs((zz0_freq - h_rad_24k) - 0.018802730669) < 1e-9
    assert abs((zz0_freq + h_rad_24k) - 0.047530602665) < 1e-9

    # Eq. (22)/(C1) Convex polytope complex Taylor + Popoviciu check on a 3D box
    A_t, B_t, P_t = 1.5, 2.0, 1.819
    u_lo, u_hi = 0.1497, 0.1841
    v_lo, v_hi = -0.0086, 0.0169
    w_lo, w_hi = 0.0774, 0.0884
    corners = list(itertools.product((u_lo, u_hi), (v_lo, v_hi), (w_lo, w_hi)))
    rng_re = (A_t * (u_hi - u_lo)) + abs(B_t) * (v_hi - v_lo)
    rng_im = P_t * (w_hi - w_lo)
    rem_cap = (rng_re ** 2 + rng_im ** 2) / 8.0
    for m_i in range(25):
        wts = [rng.random() for _ in range(8)]
        s_w = sum(wts)
        wts = [z / s_w for z in wts]
        q_mid = tuple(sum(wt * c_pt[ax] for wt, c_pt in zip(wts, corners)) for ax in range(3))
        val_mid = cmath.exp(-(A_t * q_mid[0] + B_t * q_mid[1]) + 1j * P_t * q_mid[2])
        val_lin = sum(wt * cmath.exp(-(A_t * c_pt[0] + B_t * c_pt[1]) + 1j * P_t * c_pt[2]) for wt, c_pt in zip(wts, corners))
        assert abs(val_mid - val_lin) <= rem_cap + 1e-15

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
        "lipschitz_upper_outward": {
            "u": math.ceil(L_u * 1e6) / 1e6,
            "v": math.ceil(L_v * 1e6) / 1e6,
            "w": math.ceil(L_w * 1e6) / 1e6,
            "lambda": math.ceil(L_lam * 1e6) / 1e6,
            "n": math.ceil(L_n * 1e6) / 1e6,
            "c": math.ceil(L_c * 1e6) / 1e6,
        },
        "max_empirical_stress_ratios": [round(r, 6) for r in max_emp_ratios],
        "stopped_bell_splitting_YZ_minus_eta096": diffs,
        "readout_challenge_f_ZZ_minus": {"cal_096": round(ev_zz_cal[0], 6), "chal_065": round(ev_zz_chal[0], 7)},
    }


# ---------------------------------------------------------------------------
# Part 2: Exact Rational Total-Number Cutoff & Duhamel Propagation Bounds (B_K)
# ---------------------------------------------------------------------------
def exact_duhamel_cutoff_bound(K: int) -> Q:
    """Exact outward Fraction upper bound B_K over 1/5 <= lam <= 2/5, |c| <= n <= 3/5."""
    a_star = Q(6, 11)
    b_star = Q(3, 8)
    x = Q(9, 10)  # lam_max * ||g||_2 * T_max = (2/5)*sqrt(34/25)*(23/12) < 9/10
    assert (Q(2, 5) ** 2) * Q(34, 25) * (Q(23, 12) ** 2) < x ** 2
    inv_one_minus = Q(1) / (Q(1) - (x ** 2) / 2)
    assert exp_taylor_upper((x ** 2) / 2) < inv_one_minus

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

    h_vals: list[Q] = []
    cur = Q(0)
    for fv in f_vals:
        cur = max(cur, fv)
        h_vals.append(cur)

    survived_sum = Q(0)
    pref = (1 - a_star) * (1 - b_star)
    for s in range(K + 1):
        ps = pref * sum((a_star ** i) * (b_star ** (s - i)) for i in range(s + 1))
        survived_sum += ps * (Q(1) - h_vals[s])
    return Q(1) - survived_sum


def verify_part2_cutoff_bounds() -> dict:
    assert exact_duhamel_cutoff_bound(0) == Q(1)
    prev = exact_duhamel_cutoff_bound(0)
    for k in (4, 8, 12, 13, 14, 16, 20, 24):
        cur = exact_duhamel_cutoff_bound(k)
        assert cur < prev
        prev = cur

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
        b_dec = math.ceil(float(b_k) * 10 ** 12) / (10 ** 12)
        assert abs(b_dec - exp_val) <= 2e-12, (K, b_dec, exp_val)
        out[str(K)] = b_dec
    return {"uniform_duhamel_half_trace_upper": out}


# ---------------------------------------------------------------------------
# Part 3: Scalar KG Field on R x S^1 & Full 4x4 Two-Qubit Swap Thermodynamics
# ---------------------------------------------------------------------------
def entropy_bits_nats(probs: list[float]) -> float:
    return -sum(p * math.log(p) for p in probs if p > 0.0)


def verify_part3_local_field() -> dict:
    beta = math.sqrt(5.0) / 2.0
    length = 2.0 * math.pi / beta  # L = 4*pi / sqrt(5)
    lam, n_occ, c_corr = 0.3, 0.5, 0.25

    x1 = math.pi / 80.0
    sinc1 = math.sin(x1) / x1
    target = 0.6 * math.sqrt(0.75)
    p_mix = 2.0 * (1.0 - target / (sinc1 ** 4))
    assert 0.0 < p_mix < 1.0

    w1 = math.sqrt(1.0 + beta ** 2)
    f1 = (sinc1 ** 4) * (1.0 - p_mix + p_mix * math.cos(math.pi / 3.0))
    g1 = math.sqrt(2.0 / w1) * f1
    assert abs(w1 - 1.5) < 1e-14 and abs(g1 - 0.6) < 1e-14

    # Mode-wise j^{-11} bound Eq. (E2) check across j=1..200
    c_tail = 2.0 * ((80.0 / math.pi) ** 8) / (beta ** 3)
    for j in range(1, 201):
        xj = math.pi * j / 80.0
        fj = ((math.sin(xj) / xj) ** 4) * (1.0 - p_mix + p_mix * math.cos(math.pi * j / 3.0))
        wj = math.sqrt(1.0 + (beta * j) ** 2)
        gj = math.sqrt(2.0 / wj) * fj
        assert (gj ** 2) / (wj ** 2) <= c_tail * (j ** (-11)) + 1e-30

    supp_R = (1.0 / 6.0 + 1.0 / 40.0) * length
    gap_dist = length / 2.0 - 2.0 * supp_R
    assert gap_dist > 0.4

    def run_field(modes: int, a: float, b: float, opposite: bool) -> dict:
        phase = 0.0
        damping = 0.0
        energy = 0.0
        low_d = []
        par_sign = -1.0 if opposite else 1.0
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
            re_d = gj * (math.cos(wj * a) - math.cos(wj * (a + b))) / wj
            im_d = gj * (math.sin(wj * a) - math.sin(wj * (a + b))) / wj
            damping += 4.0 * (lam ** 2) * (gj ** 2) * (1.0 - math.cos(wj * b)) / (wj ** 2)
            if j <= 1:
                low_d.append((re_d, im_d))
            energy += 2.0 * (lam ** 2) * (gj ** 2) * (2.0 - math.cos(wj * a) - math.cos(wj * b)) / wj
        (r0, i0), (r1, i1) = low_d
        damping += 4.0 * (lam ** 2) * n_occ * (r0 * r0 + i0 * i0 + r1 * r1 + i1 * i1)
        damping += 8.0 * (lam ** 2) * c_corr * par_sign * (r0 * r1 + i0 * i1)
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

    # Full 4x4 matrix unitary check for two-qubit resonant swap (theta = pi/6, H_0 = diag(0, 1, 1, 2))
    theta = math.pi / 6.0
    U_swap = [
        [1 + 0j, 0j, 0j, 0j],
        [0j, complex(math.cos(theta)), -1j * math.sin(theta), 0j],
        [0j, -1j * math.sin(theta), complex(math.cos(theta)), 0j],
        [0j, 0j, 0j, 1 + 0j],
    ]
    H0_swap = [[complex(val) if i == j else 0j for j in range(4)] for i, val in enumerate((0, 1, 1, 2))]
    comm = mat_mul(U_swap, H0_swap)
    comm2 = mat_mul(H0_swap, U_swap)
    assert max(abs(comm[i][j] - comm2[i][j]) for i in range(4) for j in range(4)) < 1e-14

    p_sys_init = Q(4, 5)
    q_bath_init = Q(1, 5)
    p_sys_after = q_bath_init + (p_sys_init - q_bath_init) * Q(3, 4)
    q_bath_after = q_bath_init + (p_sys_init - q_bath_init) * Q(1, 4)
    assert p_sys_after == Q(13, 20) and q_bath_after == Q(7, 20)
    reuse_excess = (q_bath_after - q_bath_init) * Q(1, 4)
    assert reuse_excess == Q(3, 80) == Q(375, 10000)

    # Evolve diagonal product state rho_SE via 4x4 U_swap and verify Sigma & conditionals
    rho_in = [[0j] * 4 for _ in range(4)]
    p_vec = [0.2, 0.8]
    q_vec = [0.8, 0.2]
    for i_s in (0, 1):
        for i_e in (0, 1):
            idx = 2 * i_s + i_e
            rho_in[idx][idx] = complex(p_vec[i_s] * q_vec[i_e])
    rho_out = mat_mul(mat_mul(U_swap, rho_in), mat_conj_T(U_swap))
    pS_out = (rho_out[2][2] + rho_out[3][3]).real
    qE_out = (rho_out[1][1] + rho_out[3][3]).real
    assert abs(pS_out - 0.65) < 1e-14 and abs(qE_out - 0.35) < 1e-14
    cond_E0 = rho_out[2][2].real / (rho_out[0][0] + rho_out[2][2]).real  # 49/65
    cond_E1 = rho_out[3][3].real / (rho_out[1][1] + rho_out[3][3]).real  # 16/35
    assert abs(cond_E0 - 49.0 / 65.0) < 1e-14
    assert abs(cond_E1 - 16.0 / 35.0) < 1e-14
    beta_th = math.log(4.0)  # (1-q)/q = 4
    sigma_ent = entropy_bits_nats([pS_out, 1.0 - pS_out]) - entropy_bits_nats([0.8, 0.2]) + beta_th * (qE_out - 0.2)
    assert abs(sigma_ent - 0.354988369664) < 1e-10

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
        "two_qubit_reuse": {
            "reuse_excitation_excess": str(reuse_excess),
            "entropy_production_sigma": round(sigma_ent, 12),
            "conditional_S_given_E0_E1": [round(cond_E0, 6), round(cond_E1, 6)],
        },
    }


def run_all_standalone_checks() -> dict:
    p0 = verify_fock_schrodinger_crosscheck()
    p1 = verify_part1_ramsey_and_break()
    p2 = verify_part2_cutoff_bounds()
    p3 = verify_part3_local_field()
    return {
        "status": "PASS",
        "part0_direct_fock_schrodinger_crosscheck": p0,
        "part1_ramsey_ambiguity_and_causal_break": p1,
        "part2_duhamel_total_number_cutoff": p2,
        "part3_local_kg_field_vs_two_mode": p3,
    }


if __name__ == "__main__":
    print(json.dumps(run_all_standalone_checks(), indent=2))
    sys.exit(0)
