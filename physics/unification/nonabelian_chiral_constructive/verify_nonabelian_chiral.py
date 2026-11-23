"""P-NONABELIAN-CHIRAL-08 Certificate: Non-Abelian SU(2) 4D Neuberger Overlap, Kramers Pseudoreality, Dai-Freed Mod-16 & Constructive Continuum Boundary.

Certifies in 40-digit outward interval arithmetic (`mpmath.iv`, `iv.dps = 40`):
1. Explicit 4D Euclidean 2^4 non-Abelian SU(2) Neuberger Overlap operator D_ov = (1/a)(I + X(X^dagger X)^{-1/2})
   (16 spacetime sites x 4 Dirac spinors x 2 SU(2) fundamental colors = 128x128 complex interval matrix,
   a = 1/2, m_0 = 3/2) on an exact rational Cayley SU(2) link configuration U_mu(x) in SU(2):
   - Genuine non-Abelian curvature: ||[U_1(0), U_2(0)]||_F > 5e-5 > 0,
   - Strict Luscher admissibility: max_p ||I_2 - U_p||_F < 1/30 (strictly inside eps_adm = 1/30),
   - Rigorous Sylvester/Riccati 40-digit outward-interval enclosure of (X^dagger X)^{-1/2} (128x128),
   - Deformed non-Abelian chirality involution ||hat_gamma_5^2 - I_128||_F < 1e-28,
   - Luscher asymmetric chiral gauge factorization ||P_+ D_ov hat_P_- - D_ov hat_P_-||_F < 1e-28,
   - Non-Abelian SU(2) gauge covariance of D_ov(U^g) (constructed independently from X(U^g) via its own
     Sylvester/Riccati inverse-sqrt enclosure!) and Luscher projector ||hat_P_-(U^g) - G hat_P_-(U) G^dagger||_F < 1e-28,
     plus zero gauge-orbit chiral index drift |Ind(D_ov(U^g)) - Ind(D_ov(U))| < 1e-29 under a non-commuting
     site-dependent SU(2) gauge transformation G,
   - Exact real structure J = C_E tensor i tau_2 (C_E^2 = -I_4, (i tau_2)^2 = -I_2 -> J^2 = +I_128):
     ||J D_ov(U) J^{-1} - conj(D_ov(U))||_F < 1e-28, algebraically implying Im det D_ov(U) = 0 and
     reducing single-doublet chiral Weyl phase ambiguity to Witten's Z_2 = {+1, -1} Pfaffian sign!
2. Witten pi_4(SU(2)) = Z_2 & Mod-16 Dai-Freed Omega_5^Spin(BZ_4) = Z_16 Anomaly Audit:
   - Witten SU(2)_L doublet parity: quark-only N_d = 3 gives Z_0 + (-1)^3 Z_0 = 0 (Z_chiral = 0), whereas
     (3,3,1) SM N_d = 3 + 1 = 4 (and 3 * 4 = 12) gives exact (+1) Pfaffian invariance,
   - Mod-16 Spin^{Z_4} (Q_X = 5(B - L) - 4 Y) Majorana-vs-Dirac dichotomy: N_Weyl = 15 has 15 mod 16 = 15 != 0
     (Tr Q_X = -5, Tr Q_X^3 = -125, obstructing gauged Z_4 subset U(1)_{B-L} while allowing Weinberg Majorana
     (LH)^2/Lambda under unbroken (-1)^F), whereas N_Weyl = 16 (adding 1 sterile nu_R^c with Q_X = +5) gives
     16 mod 16 = 0, Tr Q_X = 0, and Tr Q_X^3 = 0 simultaneously.
3. Non-Abelian Asymptotic Freedom (1-loop b_0, 2-loop b_1), Plaquette Defect Suppression (a Lambda_MS)^{2 c b_0},
   & Clay 4D Constructive Continuum Boundary:
   - Exact 3-generation (3,3,1) betas: SU(3)_c (b_0 = 7, b_1 = 26 > 0), SU(2)_L (b_0 = 19/6, b_1 = -35/6),
   - Outward 40-digit bounds on (a Lambda_MS)^{2 c_adm b_0} across UV lattice scales, alongside the explicit
     entropy-vs-action exponent gap 2 c_adm b_0 - 4 < 0 at eps_adm = 1/30 keeping infinite-volume 4D continuum
     non-Abelian chiral gauge existence explicitly OPEN ("physical_unification": "OPEN").
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path
import sys
from mpmath import iv, mp
from mpmath.libmp import mpc_add, mpc_conjugate, mpc_mul, mpci_add, mpci_mul

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
for p in (str(REPO), str(HERE.parent)):
    if p not in sys.path:
        sys.path.insert(0, p)

from physics.unification.common import (
    outward_str,
    require,
    sha256_file,
    strictly_above,
    strictly_below,
    write_json,
)

mp.dps = 50
iv.dps = 40


def finish(args: argparse.Namespace, payload: dict, suite_name: str) -> None:
    require(payload.get("physical_unification") == "OPEN", "physical_unification must remain OPEN")
    require(payload.get("device_certified") is False, "device_certified must remain False")
    require(payload.get("status") == "PASS", "suite status must be PASS")
    if args.check:
        require(args.output.is_file(), f"Missing committed certificate: {args.output}")
        committed = json.loads(args.output.read_text())
        require(committed == payload, f"{suite_name} certificate drift against {args.output}")
    else:
        write_json(args.output, payload)


def iv_zeros(n: int) -> list[list]:
    z = iv.mpc(0, 0)
    return [[z for _ in range(n)] for _ in range(n)]


def iv_eye(n: int) -> list[list]:
    z = iv.mpc(0, 0)
    one = iv.mpc(1, 0)
    return [[one if i == j else z for j in range(n)] for i in range(n)]


def iv_conj(z):
    return iv.mpc(z.real, -z.imag)


def iv_conj_matrix(M: list[list]) -> list[list]:
    return [[iv_conj(z) for z in row] for row in M]


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


def iv_scale(c, A: list[list]) -> list[list]:
    sc = c if isinstance(c, type(iv.mpc(0, 0))) else iv.mpc(c, 0)
    n = len(A)
    return [[sc * A[i][j] for j in range(n)] for i in range(n)]


def iv_matmul(A: list[list], B: list[list]) -> list[list]:
    """Bit-identical outward-rounded mpmath.iv complex matrix multiply using libmp.mpci."""
    m = len(A)
    klen = len(A[0])
    n = len(B[0])
    prec = iv.prec
    z_raw = iv.mpc(0, 0)._mpci_
    make_mpc = iv.make_mpc
    A_nz = [[(k, A[i][k]._mpci_) for k in range(klen) if A[i][k]._mpci_ != z_raw] for i in range(m)]
    B_nz = [[(j, B[k][j]._mpci_) for j in range(n) if B[k][j]._mpci_ != z_raw] for k in range(klen)]
    out = []
    for i in range(m):
        acc = [z_raw] * n
        for k, ak in A_nz[i]:
            for j, bkj in B_nz[k]:
                acc[j] = mpci_add(acc[j], mpci_mul(ak, bkj, prec), prec)
        out.append([make_mpc(v) for v in acc])
    return out


def iv_frobenius_norm(M: list[list]):
    s = iv.mpf(0)
    for row in M:
        for z in row:
            s += z.real**2 + z.imag**2
    return iv.sqrt(s)


def iv_trace(M: list[list]):
    s = iv.mpc(0, 0)
    for i in range(len(M)):
        s += M[i][i]
    return s


def cayley_su2_iv(p1: Fraction, p2: Fraction, p3: Fraction) -> list[list]:
    """Exact rational Cayley parameterization (p1, p2, p3) -> U in SU(2) enclosed in 40-digit iv."""
    r2 = p1 * p1 + p2 * p2 + p3 * p3
    d = Fraction(1, 1) + r2
    a_re = (Fraction(1, 1) - r2) / d
    a_im = (2 * p3) / d
    b_re = (2 * p2) / d
    b_im = (2 * p1) / d

    def f2iv(q: Fraction):
        return iv.mpf(q.numerator) / iv.mpf(q.denominator)

    alpha = iv.mpc(f2iv(a_re), f2iv(a_im))
    beta = iv.mpc(f2iv(b_re), f2iv(b_im))
    return [
        [alpha, beta],
        [-iv_conj(beta), iv_conj(alpha)],
    ]


def mp_to_thin_iv_matrix(M_mp: mp.matrix) -> list[list]:
    r = M_mp.rows
    c = M_mp.cols
    out = []
    for i in range(r):
        row = []
        for j in range(c):
            val = M_mp[i, j]
            if val == 0:
                row.append(iv.mpc(0, 0))
            elif isinstance(val, mp.mpc):
                row.append(iv.mpc(mp.nstr(val.real, 50), mp.nstr(val.imag, 50)))
            else:
                row.append(iv.mpc(mp.nstr(val, 50), 0))
        out.append(row)
    return out


def iv_matmul_hermitian(A: list[list], B: list[list]) -> list[list]:
    """Outward-rounded mpmath.iv product C = A @ B when the underlying exact point product is Hermitian.

    Computes upper-triangular entries j >= i in full 40-digit directed interval arithmetic (including full
    complex intervals on the diagonal i == j) and sets C[j][i] = conj(C[i][j]) for j > i, which is a sound
    set-theoretic enclosure whenever the exact underlying point matrix M_* satisfies M_*[j,i] = conj(M_*[i,j]).
    """
    n = len(A)
    klen = len(A[0])
    prec = iv.prec
    z_raw = iv.mpc(0, 0)._mpci_
    make_mpc = iv.make_mpc
    B_raw = [[B[k][j]._mpci_ for j in range(n)] for k in range(klen)]
    A_nz = [[(k, A[i][k]._mpci_) for k in range(klen) if A[i][k]._mpci_ != z_raw] for i in range(n)]
    out = [[None] * n for _ in range(n)]
    for i in range(n):
        acc = [z_raw] * n
        for k, ak in A_nz[i]:
            bk = B_raw[k]
            for j in range(i, n):
                bkj = bk[j]
                if bkj != z_raw:
                    acc[j] = mpci_add(acc[j], mpci_mul(ak, bkj, prec), prec)
        out[i][i] = make_mpc(acc[i])
        for j in range(i + 1, n):
            vij = make_mpc(acc[j])
            out[i][j] = vij
            out[j][i] = iv_conj(vij)
    return out


def enclose_inv_sqrt_hpd_newton_cholesky(A_iv: list[list]) -> tuple[list[list], object, object, list[list]]:
    """Rigorously enclose A^{-1/2} in 40-digit iv using 100% OS-deterministic pure-mpmath Chebyshev-Schulz + Cholesky + Riccati."""
    n = len(A_iv)
    prec = mp.prec
    z_raw = mp.mpc(0, 0)._mpc_
    A_mp = [[z_raw] * n for _ in range(n)]
    for i in range(n):
        zi = A_iv[i][i]
        re_ii = (mp.make_mpf(zi.real._mpi_[0]) + mp.make_mpf(zi.real._mpi_[1])) / 2
        A_mp[i][i] = mp.mpc(re_ii, 0)._mpc_
        for j in range(i + 1, n):
            z1 = A_iv[i][j]
            z2 = A_iv[j][i]
            re_ij = (
                mp.make_mpf(z1.real._mpi_[0])
                + mp.make_mpf(z1.real._mpi_[1])
                + mp.make_mpf(z2.real._mpi_[0])
                + mp.make_mpf(z2.real._mpi_[1])
            ) / 4
            im_ij = (
                mp.make_mpf(z1.imag._mpi_[0])
                + mp.make_mpf(z1.imag._mpi_[1])
                - mp.make_mpf(z2.imag._mpi_[0])
                - mp.make_mpf(z2.imag._mpi_[1])
            ) / 4
            if re_ij != 0 or im_ij != 0:
                vij = mp.mpc(re_ij, im_ij)._mpc_
                A_mp[i][j] = vij
                A_mp[j][i] = mpc_conjugate(vij, prec)

    def mpc_herm_mul(M1: list[list], M2: list[list]) -> list[list]:
        res = [[z_raw] * n for _ in range(n)]
        for i in range(n):
            r1 = M1[i]
            acc = [z_raw] * n
            for k in range(n):
                ak = r1[k]
                if ak != z_raw:
                    m2k = M2[k]
                    for j in range(i, n):
                        bkj = m2k[j]
                        if bkj != z_raw:
                            acc[j] = mpc_add(acc[j], mpc_mul(ak, bkj, prec), prec)
            res[i][i] = (acc[i][0], mp.mpf(0)._mpf_)
            for j in range(i + 1, n):
                res[i][j] = acc[j]
                res[j][i] = mpc_conjugate(acc[j], prec)
        return res

    A_nz = [[(k, A_mp[i][k]) for k in range(n) if A_mp[i][k] != z_raw] for i in range(n)]

    # Deterministic pure-mpmath commuting seed Y_0 = c I (c = sqrt(2 / 45), ||I - c^2 A||_2 < 0.74 < 1):
    # Cubic Chebyshev-Schulz M_k = (1/8)(15 I - W_k (10 I - 3 W_k)) with W_k = Y_k A Y_k (5 steps -> ~50 digits!).
    c_mp = mp.sqrt(mp.mpf(2) / mp.mpf(45))
    c_raw = mp.mpc(c_mp, 0)._mpc_
    eighth_raw = mp.mpc(mp.mpf(1) / 8, 0)._mpc_
    m3_raw = mp.mpc(-3, 0)._mpc_
    ten_raw = mp.mpc(10, 0)._mpc_
    fifteen_raw = mp.mpc(15, 0)._mpc_

    # Step 0 analytically from Y_0 = c I (sparse W_0 = c^2 A -> <0.05s):
    c2_raw = mpc_mul(c_raw, c_raw, prec)
    W0 = [[mpc_mul(c2_raw, A_mp[i][j], prec) if A_mp[i][j] != z_raw else z_raw for j in range(n)] for i in range(n)]
    T0 = [[mpc_mul(m3_raw, W0[i][j], prec) if W0[i][j] != z_raw else z_raw for j in range(n)] for i in range(n)]
    for i in range(n):
        T0[i][i] = mpc_add(ten_raw, T0[i][i], prec)
    WT0 = mpc_herm_mul(W0, T0)
    Y_raw = [[z_raw] * n for _ in range(n)]
    c_eighth_raw = mpc_mul(c_raw, eighth_raw, prec)
    neg_c_eighth_raw = mpc_mul(mp.mpc(-1, 0)._mpc_, c_eighth_raw, prec)
    for i in range(n):
        for j in range(n):
            val = mpc_mul(neg_c_eighth_raw, WT0[i][j], prec) if WT0[i][j] != z_raw else z_raw
            if i == j:
                val = mpc_add(mpc_mul(c_eighth_raw, fifteen_raw, prec), val, prec)
            Y_raw[i][j] = val

    # Zolotarev-accelerated cubic Chebyshev-Schulz steps (4 steps -> <1e-44):
    for step_idx in range(8):
        AY = [[z_raw] * n for _ in range(n)]
        for i in range(n):
            acc = [z_raw] * n
            for k, aik in A_nz[i]:
                yk = Y_raw[k]
                for j in range(n):
                    acc[j] = mpc_add(acc[j], mpc_mul(aik, yk[j], prec), prec)
            AY[i] = acc
        W = mpc_herm_mul(Y_raw, AY)
        if max(abs(mp.make_mpf(W[r][r][0]) - 1) for r in range(n)) < mp.mpf("1e-44"):
            break
        gain = mp.mpf(15) / 14 if step_idx == 0 else (mp.mpf(25) / 24 if step_idx == 1 else mp.mpf(1))
        neg_g_eighth = mp.mpc(-gain / 8, 0)._mpc_
        fifteen_g_eighth = mp.mpc((15 * gain) / 8, 0)._mpc_
        T = [[mpc_mul(m3_raw, W[i][j], prec) for j in range(n)] for i in range(n)]
        for i in range(n):
            T[i][i] = mpc_add(ten_raw, T[i][i], prec)
        WT = mpc_herm_mul(W, T)
        M_step = [[mpc_mul(neg_g_eighth, WT[i][j], prec) for j in range(n)] for i in range(n)]
        for i in range(n):
            M_step[i][i] = mpc_add(fifteen_g_eighth, M_step[i][i], prec)
        Y_raw = mpc_herm_mul(Y_raw, M_step)

    Y_mp = mp.matrix(n, n)
    for i in range(n):
        Y_mp[i, i] = mp.mpc(mp.make_mpf(Y_raw[i][i][0]), 0)
        for j in range(i + 1, n):
            re_v = mp.make_mpf(Y_raw[i][j][0])
            im_v = mp.make_mpf(Y_raw[i][j][1])
            Y_mp[i, j] = mp.mpc(re_v, im_v)
            Y_mp[j, i] = mp.mpc(re_v, -im_v)

    L_mp = mp.matrix(n, n)
    for i in range(n):
        for j in range(i):
            s = Y_mp[i, j]
            for k in range(j):
                s -= L_mp[i, k] * mp.conj(L_mp[j, k])
            L_mp[i, j] = s / L_mp[j, j]
        diag_s = Y_mp[i, i].real
        for k in range(i):
            z_ik = L_mp[i, k]
            diag_s -= z_ik.real * z_ik.real + z_ik.imag * z_ik.imag
        require(diag_s > 0, f"Hermitian Cholesky pivot non-positive at row {i}: {diag_s}")
        L_mp[i, i] = mp.mpc(mp.sqrt(diag_s), 0)

    L_iv = mp_to_thin_iv_matrix(L_mp)
    Y_enclosed, norm_R, delta_Y = riccati_certify_from_factor(A_iv, L_iv)
    return Y_enclosed, norm_R, delta_Y, L_iv


def iv_thin_midpoint_matrix(M: list[list]) -> list[list]:
    """Exact thin (point) iv matrix at the binary midpoints of an interval matrix."""
    out = []
    for row in M:
        new_row = []
        for z in row:
            re_m = (mp.make_mpf(z.real._mpi_[0]) + mp.make_mpf(z.real._mpi_[1])) / 2
            im_m = (mp.make_mpf(z.imag._mpi_[0]) + mp.make_mpf(z.imag._mpi_[1])) / 2
            new_row.append(iv.mpc(iv.mpf(re_m), iv.mpf(im_m)) if (re_m != 0 or im_m != 0) else iv.mpc(0, 0))
        out.append(new_row)
    return out


def riccati_certify_from_factor(A_iv: list[list], L_iv: list[list]) -> tuple[list[list], object, object]:
    """Rigorous 40-digit enclosure of A^{-1/2} around the exact PSD candidate Y = L L^H (L a thin point matrix).

    For any Hermitian PSD candidate Y with R := I - Y A Y, ||R||_F < 1 implies A > 0, Y > 0 and
    ||Y - A^{-1/2}||_F <= ||A||_F^{1/2} ||Y||_F^2 ||R||_F / (1 - ||R||_F); the bound is independent of how
    the candidate L was obtained, so seeding is irrelevant to rigor.
    """
    n = len(A_iv)
    Y_tilde = iv_matmul_hermitian(L_iv, iv_conj_transpose(L_iv))

    I_n = iv_eye(n)
    R_iv = iv_add(I_n, iv_matmul_hermitian(Y_tilde, iv_matmul(A_iv, Y_tilde)), scale_b=-1)
    norm_R = iv_frobenius_norm(R_iv)
    require(strictly_below(norm_R, "1e-34"), f"SU(2) Riccati residual ||R||_F too large: {norm_R}")

    norm_A = iv_frobenius_norm(A_iv)
    norm_Y = iv_frobenius_norm(Y_tilde)
    delta_Y = iv.sqrt(norm_A) * (norm_Y**2) * norm_R / (iv.mpf(1) - norm_R)
    require(strictly_below(delta_Y, "1e-32"), f"SU(2) inverse-sqrt bound delta_Y too wide: {delta_Y}")

    rad = delta_Y.b
    bloat = iv.mpc(iv.mpf([-rad, rad]), iv.mpf([-rad, rad]))
    Y_enclosed = [[Y_tilde[i][j] + bloat for j in range(n)] for i in range(n)]
    return Y_enclosed, norm_R, delta_Y


def gamma_4d_and_kramers():
    """4D chiral Euclidean gamma matrices and symplectic spinor charge conjugation C_E = gamma_1 gamma_3."""
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
    c_e = iv_matmul(g1, g3)  # C_E = diag(i sigma_2, i sigma_2), satisfies C_E gamma_mu C_E^{-1} = conj(gamma_mu)
    return [g1, g2, g3, g4], g5, c_e


def build_4d_su2_nonabelian_overlap() -> dict:
    """Construct and certify 128x128 4D 2^4 non-Abelian SU(2) Neuberger Overlap operator in 40-digit iv."""
    L = 2
    n_sites = L**4
    dim = 8 * n_sites  # 16 sites * 4 spinor * 2 SU(2) color = 128
    gammas, g5, c_e = gamma_4d_and_kramers()
    I4 = iv_eye(4)
    I2 = iv_eye(2)
    eps2 = [[iv.mpc(0, 0), iv.mpc(1, 0)], [iv.mpc(-1, 0), iv.mpc(0, 0)]]

    def idx4(x1: int, x2: int, x3: int, x4: int) -> int:
        return (((x1 % L) * L + (x2 % L)) * L + (x3 % L)) * L + (x4 % L)

    def coords4(site: int) -> tuple[int, int, int, int]:
        x4 = site % L
        s = site // L
        x3 = s % L
        s //= L
        x2 = s % L
        x1 = s // L
        return x1, x2, x3, x4

    # Site-modulated rational Cayley SU(2) link field U_mu(x) strictly inside Luscher's eps_adm = 1/30 ball:
    U_links: dict[tuple[int, int], list[list]] = {}
    for site in range(n_sites):
        x1, x2, x3, x4 = coords4(site)
        s12 = Fraction(1 if (x2 + x4) % 2 == 0 else -1, 1)
        s23 = Fraction(1 if (x1 + x3) % 2 == 0 else -1, 1)
        U_links[(site, 0)] = cayley_su2_iv(s12 * Fraction(1, 400), Fraction(0, 1), Fraction(1, 1200))
        U_links[(site, 1)] = cayley_su2_iv(Fraction(0, 1), s23 * Fraction(1, 400), Fraction(0, 1))
        U_links[(site, 2)] = cayley_su2_iv(Fraction(1, 1000), Fraction(0, 1), s12 * Fraction(1, 420))
        U_links[(site, 3)] = cayley_su2_iv(Fraction(0, 1), Fraction(1, 900), s23 * Fraction(1, 480))

    # Certify genuine non-Abelian non-commutativity ||[U_1(0), U_2(0)]||_F > 5e-5
    U1_0 = U_links[(0, 0)]
    U2_0 = U_links[(0, 1)]
    comm_12 = iv_add(iv_matmul(U1_0, U2_0), iv_matmul(U2_0, U1_0), scale_b=-1)
    comm_norm = iv_frobenius_norm(comm_12)
    require(strictly_above(comm_norm, "5e-5"), f"SU(2) links failed non-commutativity check: {comm_norm}")

    # Certify strict Luscher admissibility max_{x, mu<nu} ||I_2 - U_{mu,nu}(x)||_F < eps_adm = 1/30
    def shift_site(site: int, mu: int, step: int = 1) -> int:
        c = list(coords4(site))
        c[mu] = (c[mu] + step) % L
        return idx4(c[0], c[1], c[2], c[3])

    max_plaq_dist = iv.mpf(0)
    for site in range(n_sites):
        for mu in range(4):
            for nu in range(mu + 1, 4):
                s_mu = shift_site(site, mu, 1)
                s_nu = shift_site(site, nu, 1)
                u_plaq = iv_matmul(
                    iv_matmul(U_links[(site, mu)], U_links[(s_mu, nu)]),
                    iv_matmul(iv_conj_transpose(U_links[(s_nu, mu)]), iv_conj_transpose(U_links[(site, nu)])),
                )
                dist = iv_frobenius_norm(iv_add(I2, u_plaq, scale_b=-1))
                if dist.b > max_plaq_dist.b:
                    max_plaq_dist = iv.mpf([0, dist.b])
    eps_adm = iv.mpf(1) / 30
    require(strictly_below(max_plaq_dist, eps_adm), f"Plaquette distance exceeded Luscher eps_adm=1/30: {max_plaq_dist}")

    # Assemble 128x128 Wilson-Dirac kernel X(U), G5, and Kramers structure J = I_sites tensor C_E tensor eps_2
    m0 = iv.mpf(3) / 2
    a_lat = iv.mpf(1) / 2
    diag_mass = iv.mpc(iv.mpf(4) - m0, 0)
    X = iv_zeros(dim)
    G5 = iv_zeros(dim)
    J_kramers = iv_zeros(dim)

    for site in range(n_sites):
        b0 = 8 * site
        for s in range(4):
            for c in range(2):
                X[b0 + 2 * s + c][b0 + 2 * s + c] += diag_mass
            for s2 in range(4):
                g5_val = g5[s][s2]
                ce_val = c_e[s][s2]
                if g5_val != iv.mpc(0, 0):
                    for c in range(2):
                        G5[b0 + 2 * s + c][b0 + 2 * s2 + c] = g5_val
                if ce_val != iv.mpc(0, 0):
                    for c1 in range(2):
                        for c2 in range(2):
                            J_kramers[b0 + 2 * s + c1][b0 + 2 * s2 + c2] = ce_val * eps2[c1][c2]

        for mu in range(4):
            nb = shift_site(site, mu, 1)
            j0 = 8 * nb
            gm = gammas[mu]
            u_mat = U_links[(site, mu)]
            u_dag = iv_conj_transpose(u_mat)
            half_neg = iv.mpc(-iv.mpf(1) / 2, 0)
            for s1 in range(4):
                for s2 in range(4):
                    proj_f = half_neg * (I4[s1][s2] - gm[s1][s2])
                    proj_b = half_neg * (I4[s1][s2] + gm[s1][s2])
                    if proj_f != iv.mpc(0, 0):
                        for c1 in range(2):
                            for c2 in range(2):
                                X[b0 + 2 * s1 + c1][j0 + 2 * s2 + c2] += proj_f * u_mat[c1][c2]
                    if proj_b != iv.mpc(0, 0):
                        for c1 in range(2):
                            for c2 in range(2):
                                X[j0 + 2 * s1 + c1][b0 + 2 * s2 + c2] += proj_b * u_dag[c1][c2]

    # Enclose (X^dagger X)^{-1/2} in 40-digit outward interval arithmetic
    XdX = iv_matmul(iv_conj_transpose(X), X)
    Y_iv, norm_R, delta_Y, L_chol_iv = enclose_inv_sqrt_hpd_newton_cholesky(XdX)

    I_dim = iv_eye(dim)
    U_ov = iv_matmul(X, Y_iv)
    D_ov = iv_scale(iv.mpf(1) / a_lat, iv_add(I_dim, U_ov))

    # G5_hat = G5 (I - a D_ov) = -G5 U_ov, projectors P_+, hat_P_-
    G5_hat = iv_matmul(G5, iv_add(I_dim, iv_scale(a_lat, D_ov), scale_b=-1))
    P_plus = iv_scale(iv.mpf(1) / 2, iv_add(I_dim, G5))
    P_hat_minus = iv_scale(iv.mpf(1) / 2, iv_add(I_dim, G5_hat, scale_b=-1))

    # 1. Deformed chirality involution ||hat_gamma_5^2 - I_128||_F
    g5_hat_sq_err = iv_frobenius_norm(iv_add(iv_matmul(G5_hat, G5_hat), I_dim, scale_b=-1))
    require(g5_hat_sq_err.a <= 0 and strictly_below(g5_hat_sq_err, "1e-28"), f"SU(2) hat_gamma_5^2 failed: {g5_hat_sq_err}")

    # 2. Luscher chiral factorization ||P_+ D_ov hat_P_- - D_ov hat_P_-||_F
    D_Phat_m = iv_matmul(D_ov, P_hat_minus)
    luscher_fact_err = iv_frobenius_norm(iv_add(iv_matmul(P_plus, D_Phat_m), D_Phat_m, scale_b=-1))
    require(luscher_fact_err.a <= 0 and strictly_below(luscher_fact_err, "1e-28"), f"SU(2) Luscher factorization failed: {luscher_fact_err}")

    # 3. Symplectic Kramers reality: J^2 = +I_128 and J D_ov J^{-1} = conj(D_ov)
    J_sq_err = iv_frobenius_norm(iv_add(iv_matmul(J_kramers, J_kramers), I_dim, scale_b=-1))
    require(strictly_below(J_sq_err, "1e-38"), f"Kramers J^2 = I_128 failed: {J_sq_err}")
    kramers_reality_err = iv_frobenius_norm(
        iv_add(iv_matmul(J_kramers, iv_matmul(D_ov, J_kramers)), iv_conj_matrix(D_ov), scale_b=-1)
    )
    require(
        kramers_reality_err.a <= 0 and strictly_below(kramers_reality_err, "1e-28"),
        f"SU(2) Kramers reality failed: {kramers_reality_err}",
    )

    # 4. Non-Abelian site-local SU(2) gauge transformation G: verify G D_ov(U) G^dagger = D_ov(U^g) &hat_P_- covariance
    G_gauge = iv_zeros(dim)
    for site in range(n_sites):
        x1, x2, x3, x4 = coords4(site)
        g_loc = cayley_su2_iv(
            Fraction(x1 - x3, 9),
            Fraction(x2 + 1, 11),
            Fraction(x4 - x2, 13),
        )
        b0 = 8 * site
        for s in range(4):
            for c1 in range(2):
                for c2 in range(2):
                    G_gauge[b0 + 2 * s + c1][b0 + 2 * s + c2] = g_loc[c1][c2]
    G_dag = iv_conj_transpose(G_gauge)

    # Build X(U^g) directly from gauge-transformed links U^g_mu(x) = g(x) U_mu(x) g(x+mu)^dagger:
    # By exact algebraic covariance X(U^g) = G X(U) G^dagger, verify ||G X(U) G^dagger - X(U^g)||_F < 1e-36
    # and ||G hat_P_-(U) G^dagger - hat_P_-(G D_ov G^dagger)||_F < 1e-28, plus zero Luscher index drift!
    X_ug = iv_zeros(dim)
    for site in range(n_sites):
        b0 = 8 * site
        for s in range(4):
            for c in range(2):
                X_ug[b0 + 2 * s + c][b0 + 2 * s + c] += diag_mass
        g_x = [[G_gauge[b0 + c1][b0 + c2] for c2 in range(2)] for c1 in range(2)]
        for mu in range(4):
            nb = shift_site(site, mu, 1)
            j0 = 8 * nb
            g_nb = [[G_gauge[j0 + c1][j0 + c2] for c2 in range(2)] for c1 in range(2)]
            gm = gammas[mu]
            u_ug = iv_matmul(g_x, iv_matmul(U_links[(site, mu)], iv_conj_transpose(g_nb)))
            u_ug_dag = iv_conj_transpose(u_ug)
            half_neg = iv.mpc(-iv.mpf(1) / 2, 0)
            for s1 in range(4):
                for s2 in range(4):
                    proj_f = half_neg * (I4[s1][s2] - gm[s1][s2])
                    proj_b = half_neg * (I4[s1][s2] + gm[s1][s2])
                    if proj_f != iv.mpc(0, 0):
                        for c1 in range(2):
                            for c2 in range(2):
                                X_ug[b0 + 2 * s1 + c1][j0 + 2 * s2 + c2] += proj_f * u_ug[c1][c2]
                    if proj_b != iv.mpc(0, 0):
                        for c1 in range(2):
                            for c2 in range(2):
                                X_ug[j0 + 2 * s1 + c1][b0 + 2 * s2 + c2] += proj_b * u_ug_dag[c1][c2]

    gauge_kernel_cov_err = iv_frobenius_norm(
        iv_add(iv_matmul(G_gauge, iv_matmul(X, G_dag)), X_ug, scale_b=-1)
    )
    require(strictly_below(gauge_kernel_cov_err, "1e-36"), f"SU(2) kernel gauge covariance failed: {gauge_kernel_cov_err}")

    # Independently certify an enclosure of (X_ug^dagger X_ug)^{-1/2} against the Wilson kernel X_ug built from the
    # transformed links: exact PSD point candidate Y_ug = L_ug L_ug^H (L_ug = midpoint(G L)), Riccati residual
    # evaluated against X_ug^dagger X_ug only (never against D_ov(U)), then D_ov(U^g) assembled from X_ug.
    XdX_ug = iv_matmul(iv_conj_transpose(X_ug), X_ug)
    L_ug_iv = iv_thin_midpoint_matrix(iv_matmul(G_gauge, L_chol_iv))
    Y_ug_iv, norm_R_ug, delta_Y_ug = riccati_certify_from_factor(XdX_ug, L_ug_iv)
    D_ov_ug = iv_scale(iv.mpf(1) / a_lat, iv_add(I_dim, iv_matmul(X_ug, Y_ug_iv)))

    dov_gauge_cov_err = iv_frobenius_norm(
        iv_add(D_ov_ug, iv_matmul(G_gauge, iv_matmul(D_ov, G_dag)), scale_b=-1)
    )
    require(
        dov_gauge_cov_err.a <= 0 and strictly_below(dov_gauge_cov_err, "1e-28"),
        f"Non-Abelian Overlap operator SU(2) gauge covariance failed: {dov_gauge_cov_err}",
    )

    G5_hat_ug = iv_matmul(G5, iv_add(I_dim, iv_scale(a_lat, D_ov_ug), scale_b=-1))
    P_hat_minus_ug = iv_scale(iv.mpf(1) / 2, iv_add(I_dim, G5_hat_ug, scale_b=-1))
    proj_gauge_cov_err = iv_frobenius_norm(
        iv_add(P_hat_minus_ug, iv_matmul(G_gauge, iv_matmul(P_hat_minus, G_dag)), scale_b=-1)
    )
    require(
        proj_gauge_cov_err.a <= 0 and strictly_below(proj_gauge_cov_err, "1e-28"),
        f"Luscher projector SU(2) covariance failed: {proj_gauge_cov_err}",
    )

    idx_u = (iv.mpc(-a_lat / 2, 0) * iv_trace(iv_matmul(G5, D_ov))).real
    idx_ug = (iv.mpc(-a_lat / 2, 0) * iv_trace(iv_matmul(G5, D_ov_ug))).real
    idx_gauge_drift = abs(idx_ug - idx_u)
    require(strictly_below(idx_gauge_drift, "1e-29"), f"Non-Abelian Luscher index drifted under gauge transform: {idx_gauge_drift}")
    require(strictly_below(abs(idx_u), "1e-29"), f"Admissible trivial-sector SU(2) index non-zero: {idx_u}")

    return {
        "spacetime_lattice": "2x2x2x2_T4_Euclidean_SU2_fundamental",
        "matrix_dimension": dim,
        "nonabelian_link_commutator_fro": outward_str(comm_norm, digits=40),
        "max_plaquette_frobenius_distance": outward_str(max_plaq_dist, digits=40),
        "riccati_inv_sqrt_residual_fro": outward_str(norm_R, digits=40),
        "inv_sqrt_enclosure_radius_fro": outward_str(delta_Y, digits=40),
        "riccati_inv_sqrt_ug_residual_fro": outward_str(norm_R_ug, digits=40),
        "inv_sqrt_ug_enclosure_radius_fro": outward_str(delta_Y_ug, digits=40),
        "modified_chirality_involution_residual_fro": outward_str(g5_hat_sq_err, digits=40),
        "luscher_left_factorization_residual_fro": outward_str(luscher_fact_err, digits=40),
        "kramers_real_structure_D_ov_residual_fro": outward_str(kramers_reality_err, digits=40),
        "su2_kernel_gauge_covariance_residual_fro": outward_str(gauge_kernel_cov_err, digits=40),
        "su2_overlap_operator_gauge_covariance_residual_fro": outward_str(dov_gauge_cov_err, digits=40),
        "luscher_projector_su2_covariance_residual_fro": outward_str(proj_gauge_cov_err, digits=40),
        "luscher_index_gauge_orbit_drift": outward_str(idx_gauge_drift, digits=40),
        "certified_admissible_su2_chiral_index": 0,
    }


def verify_witten_and_dai_freed_invariants() -> dict:
    """Verify Witten pi_4(SU(2)) = Z_2 Pfaffian parity and mod-16 Dai-Freed Omega_5^Spin(BZ_4) invariants."""
    # Q_X = 5(B - L) - 4 Y on (Q_L, u_R^c, d_R^c, L_L, e_R^c) + optional sterile nu_R^c
    sm_15 = [
        ("Q_L", 6, Fraction(1, 3), Fraction(1, 6), 3),   # 3 SU(2)_L doublets
        ("u_R_c", 3, Fraction(-1, 3), Fraction(-2, 3), 0),
        ("d_R_c", 3, Fraction(-1, 3), Fraction(1, 3), 0),
        ("L_L", 2, Fraction(-1, 1), Fraction(-1, 2), 1),  # 1 SU(2)_L doublet
        ("e_R_c", 1, Fraction(1, 1), Fraction(1, 1), 0),
    ]
    nu_R = ("nu_R_c", 1, Fraction(1, 1), Fraction(0, 1), 0)

    def q_x(bml: Fraction, y: Fraction) -> int:
        val = 5 * bml - 4 * y
        require(val.denominator == 1, f"Non-integer Q_X: {val}")
        return int(val.numerator)

    qx_map = {name: q_x(bml, y) for name, _, bml, y, _ in sm_15 + [nu_R]}
    require(all(v % 4 == 1 for v in qx_map.values()), f"Spin-Z4 alignment failed: {qx_map}")

    n_doublets_quark_only = 3
    n_doublets_sm_1gen = sum(nd for _, _, _, _, nd in sm_15)
    n_doublets_sm_3gen = 3 * n_doublets_sm_1gen
    require(1 + (-1) ** n_doublets_quark_only == 0, "Quark-only Witten Z_2 cancellation check failed")
    require(n_doublets_sm_1gen == 4 and (-1) ** n_doublets_sm_1gen == 1, "1-gen Witten invariance failed")
    require(n_doublets_sm_3gen == 12 and (-1) ** n_doublets_sm_3gen == 1, "3-gen Witten invariance failed")

    # 15-Weyl vs 16-Weyl Dai-Freed Omega_5^{Spin^{Z_4}} = Z_16 and U(1)_X traces
    df_15_1gen = sum(mult for _, mult, _, _, _ in sm_15) % 16
    df_15_3gen = (3 * sum(mult for _, mult, _, _, _ in sm_15)) % 16
    tr_qx_15 = sum(mult * qx_map[name] for name, mult, _, _, _ in sm_15)
    tr_qx3_15 = sum(mult * (qx_map[name] ** 3) for name, mult, _, _, _ in sm_15)

    df_16_1gen = (sum(mult for _, mult, _, _, _ in sm_15) + nu_R[1]) % 16
    df_16_3gen = (3 * (sum(mult for _, mult, _, _, _ in sm_15) + nu_R[1])) % 16
    tr_qx_16 = tr_qx_15 + nu_R[1] * qx_map["nu_R_c"]
    tr_qx3_16 = tr_qx3_15 + nu_R[1] * (qx_map["nu_R_c"] ** 3)

    require(df_15_1gen == 15 and df_15_3gen == 13 and tr_qx_15 == -5 and tr_qx3_15 == -125, "15-Weyl Dai-Freed values drifted")
    require(df_16_1gen == 0 and df_16_3gen == 0 and tr_qx_16 == 0 and tr_qx3_16 == 0, "16-Weyl Dai-Freed cancellation failed")

    return {
        "charges_QX_5BminusL_minus_4Y": qx_map,
        "all_states_QX_mod_4_eq_1": True,
        "witten_su2_quark_only_doublets_3_partition_factor": 0,
        "witten_su2_sm_1gen_doublets_4_pfaffian_sign": 1,
        "witten_su2_sm_3gen_doublets_12_pfaffian_sign": 1,
        "dai_freed_Z4_mod16_15weyl_1gen": df_15_1gen,
        "dai_freed_Z4_mod16_15weyl_3gen": df_15_3gen,
        "tr_QX_15weyl_1gen": tr_qx_15,
        "tr_QX_cubed_15weyl_1gen": tr_qx3_15,
        "dai_freed_Z4_mod16_16weyl_1gen": df_16_1gen,
        "dai_freed_Z4_mod16_16weyl_3gen": df_16_3gen,
        "tr_QX_16weyl_1gen": tr_qx_16,
        "tr_QX_cubed_16weyl_1gen": tr_qx3_16,
    }


def verify_asymptotic_freedom_and_clay_boundary() -> dict:
    """Compute 40-digit outward intervals for 1/2-loop AF, plaquette defect suppression, & Clay exponent gap."""
    b0_su3 = Fraction(7, 1)
    b1_su3 = Fraction(26, 1)
    b0_su2 = Fraction(19, 6)
    b1_su2 = Fraction(-35, 6)

    pi_sq_16 = 16 * (iv.pi**2)
    eps_luscher = iv.mpf(1) / 30
    c_adm_luscher = (eps_luscher**2) / pi_sq_16

    exp_su3_luscher = 2 * c_adm_luscher * iv.mpf(7)
    exp_su2_luscher = 2 * c_adm_luscher * (iv.mpf(19) / 6)
    require(strictly_above(exp_su3_luscher, "0") and strictly_below(exp_su3_luscher, "4"), "Clay exponent gap check failed")

    # Effective O(1) physical vortex core defect ||I - U_p||_F = sqrt(8) (center flip U_p = -I_2 -> ||I - (-I_2)||_F^2 = 8)
    dist_sq_z2_vortex = iv.mpf(8)
    c_vortex = dist_sq_z2_vortex / pi_sq_16
    exp_su2_z2_vortex = 2 * c_vortex * (iv.mpf(19) / 6)
    exp_su3_o1_defect = 2 * c_vortex * iv.mpf(7)

    # Evaluate single-plaquette defect Boltzmann weight (a Lambda_MS)^{2 c b_0} at UV scale a Lambda_MS = 10^{-16}
    a_lambda_uv = iv.mpf("1e-16")
    weight_su3_luscher_uv = a_lambda_uv**exp_su3_luscher
    weight_su2_vortex_uv = a_lambda_uv**exp_su2_z2_vortex
    require(strictly_below(weight_su3_luscher_uv, "1") and strictly_below(weight_su2_vortex_uv, "1e-5"), "UV defect suppression failed")

    return {
        "su3c_3gen_b0_exact": str(b0_su3),
        "su3c_3gen_b1_exact": str(b1_su3),
        "su2L_3gen_b0_exact": str(b0_su2),
        "su2L_3gen_b1_exact": str(b1_su2),
        "luscher_eps_1_over_30_c_adm": outward_str(c_adm_luscher, digits=40),
        "su3c_luscher_defect_exponent_2cb0": outward_str(exp_su3_luscher, digits=40),
        "su2L_luscher_defect_exponent_2cb0": outward_str(exp_su2_luscher, digits=40),
        "su2L_center_vortex_exponent_2cb0": outward_str(exp_su2_z2_vortex, digits=40),
        "su3c_large_defect_exponent_2cb0": outward_str(exp_su3_o1_defect, digits=40),
        "uv_aLambda_1e_minus_16_su3_luscher_boltzmann_bound": outward_str(weight_su3_luscher_uv, digits=40),
        "uv_aLambda_1e_minus_16_su2_vortex_boltzmann_bound": outward_str(weight_su2_vortex_uv, digits=40),
        "clay_4d_infinite_volume_chiral_continuum_measure": "OPEN",
    }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    mode = ap.add_mutually_exclusive_group()
    mode.add_argument("--write", "--write-certificate", dest="write", action="store_true", help="Write certificate.json")
    mode.add_argument("--check", action="store_true", help="Verify committed certificate.json without rewriting")
    ap.add_argument("--output", type=Path, default=HERE / "certificate.json")
    args = ap.parse_args()

    su2_overlap_cert = build_4d_su2_nonabelian_overlap()
    topo_anom_cert = verify_witten_and_dai_freed_invariants()
    af_clay_cert = verify_asymptotic_freedom_and_clay_boundary()

    payload = {
        "result_ids": ["P-NONABELIAN-CHIRAL-08"],
        "lean_module": "formalization/ueot-physics-unification/UEOTPhysicsUnification/NonAbelianChiralConstructiveBoundary.lean",
        "nonabelian_su2_4d_overlap_audit": su2_overlap_cert,
        "witten_z2_and_dai_freed_mod16_invariants": topo_anom_cert,
        "asymptotic_freedom_and_clay_continuum_boundary": af_clay_cert,
        "device_certified": False,
        "physical_unification": "OPEN",
        "status": "PASS",
        "source_sha256": sha256_file(Path(__file__).resolve()),
    }
    finish(args, payload, "nonabelian_chiral_constructive")
    print("PASS: nonabelian_chiral_constructive (P-NONABELIAN-CHIRAL-08)")


if __name__ == "__main__":
    main()
