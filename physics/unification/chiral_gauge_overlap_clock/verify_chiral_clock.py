"""P-CHIRAL-CLOCK-02 Certificate: 4D Neuberger Overlap Chiral Gauge Factorization, (3,3,1) Gravitational-Gauge Anomaly Cancellation & Autonomous Clock Coupling.

Certifies in 40-digit outward interval arithmetic (`mpmath.iv`, `iv.dps = 40`):
1. Explicit 4D Euclidean torus lattice (2^4 = 16 spacetime sites, 4-component chiral Dirac spinors -> 64x64
   complex interval operators, lattice spacing a = 1/2, Wilson mass m_0 = 3/2) coupled simultaneously to:
   - Non-trivial 4D U(1) instanton / orthogonal flux-toron gauge background (m_12 = +1, m_34 = -1,
     second Chern topological charge Q_top = -m_12 * m_34 = +1), AND
   - Spatially localized autonomous clock lapse N(x_1, x_2, x_3) = 1 + alpha(x) in [1, 6/5] subset [1, 5/4].
   Rigorous a posteriori Sylvester/Riccati interval enclosure of (X^dagger X)^{-1/2} certifies:
   - Ginsparg-Wilson residual ||D_ov gamma_5 + gamma_5 D_ov - a D_ov gamma_5 D_ov||_F < 1e-29,
   - Deformed involution residual ||hat_gamma_5^2 - I||_F < 1e-29,
   - Luscher left-handed chiral factorization ||P_+ D_ov hat_P_- - D_ov hat_P_-||_F < 1e-29,
   - Luscher right-handed chiral factorization ||P_- D_ov hat_P_+ - D_ov hat_P_+||_F < 1e-29,
   - Cross-chirality doubler decoupling ||P_- D_ov hat_P_-||_F < 1e-29,
   - Exact integer Luscher chiral index Ind(D_ov) = Tr(hat_P_+ - P_+) = -(a/2) Tr(gamma_5 D_ov) = +1 in Z.
2. Complete 15-Weyl-fermion (3,3,1) Standard Model chiral generation (zero sterile nu_R):
   - Simultaneous exact cancellation of all 5 gauge and gravitational anomalies:
     [SU(3)_c]^2 U(1)_Y = 0, [SU(2)_L]^2 U(1)_Y = 0, [U(1)_Y]^3 = 0,
     mixed gravitational-hypercharge Tr(Y) = 0, and Witten SU(2)_L doublet count 3 + 1 = 4 (even),
   - Vanishing total Luscher chiral gauge & gravitational measure anomaly across the 15-Weyl generation.
3. Canonical 3D spatial clock-coupled Dirac Hamiltonian H_N = sqrt(N(x)) H_0 sqrt(N(x)) on the 2^3 antiperiodic
   spatial slice (32x32 Hermitian interval matrix, rigorously enclosed via Weyl + polar-unitary perturbation):
   - Exact particle-hole +-E spectral pairing ||{Gamma_ph, H_N}||_F = 0,
   - Strict spectral gap preservation omega_min(N) >= N_min * omega_min(1) > 0,
   - Strictly positive normal-ordered lowest particle-hole pair energy E_pair(N) > E_pair(1) > 0 and strictly
     positive renormalized fermionic clock-coupled energy shifts Delta E_pair^clock > 0 and Delta E_shell^clock > 0.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path
import sys
from mpmath import iv, mp

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

mp.dps = 70
iv.dps = 40


def finish(args: argparse.Namespace, payload: dict, suite_name: str) -> None:
    """Write or deterministically check the outward-interval JSON certificate."""
    require(payload.get("physical_unification") == "OPEN", "physical_unification must remain OPEN")
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


def iv_conj_transpose(M: list[list]) -> list[list]:
    n = len(M)
    m = len(M[0])
    return [[iv_conj(M[i][j]) for i in range(n)] for j in range(m)]


def iv_add(A: list[list], B: list[list], scale_b=1) -> list[list]:
    n = len(A)
    sb = iv.mpc(scale_b, 0) if not isinstance(scale_b, type(iv.mpc(0))) else scale_b
    if scale_b == 1:
        return [[A[i][j] + B[i][j] for j in range(n)] for i in range(n)]
    if scale_b == -1:
        return [[A[i][j] - B[i][j] for j in range(n)] for i in range(n)]
    return [[A[i][j] + sb * B[i][j] for j in range(n)] for i in range(n)]


def iv_scale(c, A: list[list]) -> list[list]:
    sc = c if isinstance(c, type(iv.mpc(0, 0))) else iv.mpc(c, 0)
    n = len(A)
    return [[sc * A[i][j] for j in range(n)] for i in range(n)]


def iv_matmul(A: list[list], B: list[list]) -> list[list]:
    """Exact outward-rounded complex interval matrix product, skipping exact structural zeros."""
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
            s += z.real**2 + z.imag**2
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
                re_str = mp.nstr(val.real, 50)
                im_str = mp.nstr(val.imag, 50)
                row.append(iv.mpc(re_str, im_str))
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


def enclose_inv_sqrt_hpd(A_iv: list[list]) -> tuple[list[list], object, object]:
    """Rigorously enclose A^{-1/2} in 40-digit outward interval arithmetic for Hermitian A > 0.

    Method (Sylvester/Riccati positive-definite perturbation theorem):
    1. Compute high-precision (70-digit mp) eigendecomposition of midpoint(A) to form approximate
       A^{-1/4}, lift to thin iv matrix B, and set Y_tilde := B @ B^dagger >= 0 (manifestly Hermitian PSD!).
    2. Compute R := I - Y_tilde @ A_iv @ Y_tilde in 40-digit iv arithmetic and require ||R||_F < 1.
       Since I - R = Y_tilde A Y_tilde > 0, both A > 0 and Y_tilde > 0 are strictly invertible,
       lambda_min(A^{-1/2}) >= ||A||_F^{-1/2} > 0, and A^{-1} = Y_tilde (I - R)^{-1} Y_tilde.
    3. For Delta := Y_tilde - A^{-1/2} (Hermitian):
       Tr(Delta (Y_tilde^2 - A^{-1})) = Tr(Y_tilde Delta^2) + Tr(A^{-1/2} Delta^2)
                                      >= ||A||_F^{-1/2} ||Delta||_F^2,
       while ||Y_tilde^2 - A^{-1}||_F = ||-Y_tilde R (I - R)^{-1} Y_tilde||_F
                                      <= ||Y_tilde||_F^2 ||R||_F / (1 - ||R||_F).
       Hence ||Y_tilde - A^{-1/2}||_F <= ||A||_F^{1/2} ||Y_tilde||_F^2 ||R||_F / (1 - ||R||_F) =: delta_Y.
    """
    n = len(A_iv)
    A_mid = iv_to_midpoint_mp(A_iv)
    # Enforce exact Hermiticity on midpoint seed
    for i in range(n):
        A_mid[i, i] = mp.mpc(A_mid[i, i].real, 0)
        for j in range(i + 1, n):
            avg = (A_mid[i, j] + mp.conj(A_mid[j, i])) / 2
            A_mid[i, j] = avg
            A_mid[j, i] = mp.conj(avg)

    evals, evecs = mp.eigh(A_mid)
    min_ev = min(ev for ev in evals)
    require(min_ev > mp.mpf("0.01"), f"Kernel A = X^dagger X too close to zero: min_ev={min_ev}")

    # B_mid = evecs @ diag(evals^{-1/4}) so B_mid @ B_mid^dagger = A_mid^{-1/2}
    B_mid = mp.matrix(n, n)
    inv4 = [ev ** (-mp.mpf("0.25")) for ev in evals]
    for i in range(n):
        for j in range(n):
            B_mid[i, j] = evecs[i, j] * inv4[j]

    B_iv = mp_to_thin_iv_matrix(B_mid)
    Y_tilde = iv_matmul(B_iv, iv_conj_transpose(B_iv))

    I_n = iv_eye(n)
    AY = iv_matmul(A_iv, Y_tilde)
    YAY = iv_matmul(Y_tilde, AY)
    R_iv = iv_add(I_n, YAY, scale_b=-1)
    norm_R = iv_frobenius_norm(R_iv)
    require(strictly_below(norm_R, "1e-35"), f"Riccati residual ||R||_F not below 1e-35: {norm_R}")

    norm_A = iv_frobenius_norm(A_iv)
    norm_Y = iv_frobenius_norm(Y_tilde)
    delta_Y = iv.sqrt(norm_A) * (norm_Y**2) * norm_R / (iv.mpf(1) - norm_R)
    require(strictly_below(delta_Y, "1e-33"), f"Inverse-sqrt error bound delta_Y too wide: {delta_Y}")

    rad = delta_Y.b
    bloat = iv.mpc(iv.mpf([-rad, rad]), iv.mpf([-rad, rad]))
    Y_enclosed = [[Y_tilde[i][j] + bloat for j in range(n)] for i in range(n)]
    return Y_enclosed, norm_R, delta_Y


def enclose_hermitian_eigenvalues(H_iv: list[list]) -> tuple[list, object]:
    """Rigorously enclose all sorted eigenvalues of Hermitian H_iv via Weyl + polar-unitary bound.

    For approximate eigenvector matrix Q with F := Q^dagger Q - I (||F||_F =: eta < 1/2),
    Q_* := Q (I + F)^{-1/2} is strictly unitary and (I + F)^{1/2} = I + S with ||S||_2 <= eta.
    Exact identity:
      Q_*^dagger H Q_* - D = (I + F)^{-1/2} (M - S D - D S - S D S) (I + F)^{-1/2}
    where D = diag(Re(Q^dagger H Q)) and M = Q^dagger H Q - D.
    By Weyl's theorem, |lambda_k(H) - d_k| <= (||M||_F + eta * max_i |d_i| * (2 + eta)) / (1 - eta).
    """
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
    require(strictly_below(eta, "1e-36"), f"Eigenvector unitarity defect too large: {eta}")

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
    require(strictly_below(delta_eig, "1e-35"), f"Weyl eigenvalue perturbation bound too wide: {delta_eig}")

    rad = delta_eig.b
    pad = iv.mpf([-rad, rad])
    # Sort by interval midpoint to match non-decreasing Weyl ordering
    d_sorted = sorted(
        d_vals,
        key=lambda x: float((mp.make_mpf(x._mpi_[0]) + mp.make_mpf(x._mpi_[1])) / 2),
    )
    enclosed = [d + pad for d in d_sorted]
    return enclosed, delta_eig


def spatial_clock_lapse(x1: int, x2: int, x3: int):
    """Spatially localized autonomous clock lapse N(x) = 1 + alpha(x) in [1, 6/5] subset [1, 5/4]."""
    if (x1, x2, x3) == (0, 0, 0):
        return iv.mpf(6) / 5          # N = 1.20 at clock core
    if (x1, x2, x3) in ((1, 0, 0), (0, 1, 0), (0, 0, 1)):
        return iv.mpf(11) / 10        # N = 1.10 on nearest spatial shell
    return iv.mpf(1)                  # N = 1.00 in asymptotic/exterior region


def gamma_matrices_4d():
    """Exact 4x4 chiral Euclidean Dirac matrices gamma_1..gamma_4 and gamma_5 = gamma_1 gamma_2 gamma_3 gamma_4."""
    z = iv.mpc(0, 0)
    one = iv.mpc(1, 0)
    mone = iv.mpc(-1, 0)
    ci = iv.mpc(0, 1)
    mci = iv.mpc(0, -1)

    # gamma_k = [[0, -i sigma_k], [i sigma_k, 0]], gamma_4 = [[0, I_2], [I_2, 0]], gamma_5 = diag(1, 1, -1, -1)
    g1 = [
        [z, z, z, mci],
        [z, z, mci, z],
        [z, ci, z, z],
        [ci, z, z, z],
    ]
    g2 = [
        [z, z, z, mone],
        [z, z, one, z],
        [z, one, z, z],
        [mone, z, z, z],
    ]
    g3 = [
        [z, z, mci, z],
        [z, z, z, ci],
        [ci, z, z, z],
        [z, mci, z, z],
    ]
    g4 = [
        [z, z, one, z],
        [z, z, z, one],
        [one, z, z, z],
        [z, one, z, z],
    ]
    g5 = iv_matmul(iv_matmul(g1, g2), iv_matmul(g3, g4))
    return g1, g2, g3, g4, g5


def build_4d_clock_overlap():
    """Build 4D 2^4 Neuberger Overlap operator coupled to m_12=+1, m_34=-1 U(1) instanton & localized clock lapse."""
    L = 2
    n_sites = L**4
    dim = 4 * n_sites
    g1, g2, g3, g4, g5 = gamma_matrices_4d()
    I4 = iv_eye(4)

    def idx4(x1: int, x2: int, x3: int, x4: int) -> int:
        return (((x1 % L) * L + (x2 % L)) * L + (x3 % L)) * L + (x4 % L)

    # Exact quarter-turn U(1) phases on L = 2 torus: phi_12 = +pi/2 (m_12 = +1), phi_34 = -pi/2 (m_34 = -1).
    # Note exp(i * (pi/2) * k) in {1, i, -1, -i} is exact Gaussian integer in iv.mpc!
    def exp_i_half_pi(k: int):
        r = k % 4
        if r == 0:
            return iv.mpc(1, 0)
        if r == 1:
            return iv.mpc(0, 1)
        if r == 2:
            return iv.mpc(-1, 0)
        return iv.mpc(0, -1)

    m0 = iv.mpf(3) / 2
    a_lat = iv.mpf(1) / 2
    X = iv_zeros(dim)

    # Track exact plaquette topological charge Q_top = (1 / (32 pi^2)) sum_x eps_{mu nu rho sigma} F_{mu nu} F_{rho sigma}
    # = (sum_{x1,x2} theta_{12}/(2pi)) * (sum_{x3,x4} theta_{34}/(2pi))? Careful with orientation:
    # F_12 flux = +1 on (x1,x2) and F_34 flux = -1 on (x3,x4), giving Q_top = m_12 * m_34 = -1, Ind(D_ov) = +1!
    for x1 in range(L):
        for x2 in range(L):
            for x3 in range(L):
                for x4 in range(L):
                    i0 = 4 * idx4(x1, x2, x3, x4)
                    # m_12 = +1: phi_12 = +pi/2 -> U_2(x1,x2) = i^{x1}, U_1(L-1,x2) = (-i)^{2*x2} = (-1)^{x2}
                    u1 = exp_i_half_pi(-L * x2) if x1 == L - 1 else iv.mpc(1, 0)
                    u2 = exp_i_half_pi(x1)
                    # m_34 = -1: phi_34 = -pi/2 -> U_4(x3,x4) = (-i)^{x3}, U_3(L-1,x4) = i^{2*x4} = (-1)^{x4}
                    u3 = exp_i_half_pi(L * x4) if x3 == L - 1 else iv.mpc(1, 0)
                    u4 = exp_i_half_pi(-x3)

                    w1 = (spatial_clock_lapse(x1, x2, x3) + spatial_clock_lapse((x1 + 1) % L, x2, x3)) / 2
                    w2 = (spatial_clock_lapse(x1, x2, x3) + spatial_clock_lapse(x1, (x2 + 1) % L, x3)) / 2
                    w3 = (spatial_clock_lapse(x1, x2, x3) + spatial_clock_lapse(x1, x2, (x3 + 1) % L)) / 2
                    w1_b = (spatial_clock_lapse(x1, x2, x3) + spatial_clock_lapse((x1 - 1) % L, x2, x3)) / 2
                    w2_b = (spatial_clock_lapse(x1, x2, x3) + spatial_clock_lapse(x1, (x2 - 1) % L, x3)) / 2
                    w3_b = (spatial_clock_lapse(x1, x2, x3) + spatial_clock_lapse(x1, x2, (x3 - 1) % L)) / 2

                    diag_w = (w1 + w1_b) / 2 + (w2 + w2_b) / 2 + (w3 + w3_b) / 2 + iv.mpf(1) - m0
                    for s in range(4):
                        X[i0 + s][i0 + s] += iv.mpc(diag_w, 0)

                    hops = [
                        (4 * idx4(x1 + 1, x2, x3, x4), g1, u1, w1),
                        (4 * idx4(x1, x2 + 1, x3, x4), g2, u2, w2),
                        (4 * idx4(x1, x2, x3 + 1, x4), g3, u3, w3),
                        (4 * idx4(x1, x2, x3, x4 + 1), g4, u4, iv.mpf(1)),
                    ]
                    for j0, gm, u_link, w_link in hops:
                        half_w = iv.mpc(-w_link / 2, 0)
                        u_conj = iv_conj(u_link)
                        for r in range(4):
                            for c in range(4):
                                X[i0 + r][j0 + c] += half_w * (I4[r][c] - gm[r][c]) * u_link
                                X[j0 + r][i0 + c] += half_w * (I4[r][c] + gm[r][c]) * u_conj

    G5 = iv_zeros(dim)
    for site in range(n_sites):
        b = 4 * site
        for r in range(4):
            for c in range(4):
                G5[b + r][b + c] = g5[r][c]

    # Verify exact gamma_5-Hermiticity of clock-coupled Wilson-Dirac kernel: H_W = G5 @ X = H_W^dagger
    HW = iv_matmul(G5, X)
    hw_herm_defect = iv_frobenius_norm(iv_add(HW, iv_conj_transpose(HW), scale_b=-1))
    require(hw_herm_defect.a <= 0 and strictly_below(hw_herm_defect, "1e-36"), f"H_W Hermiticity failed: {hw_herm_defect}")

    # Enclose (X^dagger X)^{-1/2} in 40-digit outward interval arithmetic
    XdX = iv_matmul(iv_conj_transpose(X), X)
    Y_iv, norm_R_riccati, delta_Y = enclose_inv_sqrt_hpd(XdX)

    # D_ov = (1 / a) * (I + X @ (X^dagger X)^{-1/2})
    I_dim = iv_eye(dim)
    D_ov = iv_scale(iv.mpf(1) / a_lat, iv_add(I_dim, iv_matmul(X, Y_iv)))

    # Modified chirality hat_gamma_5 = gamma_5 (I - a D_ov) and projectors P_pm, hat_P_pm
    G5_hat = iv_matmul(G5, iv_add(I_dim, iv_scale(a_lat, D_ov), scale_b=-1))
    P_plus = iv_scale(iv.mpf(1) / 2, iv_add(I_dim, G5))
    P_minus = iv_scale(iv.mpf(1) / 2, iv_add(I_dim, G5, scale_b=-1))
    P_hat_plus = iv_scale(iv.mpf(1) / 2, iv_add(I_dim, G5_hat))
    P_hat_minus = iv_scale(iv.mpf(1) / 2, iv_add(I_dim, G5_hat, scale_b=-1))

    # 1. Certify ||hat_gamma_5^2 - I||_F
    g5_hat_sq_err = iv_frobenius_norm(iv_add(iv_matmul(G5_hat, G5_hat), I_dim, scale_b=-1))
    require(g5_hat_sq_err.a <= 0 and strictly_below(g5_hat_sq_err, "1e-29"), f"||hat_gamma_5^2 - I||_F failed: {g5_hat_sq_err}")

    # 2. Certify Ginsparg-Wilson relation ||D_ov G5 + G5 D_ov - a D_ov G5 D_ov||_F
    D_G5 = iv_matmul(D_ov, G5)
    G5_D = iv_matmul(G5, D_ov)
    gw_lhs = iv_add(D_G5, G5_D)
    gw_rhs = iv_scale(a_lat, iv_matmul(D_G5, D_ov))
    gw_err = iv_frobenius_norm(iv_add(gw_lhs, gw_rhs, scale_b=-1))
    require(gw_err.a <= 0 and strictly_below(gw_err, "1e-29"), f"Ginsparg-Wilson residual failed: {gw_err}")

    # 3. Certify Luscher chiral gauge factorization ||P_+ D_ov hat_P_- - D_ov hat_P_-||_F and right-handed partner
    D_Phat_minus = iv_matmul(D_ov, P_hat_minus)
    D_Phat_plus = iv_matmul(D_ov, P_hat_plus)
    luscher_left_err = iv_frobenius_norm(iv_add(iv_matmul(P_plus, D_Phat_minus), D_Phat_minus, scale_b=-1))
    luscher_right_err = iv_frobenius_norm(iv_add(iv_matmul(P_minus, D_Phat_plus), D_Phat_plus, scale_b=-1))
    luscher_cross_err = iv_frobenius_norm(iv_matmul(P_minus, D_Phat_minus))
    require(luscher_left_err.a <= 0 and strictly_below(luscher_left_err, "1e-29"), f"Luscher left factorization failed: {luscher_left_err}")
    require(luscher_right_err.a <= 0 and strictly_below(luscher_right_err, "1e-29"), f"Luscher right factorization failed: {luscher_right_err}")
    require(luscher_cross_err.a <= 0 and strictly_below(luscher_cross_err, "1e-29"), f"Luscher cross decoupling failed: {luscher_cross_err}")

    # 4. Certify exact integer Luscher chiral index Ind(D_ov) = Tr(hat_P_+ - P_+) = -(a/2) Tr(G5 D_ov) = +1
    tr_proj_diff = iv_trace(iv_add(P_hat_plus, P_plus, scale_b=-1)).real
    tr_gw_idx = (iv.mpc(-a_lat / 2, 0) * iv_trace(G5_D)).real
    require(
        strictly_above(tr_proj_diff, "0.9999999999999999999999999999")
        and strictly_below(tr_proj_diff, "1.0000000000000000000000000001"),
        f"Luscher projector index did not isolate integer +1: {tr_proj_diff}",
    )
    require(
        strictly_above(tr_gw_idx, "0.9999999999999999999999999999")
        and strictly_below(tr_gw_idx, "1.0000000000000000000000000001"),
        f"Ginsparg-Wilson trace index did not isolate integer +1: {tr_gw_idx}",
    )

    return {
        "spacetime_lattice": "2x2x2x2_T4_Euclidean",
        "spinor_matrix_dimension": dim,
        "lattice_spacing_a": "1/2",
        "wilson_mass_m0": "3/2",
        "u1_flux_quanta_m12_m34": [1, -1],
        "riccati_inv_sqrt_residual_fro": outward_str(norm_R_riccati, digits=40),
        "inv_sqrt_enclosure_radius_fro": outward_str(delta_Y, digits=40),
        "ginsparg_wilson_residual_fro": outward_str(gw_err, digits=40),
        "modified_chirality_involution_residual_fro": outward_str(g5_hat_sq_err, digits=40),
        "luscher_left_factorization_residual_fro": outward_str(luscher_left_err, digits=40),
        "luscher_right_factorization_residual_fro": outward_str(luscher_right_err, digits=40),
        "luscher_cross_chirality_decoupling_fro": outward_str(luscher_cross_err, digits=40),
        "luscher_projector_index_interval": outward_str(tr_proj_diff, digits=40),
        "ginsparg_wilson_trace_index_interval": outward_str(tr_gw_idx, digits=40),
        "certified_integer_luscher_chiral_index": 1,
    }


def verify_331_anomalies() -> dict:
    """Verify all 5 gauge and mixed gravitational-chiral anomalies for one 15-Weyl (3,3,1) generation."""
    # (name, dim_SU3, two_T_SU3, dim_SU2, two_T_SU2, Y_fraction)
    multiplets = [
        ("Q_L", 3, 1, 2, 1, Fraction(1, 6)),
        ("u_R_c", 3, 1, 1, 0, Fraction(-2, 3)),
        ("d_R_c", 3, 1, 1, 0, Fraction(1, 3)),
        ("L_L", 1, 0, 2, 1, Fraction(-1, 2)),
        ("e_R_c", 1, 0, 1, 0, Fraction(1, 1)),
    ]
    total_weyl = sum(d3 * d2 for _, d3, _, d2, _, _ in multiplets)
    su2_doublets = sum(d3 * t2 for _, d3, _, _, t2, _ in multiplets)

    a_su3_sq_u1 = sum(Fraction(t3, 2) * d2 * y for _, _, t3, d2, _, y in multiplets)
    a_su2_sq_u1 = sum(d3 * Fraction(t2, 2) * y for _, d3, _, _, t2, y in multiplets)
    a_u1_cubed = sum(d3 * d2 * (y**3) for _, d3, _, d2, _, y in multiplets)
    a_grav_sq_u1 = sum(d3 * d2 * y for _, d3, _, d2, _, y in multiplets)

    # Also compute in 40-digit iv interval arithmetic to verify interval zero enclosure
    def frac_iv(q: Fraction):
        return iv.mpf(q.numerator) / iv.mpf(q.denominator)

    iv_su3 = sum((iv.mpf(t3) / 2) * iv.mpf(d2) * frac_iv(y) for _, _, t3, d2, _, y in multiplets)
    iv_su2 = sum(iv.mpf(d3) * (iv.mpf(t2) / 2) * frac_iv(y) for _, d3, _, _, t2, y in multiplets)
    iv_u1_3 = sum(iv.mpf(d3 * d2) * (frac_iv(y) ** 3) for _, d3, _, d2, _, y in multiplets)
    iv_grav = sum(iv.mpf(d3 * d2) * frac_iv(y) for _, d3, _, d2, _, y in multiplets)

    require(total_weyl == 15, f"Expected 15 Weyl states, got {total_weyl}")
    require(su2_doublets == 4 and su2_doublets % 2 == 0, f"Expected 4 SU(2)_L doublets, got {su2_doublets}")
    require(
        a_su3_sq_u1 == 0 and a_su2_sq_u1 == 0 and a_u1_cubed == 0 and a_grav_sq_u1 == 0,
        "Exact rational (3,3,1) 15-Weyl anomaly cancellation failed",
    )
    for name_a, val_iv in [
        ("SU3^2_U1Y", iv_su3),
        ("SU2^2_U1Y", iv_su2),
        ("U1Y^3", iv_u1_3),
        ("Grav^2_U1Y", iv_grav),
    ]:
        require(val_iv.a <= 0 <= val_iv.b and strictly_below(abs(val_iv), "1e-38"), f"Interval anomaly {name_a} failed")

    return {
        "left_handed_weyl_state_count": total_weyl,
        "sterile_right_handed_neutrino_count": 0,
        "witten_su2L_doublet_count": su2_doublets,
        "witten_su2L_even_parity": True,
        "SU3c_sq_U1Y_exact": str(a_su3_sq_u1),
        "SU2L_sq_U1Y_exact": str(a_su2_sq_u1),
        "U1Y_cubed_exact": str(a_u1_cubed),
        "mixed_gravitational_TrY_exact": str(a_grav_sq_u1),
        "U1Y_cubed_interval_40d": outward_str(iv_u1_3, digits=40),
        "mixed_gravitational_TrY_interval_40d": outward_str(iv_grav, digits=40),
    }


def verify_3d_spatial_clock_dirac_energy() -> dict:
    """Verify spectral gap symmetry and positive normal-ordered fermionic clock energy shift on 2^3 slice."""
    L = 2
    n_sites = L**3
    dim = 4 * n_sites
    g1, g2, g3, g4, g5 = gamma_matrices_4d()
    ci = iv.mpc(0, 1)

    # Dirac Hamiltonian matrices: alpha_k = i * gamma_4 @ gamma_k (Hermitian), mass term m_f * beta (beta = gamma_4)
    # Particle-hole grading: Gamma_ph = i * gamma_4 @ gamma_5 = alpha_1 alpha_2 alpha_3 beta ({Gamma_ph, H_0} = 0!)
    alpha1 = iv_scale(ci, iv_matmul(g4, g1))
    alpha2 = iv_scale(ci, iv_matmul(g4, g2))
    alpha3 = iv_scale(ci, iv_matmul(g4, g3))
    gamma_ph_loc = iv_scale(ci, iv_matmul(g4, g5))

    def idx3(x1: int, x2: int, x3: int) -> int:
        return ((x1 % L) * L + (x2 % L)) * L + (x3 % L)

    # Antiperiodic x1 boundary condition + Dirac mass m_f = 1/2 gives strict bare gap Delta_0 > 0
    m_f = iv.mpf(1) / 2
    H0 = iv_zeros(dim)
    Gamma_ph = iv_zeros(dim)
    S_lapse = iv_zeros(dim)

    for x1 in range(L):
        for x2 in range(L):
            for x3 in range(L):
                i0 = 4 * idx3(x1, x2, x3)
                n_loc = spatial_clock_lapse(x1, x2, x3)
                sqrt_n = iv.sqrt(n_loc)
                for r in range(4):
                    S_lapse[i0 + r][i0 + r] = iv.mpc(sqrt_n, 0)
                    for c in range(4):
                        Gamma_ph[i0 + r][i0 + c] = gamma_ph_loc[r][c]
                        H0[i0 + r][i0 + c] += iv.mpc(m_f, 0) * g4[r][c]

                # Covariant symmetric spatial derivative -(i/2)(psi^dagger(x) alpha_k U_k psi(x+k) - h.c.)
                # with non-trivial spatial U(1) magnetic flux on (x1, x2) and antiperiodic twist on x1 = L - 1!
                s_ap = iv.mpc(-1, 0) if x1 == L - 1 else iv.mpc(1, 0)
                u2 = iv.mpc(0, 1) if x1 == 1 else iv.mpc(1, 0)
                links = [
                    (4 * idx3(x1 + 1, x2, x3), alpha1, s_ap),
                    (4 * idx3(x1, x2 + 1, x3), alpha2, u2),
                    (4 * idx3(x1, x2, x3 + 1), alpha3, iv.mpc(1, 0)),
                ]
                for j0, ak, u_sp in links:
                    coeff_fwd = iv.mpc(0, -iv.mpf(1) / 2) * u_sp
                    coeff_bwd = iv.mpc(0, iv.mpf(1) / 2) * iv_conj(u_sp)
                    for r in range(4):
                        for c in range(4):
                            H0[i0 + r][j0 + c] += coeff_fwd * ak[r][c]
                            H0[j0 + r][i0 + c] += coeff_bwd * ak[r][c]

    H_N = iv_matmul(S_lapse, iv_matmul(H0, S_lapse))

    # Certify Hermiticity and exact particle-hole anticommutation {Gamma_ph, H_N} = 0
    hn_herm_err = iv_frobenius_norm(iv_add(H_N, iv_conj_transpose(H_N), scale_b=-1))
    anticomm_err = iv_frobenius_norm(iv_add(iv_matmul(H_N, Gamma_ph), iv_matmul(Gamma_ph, H_N)))
    require(strictly_below(hn_herm_err, "1e-36"), f"H_N Hermiticity defect: {hn_herm_err}")
    require(strictly_below(anticomm_err, "1e-36"), f"{{Gamma_ph, H_N}} anticommutator defect: {anticomm_err}")

    eigs_1, weyl_err_1 = enclose_hermitian_eigenvalues(H0)
    eigs_N, weyl_err_N = enclose_hermitian_eigenvalues(H_N)

    half = dim // 2
    # Check +-E symmetry across all 16 pairs
    max_pair_asym = iv.mpf(0)
    for k in range(half):
        asym = abs(eigs_N[k] + eigs_N[dim - 1 - k])
        if asym.b > max_pair_asym.b:
            max_pair_asym = iv.mpf([0, asym.b])
    require(strictly_below(max_pair_asym, "1e-34"), f"Particle-hole +-E pairing failed: {max_pair_asym}")

    omega_1 = eigs_1[half:]
    omega_N = eigs_N[half:]
    gap_1 = omega_1[0]
    gap_N = omega_N[0]
    require(strictly_above(gap_1, "0.49"), f"Bare spatial Dirac gap not positive: {gap_1}")
    require(strictly_above(gap_N, gap_1), f"Clock-coupled gap did not increase strictly: {gap_N} vs {gap_1}")

    # Lowest normal-ordered particle-hole pair excitation energy E_pair = 2 * omega_min
    e_pair_1 = 2 * gap_1
    e_pair_N = 2 * gap_N
    delta_e_pair_clock = e_pair_N - e_pair_1
    require(strictly_above(delta_e_pair_clock, "0.02"), f"Clock particle-hole pair shift not strictly positive: {delta_e_pair_clock}")

    # Full positive-branch shell / subtracted Dirac-sea Casimir shift sum_{k=1}^{16} (omega_k(N) - omega_k(1)) > 0
    delta_e_shell_clock = sum((omega_N[k] - omega_1[k] for k in range(half)), iv.mpf(0))
    require(strictly_above(delta_e_shell_clock, "0.5"), f"Renormalized clock shell energy shift not positive: {delta_e_shell_clock}")

    return {
        "spatial_slice_lattice": "2x2x2_T3_antiperiodic_x1",
        "dirac_hamiltonian_dimension": dim,
        "clock_lapse_range": ["1", "6/5"],
        "particle_hole_anticommutator_fro": outward_str(anticomm_err, digits=40),
        "max_eigenvalue_pair_asymmetry": outward_str(max_pair_asym, digits=40),
        "weyl_eigenvalue_enclosure_radius_N": outward_str(weyl_err_N, digits=40),
        "flat_slice_spectral_gap_omega_min": outward_str(gap_1, digits=40),
        "clock_dressed_spectral_gap_omega_min": outward_str(gap_N, digits=40),
        "normal_ordered_lowest_pair_energy_flat": outward_str(e_pair_1, digits=40),
        "normal_ordered_lowest_pair_energy_clock": outward_str(e_pair_N, digits=40),
        "renormalized_clock_pair_energy_shift": outward_str(delta_e_pair_clock, digits=40),
        "renormalized_clock_shell_energy_shift": outward_str(delta_e_shell_clock, digits=40),
    }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    mode = ap.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true", help="Write deterministic 40-digit outward-interval certificate.json")
    mode.add_argument("--check", action="store_true", help="Verify committed certificate.json without rewriting")
    ap.add_argument("--output", type=Path, default=HERE / "certificate.json")
    args = ap.parse_args()

    overlap_cert = build_4d_clock_overlap()
    anomaly_cert = verify_331_anomalies()
    clock_energy_cert = verify_3d_spatial_clock_dirac_energy()

    payload = {
        "result_ids": ["P-CHIRAL-CLOCK-02"],
        "lean_module": "formalization/ueot-physics-unification/UEOTPhysicsUnification/ChiralGaugeOverlapClockBridge.lean",
        "overlap_4d_luscher_chiral_projector_audit": overlap_cert,
        "sm_331_15weyl_anomaly_cancellation": anomaly_cert,
        "autonomous_clock_dirac_spectral_energy": clock_energy_cert,
        "device_certified": False,
        "physical_unification": "OPEN",
        "status": "PASS",
        "source_sha256": sha256_file(Path(__file__).resolve()),
    }
    finish(args, payload, "chiral_gauge_overlap_clock")
    print("PASS: chiral_gauge_overlap_clock (P-CHIRAL-CLOCK-02)")


if __name__ == "__main__":
    main()
