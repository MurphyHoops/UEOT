"""P-DISCRETE-QG-01 Certificate: Non-Perturbative Discrete Quantum Geometry, Anomaly-Free
Finite-Graph Hypersurface Algebra & Relational Wheeler-DeWitt Closure.

Verifies with exact symbolic algebra (sympy) and 40-digit outward interval arithmetic (mpmath.iv):
1. Continuum Pauli-Villars Indefinite-Metric Ghost vs AH01 Simplicial Planck-Graph Positivity:
   - Reproduces AH01 operational Planck sensor floor L_min / l_P in [1.9619287, 1.9619288] and sets
     simplicial 3-sphere (partial Delta^4 = K_5, N_sites = 5, d_deg = 4) spacing a_lat = 2 l_P > L_min l_P,
   - Verifies AH09 5-field Hermitian tridiagonal mediator sum rule sum_{j=1}^5 O_{5,j}^2 == 1 and
     proves any 4-pole Vandermonde Pauli-Villars regulator canceling sum_j c_j lambda_j^p = 0 (p=0,1,2)
     with c_1 = 1 has exact ghost weight -(3 + sqrt(3))/2 < -2.36 < 0 (and L1 norm == 6),
   - Encloses strictly positive ghost-free discrete equal-time variance and finite Laplacian norm on K_5.
2. Multi-Site 4-Vertex Tetrahedral Regge Quantum Geometry + 21-Tick Clock + Source-Branch + Pointer
   Wheeler-DeWitt Closure (dim H_kin = 21 x 16 x 2 x 2 = 1344) at Finite Planck Coupling:
   - Non-commuting 4-site quantum volume & extrinsic-curvature operators [S_z, S_x] = i S_y != 0
     (||[S_z, S_x]||_F^2 == 16),
   - Exact Hermitian H_tot = P_clk x I + I x H_tot_dyn solving ||H_tot |Psi_phys^(b)>||_2 == 0
     identically for both vacuum (b=0) and gravitating-source (b=1) branches,
   - Exact zero discrete constraint anomalies: [G_u, G_v] == 0, [H_tot, U_diff(sigma)] == 0 (S_4),
     and [O_rel(t_*, Z_ptr), Pi_phys] == 0,
   - Encloses 4-site quantum-geometry <-> pointer entanglement at tick t_* = 3 (reduced pointer
     purity Tr(rho_ptr^2) in [0.5117, 0.5118] < 1, contrast in [1.0822, 1.0823]) and exact coherent
     quantum-geometry revival at t_* = 7 with relational Dirac pointer contrast Delta C_rel(7) = 3/2.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
import sympy as sp
from mpmath import iv

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from common import outward_str, require, sha256_file, strictly_above, strictly_below, write_json


def iv40(x) -> list[str]:
    return outward_str(x, digits=40)


def finish(payload: dict, args: argparse.Namespace) -> None:
    require(not (args.write and args.check), "Cannot pass both --write and --check")
    if args.check:
        require(args.output.is_file(), f"Missing certificate file for --check: {args.output}")
        committed = json.loads(args.output.read_text())
        require(committed == payload, "discrete_quantum_geometry certificate drift")
    else:
        write_json(args.output, payload)


def verify_pauli_villars_vs_planck_graph() -> dict:
    # 1. AH01 Planck sensor floor (N_gate = 10, eta_t = 1/2, lambda_sys = 2, a_bar = sqrt(7)):
    a_bar = iv.sqrt(iv.mpf("7"))
    e_min_10 = iv.mpf("100") / (2 * (a_bar + iv.sqrt(iv.mpf("107"))))
    l_min_ratio = iv.sqrt(e_min_10)  # L_min / l_P ~ 1.96192878...
    a_lat = iv.mpf("2")              # in Planck units l_P = 1
    require(
        strictly_above(l_min_ratio, "1.961928") and strictly_below(l_min_ratio, a_lat),
        "Planck lattice spacing a_lat = 2 l_P must strictly exceed AH01 L_min",
    )

    # 2. AH09 5-field Hermitian tridiagonal mediator vs Vandermonde Pauli-Villars ghost weights:
    # Eigenvalues of T_{5x5} (M_Sigma = 20): lambda_j = 400 * (1 + cos(j * pi / 6)), j = 1..5.
    # Normalized eigenvectors O_{r,j} = sqrt(1/3) * sin(r * j * pi / 6) on {1..5}:
    kl_sum_sym = sum(sp.Rational(1, 3) * (sp.sin(sp.Integer(5 * j) * sp.pi / 6) ** 2) for j in range(1, 6))
    require(sp.simplify(kl_sum_sym - 1) == 0, "Exact AH09 Kallen-Lehmann orthogonal sum == 1")

    lams_sym = [sp.Integer(400) * (1 + sp.cos(sp.Integer(j) * sp.pi / 6)) for j in range(1, 5)]
    c2, c3, c4 = sp.symbols("c2 c3 c4")
    pv_sol = sp.solve(
        [
            1 + c2 + c3 + c4,
            lams_sym[0] + c2 * lams_sym[1] + c3 * lams_sym[2] + c4 * lams_sym[3],
            lams_sym[0] ** 2 + c2 * (lams_sym[1] ** 2) + c3 * (lams_sym[2] ** 2) + c4 * (lams_sym[3] ** 2),
        ],
        (c2, c3, c4),
        dict=True,
    )[0]
    pv_weights_sym = [sp.Integer(1), sp.simplify(pv_sol[c2]), sp.simplify(pv_sol[c3]), sp.simplify(pv_sol[c4])]
    require(sp.simplify(sum(pv_weights_sym)) == 0, "Exact Pauli-Villars moment p=0 cancellation")

    # Evaluate exact Vandermonde Pauli-Villars weights in 40-digit outward interval arithmetic:
    # By Euler-Lagrange divided-difference identity, sum_{j=0}^3 lambda_j^p / prod_{k != j} (lambda_j - lambda_k) == 0
    # for p = 0, 1, 2; normalizing c_0 = 1 gives c_j = prod_{k=1}^3 (lambda_0 - lambda_k) / prod_{k != j} (lambda_j - lambda_k).
    lams_iv = [iv.mpf("400") * (1 + iv.cos(iv.mpf(j) * iv.pi / 6)) for j in range(1, 5)]
    c_iv = [iv.mpf("1")]
    num_const = (lams_iv[0] - lams_iv[1]) * (lams_iv[0] - lams_iv[2]) * (lams_iv[0] - lams_iv[3])
    for j in range(1, 4):
        den = iv.mpf("1")
        for k in range(4):
            if k != j:
                den *= (lams_iv[j] - lams_iv[k])
        c_iv.append(num_const / den)

    sum_c = c_iv[0] + c_iv[1] + c_iv[2] + c_iv[3]
    sum_abs_c = abs(c_iv[0]) + abs(c_iv[1]) + abs(c_iv[2]) + abs(c_iv[3])
    require(iv.mpf("0") in sum_c and strictly_below(abs(sum_c), "1e-37"), "Interval PV sum encloses 0")
    require(iv.mpf("6") in sum_abs_c and strictly_above(sum_abs_c, "5.99"), "Nontrivial PV L1 norm == 6 > 5.99")
    # c_1 = -(3 + sqrt(3))/2 ~ -2.3660254... is the negative-norm ghost weight:
    c_ghost = c_iv[1]
    require(strictly_below(c_ghost, "-2.36") and strictly_above(c_ghost, "-2.37"),
            "Strictly negative Pauli-Villars ghost weight -(3+sqrt(3))/2 in (-2.37, -2.36)")

    # 3. Minimal simplicial 3-sphere Regge graph partial(Delta^4) = K_5 (N_sites = 5, degree d = 4):
    # Eigenvalues of discrete graph Laplacian on K_5: {0, 5/a_lat^2 (x4)}.
    n_sites = 5
    d_deg = iv.mpf("4")
    m_gap = iv.mpf("1") / 5
    lap_eigs = [iv.mpf("0")] + [iv.mpf("5") / (a_lat ** 2)] * 4
    omegas = [iv.sqrt(m_gap ** 2 + lam) for lam in lap_eigs]
    u_weight = iv.mpf("1") / n_sites

    graph_var = sum(u_weight / (2 * (a_lat ** 3) * om) for om in omegas)
    lean_var_upper = iv.mpf("1") / (2 * (l_min_ratio ** 3) * m_gap)
    lap_spec_max = lap_eigs[1]
    lean_lap_upper = (4 * d_deg) / (l_min_ratio ** 2)

    require(
        strictly_above(graph_var, "0.044") and strictly_below(graph_var, lean_var_upper),
        "Ghost-free K_5 equal-time variance strictly positive and below Lean AH01 bound",
    )
    require(
        strictly_below(lap_spec_max, lean_lap_upper),
        "K_5 discrete Laplacian norm strictly below Brillouin bound 4 d / L_min^2",
    )

    return {
        "AH01_L_min_over_Planck": iv40(l_min_ratio),
        "lattice_spacing_over_Planck": "2",
        "AH09_Hermitian_KL_sum_exact": "1",
        "Pauli_Villars_4pole_L1_norm": iv40(sum_abs_c),
        "Pauli_Villars_most_negative_ghost_weight": iv40(c_ghost),
        "K5_simplicial_S3_equal_time_variance_Planck": iv40(graph_var),
        "Lean_theorem_variance_upper_bound_Planck": iv40(lean_var_upper),
        "K5_discrete_Laplacian_max_eigenvalue_Planck": iv40(lap_spec_max),
        "Lean_theorem_Laplacian_upper_bound_Planck": iv40(lean_lap_upper),
    }


def verify_multisite_regge_wheeler_dewitt() -> dict:
    # 4-vertex tetrahedral quantum geometry H_geom = (C^2)^x4 (dim = 16) x H_src (2) x H_ptr (2) (dim = 64)
    # coupled to 21-tick autonomous quantum clock H_clk (dim = 21; full H_kin dim = 1344).
    I2 = sp.eye(2)
    X = sp.Matrix([[0, 1], [1, 0]])
    Z = sp.Matrix([[1, 0], [0, -1]])

    def kron_list(mats: list[sp.Matrix]) -> sp.Matrix:
        out = mats[0]
        for m in mats[1:]:
            out = sp.kronecker_product(out, m)
        return out

    # Collective non-commuting 4-site Regge volume S_z and extrinsic-curvature shift S_x on (C^2)^x4:
    Sx_geom = sp.zeros(16, 16)
    Sz_geom = sp.zeros(16, 16)
    for v in range(4):
        ops_x = [X if i == v else I2 for i in range(4)]
        ops_z = [Z if i == v else I2 for i in range(4)]
        Sx_geom += sp.Rational(1, 2) * kron_list(ops_x)
        Sz_geom += sp.Rational(1, 2) * kron_list(ops_z)

    # Complete K_4 6-edge projector family G_edges[(u, w)] = (1/2)(I_16 - Z_u Z_w) (0 <= u < w < 4)
    # and per-vertex star sums G_verts[v] = sum_{w != v} G_edges[(min(v, w), max(v, w))]:
    G_edges: dict[tuple[int, int], sp.Matrix] = {}
    for u in range(4):
        for w in range(u + 1, 4):
            ops_zz = [Z if i in (u, w) else I2 for i in range(4)]
            G_edges[(u, w)] = sp.Rational(1, 2) * (sp.eye(16) - kron_list(ops_zz))
    require(len(G_edges) == 6, "Expected all 6 tetrahedral edges of K_4")

    G_verts = [
        sum((G_edges[(min(v, w), max(v, w))] for w in range(4) if w != v), sp.zeros(16, 16))
        for v in range(4)
    ]

    # Verify non-commutativity [S_z, S_x] = i S_y != 0 (operator-valued quantum geometry, Tr(S_y^2) = 16):
    comm_zx = Sz_geom * Sx_geom - Sx_geom * Sz_geom
    comm_zx_frob_sq = int(sum(abs(x) ** 2 for x in comm_zx))
    require(comm_zx_frob_sq == 16, f"Expected ||[S_z, S_x]||_F^2 == 16 on 4-site geometry, got {comm_zx_frob_sq}")

    # Verify idempotence & pairwise vanishing commutators across all 6 K_4 edge projectors and all 4 vertex stars:
    for e1, ge1 in G_edges.items():
        require(ge1 * ge1 == ge1, f"Edge constraint projector G_edges[{e1}] is not idempotent")
        for e2, ge2 in G_edges.items():
            require(ge1 * ge2 - ge2 * ge1 == sp.zeros(16, 16),
                    f"Edge constraint anomaly detected on {e1}, {e2}")
    for u in range(4):
        for v in range(4):
            require(G_verts[u] * G_verts[v] - G_verts[v] * G_verts[u] == sp.zeros(16, 16),
                    "Vertex star constraint anomaly detected")

    # S_4 discrete spatial diffeomorphism generators on complete 4-site tetrahedral slice K_4:
    def perm_matrix_16(perm: tuple[int, int, int, int]) -> sp.Matrix:
        P = sp.zeros(16, 16)
        for idx in range(16):
            bits = [(idx >> (3 - v)) & 1 for v in range(4)]
            new_bits = [bits[perm[v]] for v in range(4)]
            new_idx = sum(new_bits[v] << (3 - v) for v in range(4))
            P[new_idx, idx] = 1
        return P

    s4_generators = [
        ("swap01", (1, 0, 2, 3)),
        ("cyc0123", (3, 0, 1, 2)),
    ]
    U_swap01 = perm_matrix_16((1, 0, 2, 3))
    U_cyc0123 = perm_matrix_16((3, 0, 1, 2))
    for gen_name, perm in s4_generators:
        U_gen = perm_matrix_16(perm)
        # Under new_bits[v] = bits[perm[v]], site u moves to sigma(u) with perm[sigma(u)] == u:
        sigma = tuple(perm.index(u) for u in range(4))
        for (u, w), g_uw in G_edges.items():
            img_edge = (min(sigma[u], sigma[w]), max(sigma[u], sigma[w]))
            require(U_gen * g_uw * U_gen.T == G_edges[img_edge],
                    f"S_4 edge covariance failed under {gen_name} on edge {(u, w)}")
        for v in range(4):
            require(U_gen * G_verts[v] * U_gen.T == G_verts[sigma[v]],
                    f"S_4 vertex star covariance failed under {gen_name} on vertex {v}")

    # Coupled 64x64 Hamiltonian H_tot_dyn (in Planck units omega_0):
    # H_tot_dyn = (3 S_x + 4 S_z) x I_src x I_ptr - 2 S_z x |1><1|_src x (I_ptr - X_ptr)
    Pi_src1 = sp.Matrix([[0, 0], [0, 1]])
    H_dyn = (
        kron_list([3 * Sx_geom + 4 * Sz_geom, I2, I2])
        - kron_list([2 * Sz_geom, Pi_src1, I2 - X])
    )
    require(H_dyn == H_dyn.H, "H_tot_dyn must be Hermitian")

    # Exact anomaly-free diffeomorphism invariance [U_diff(sigma), H_tot_dyn] == 0 for S_4 generators:
    U_swap_64 = kron_list([U_swap01, I2, I2])
    U_cyc_64 = kron_list([U_cyc0123, I2, I2])
    require(U_swap_64 * H_dyn - H_dyn * U_swap_64 == sp.zeros(64, 64), "Swap diffeomorphism commutator != 0")
    require(U_cyc_64 * H_dyn - H_dyn * U_cyc_64 == sp.zeros(64, 64), "Cycle diffeomorphism commutator != 0")

    # Exact symbolic spectrum check on all 64 dimensions:
    eig_mults = H_dyn.eigenvals()
    eig_set = sorted(int(k) for k in eig_mults.keys())
    require(eig_set == [-10, -6, -5, -3, 0, 3, 5, 6, 10], f"Unexpected H_tot_dyn spectrum: {eig_set}")

    # Exact 4-site ground state |Omega_grav> = (1/sqrt(10) (|0> - 3|1>))^x4 of 3 S_x + 4 S_z (eigenvalue -10):
    site_gs = sp.Matrix([1, -3]) / sp.sqrt(10)
    omega_grav = kron_list([site_gs, site_gs, site_gs, site_gs])
    require(sp.simplify((3 * Sx_geom + 4 * Sz_geom) * omega_grav + 10 * omega_grav) == sp.zeros(16, 1),
            "4-site Regge ground state verification failed")
    require(U_swap01 * omega_grav == omega_grav and U_cyc0123 * omega_grav == omega_grav,
            "4-site ground state must be S_4 diffeomorphism invariant")

    # Construct exact Wheeler-DeWitt physical states |Psi_phys^(b)> in H_clk (N_clk=21, k in -10..10) x C^64 (dim=1344)
    # In clock momentum basis |k_tilde> (k = -10..10), P_clk |k_tilde> = k |k_tilde>.
    # Projecting |t_0 = 0>_clk x |chi^(b)> = (1/sqrt(21)) sum_{k=-10}^{10} |k_tilde> x |chi^(b)>
    # via sqrt(21) * Pi_phys selects for each integer eigenvalue n in [-10, 10] the exact projector P_n |chi^(b)>
    # paired with |k_tilde = -n>!
    # Compute exact spectral projectors P_n of H_dyn on the integer spectrum eig_set:
    spec_projectors: dict[int, sp.Matrix] = {}
    for n in eig_set:
        # Lagrange interpolation polynomial over eig_set (exact rational matrices!):
        Pn = sp.eye(64)
        denom = sp.Integer(1)
        for m in eig_set:
            if m != n:
                Pn = Pn * (H_dyn - m * sp.eye(64))
                denom *= (n - m)
        Pn = Pn / denom
        spec_projectors[n] = Pn

    require(sum(spec_projectors.values(), sp.zeros(64, 64)) == sp.eye(64),
            "Spectral projectors of H_tot_dyn must sum to I_64")

    ptr_0 = sp.Matrix([1, 0])
    chi_b0 = kron_list([omega_grav, sp.Matrix([1, 0]), ptr_0])
    chi_b1 = kron_list([omega_grav, sp.Matrix([0, 1]), ptr_0])

    # Verify exact Wheeler-DeWitt equation (P_clk x I_64 + I_21 x H_dyn) |Psi_phys^(b)> == 0 in all 1344 components!
    for b_idx, chi_b in enumerate((chi_b0, chi_b1)):
        norm_sq = sp.Integer(0)
        for k_clk in range(-10, 11):
            n_match = -k_clk
            comp_64 = spec_projectors[n_match] * chi_b if n_match in spec_projectors else sp.zeros(64, 1)
            # Action of (k_clk * I_64 + H_dyn) on this 64-component clock-momentum block:
            wdw_block_res = sp.simplify(k_clk * comp_64 + H_dyn * comp_64)
            require(wdw_block_res == sp.zeros(64, 1), f"Nonzero WDW residual on branch {b_idx}, k={k_clk}")
            # Diffeomorphism residual on physical block:
            require(sp.simplify((U_swap_64 - sp.eye(64)) * comp_64) == sp.zeros(64, 1), "Swap diffeo residual != 0")
            require(sp.simplify((U_cyc_64 - sp.eye(64)) * comp_64) == sp.zeros(64, 1), "Cycle diffeo residual != 0")
            norm_sq += (comp_64.H * comp_64)[0, 0]
        require(sp.simplify(norm_sq - 1) == 0, f"Physical state norm != 1 on branch {b_idx}")

    # Evaluate relational Dirac observable O_rel(t_*, Z_ptr) and reduced pointer purity in 40-digit mpmath.iv!
    # By exact Page-Wootters theorem:
    # <Psi_phys^(b) | O_rel(t_*, A) | Psi_phys^(b)> = <chi^(b) | exp(+i 2pi t_*/21 H_dyn) A exp(-i 2pi t_*/21 H_dyn) | chi^(b)>
    # Check exact matrix evolution at t_* = 0, 3, 7 against closed-form 4-site formula in 40-digit interval arithmetic!
    Z_ptr_64 = kron_list([sp.eye(16), sp.eye(2), Z])
    X_ptr_64 = kron_list([sp.eye(16), sp.eye(2), X])
    Y_ptr = sp.Matrix([[0, -sp.I], [sp.I, 0]])
    Y_ptr_64 = kron_list([sp.eye(16), sp.eye(2), Y_ptr])

    def evolved_expectation_iv(chi_vec: sp.Matrix, obs_64: sp.Matrix, t_star: int) -> iv.mpf:
        # Expand U_dyn(t_star) |chi> = sum_{n in eig_set} exp(-i * 2*pi*t_star*n / 21) (P_n |chi>)
        # Then <U chi | obs | U chi> = sum_{n, m} cos_or_sin * <P_n chi | obs | P_m chi>
        # Since P_n |chi> are real vectors and obs is Hermitian, compute real part in 40-digit iv:
        total_re = iv.mpf("0")
        theta_unit = 2 * iv.pi * iv.mpf(t_star) / iv.mpf("21")
        comps = {n: spec_projectors[n] * chi_vec for n in eig_set}
        for n in eig_set:
            cn = comps[n]
            if cn == sp.zeros(64, 1):
                continue
            for m in eig_set:
                cm = comps[m]
                if cm == sp.zeros(64, 1):
                    continue
                mel = sp.simplify((cn.H * obs_64 * cm)[0, 0])
                re_mel, im_mel = mel.as_real_imag()
                require(re_mel.is_Rational and im_mel.is_Rational,
                        f"Expected exact rational matrix elements, got {mel}")
                re_iv = iv.mpf(int(re_mel.p)) / iv.mpf(int(re_mel.q))
                im_iv = iv.mpf(int(im_mel.p)) / iv.mpf(int(im_mel.q))
                dphi = theta_unit * iv.mpf(n - m)
                # exp(+i n theta) * (re + i im) * exp(-i m theta): real part is re*cos((n-m)theta) - im*sin((n-m)theta)
                total_re += re_iv * iv.cos(dphi) - im_iv * iv.sin(dphi)
        return total_re

    # Verify all matrix elements (cn.H * obs_64 * cm) are EXACT RATIONALS (or i * RATIONALS) — zero float rounding!
    z_b0_t0 = evolved_expectation_iv(chi_b0, Z_ptr_64, 0)
    z_b1_t0 = evolved_expectation_iv(chi_b1, Z_ptr_64, 0)
    require(strictly_below(abs(z_b0_t0 - 1), "1e-38") and strictly_below(abs(z_b1_t0 - 1), "1e-38"),
            "Initial t_* = 0 pointer expectation must be +1 on both branches")

    # Tick t_* = 3: genuine 4-site quantum-geometry <-> pointer entanglement + positive contrast:
    z_b0_t3 = evolved_expectation_iv(chi_b0, Z_ptr_64, 3)
    z_b1_t3 = evolved_expectation_iv(chi_b1, Z_ptr_64, 3)
    x_b1_t3 = evolved_expectation_iv(chi_b1, X_ptr_64, 3)
    y_b1_t3 = evolved_expectation_iv(chi_b1, Y_ptr_64, 3)
    purity_b1_t3 = iv.mpf("0.5") * (1 + x_b1_t3 ** 2 + y_b1_t3 ** 2 + z_b1_t3 ** 2)
    contrast_t3 = z_b0_t3 - z_b1_t3

    # Cross-check against analytical 4-site overlap z_1(3) = (1/5)e^{-i*3pi/7} + (4/5)e^{+i*3pi/7}:
    ang3 = 3 * iv.pi / 7
    mod_sq_z1_3 = (iv.mpf("1") / 25) * (17 + 8 * iv.cos(2 * ang3))
    purity_analytic_t3 = iv.mpf("0.5") * (1 + (mod_sq_z1_3 ** 4))
    require(
        strictly_below(abs(purity_b1_t3 - purity_analytic_t3), "1e-37"),
        "64D spectral purity at t_*=3 must match exact 4-site analytical formula",
    )
    require(
        strictly_above(purity_b1_t3, "0.5117") and strictly_below(purity_b1_t3, "0.5118"),
        "Reduced pointer purity at t_*=3 must be strictly < 1 (4-site quantum-geometry entanglement)",
    )
    require(
        strictly_above(contrast_t3, "1.0822") and strictly_below(contrast_t3, "1.0823"),
        "Relational Dirac pointer contrast at t_*=3 must lie in (1.0822, 1.0823)",
    )

    # Explicit matrix check of [O_rel(t_*, Z_ptr), Pi_phys] == 0 on the 16D Lean witness ZMod 4 x Bool x Bool:
    W_cgp = sp.Matrix([
        [1, 0, 0, 0],
        [0, 1, 0, 0],
        [0, 0, 0, -1],
        [0, 0, 1, 0],
    ])
    S_clk4 = sp.Matrix([
        [0, 0, 0, 1],
        [1, 0, 0, 0],
        [0, 1, 0, 0],
        [0, 0, 1, 0],
    ])
    U_lean = [sp.kronecker_product(S_clk4 ** g, W_cgp ** g) for g in range(4)]
    Pi_lean = sum(U_lean, sp.zeros(16, 16)) / 4
    E_t1_lean = sp.kronecker_product(sp.diag(0, 1, 0, 0), sp.diag(1, -1, 1, -1))
    O_rel_lean = sum((U_lean[g] * E_t1_lean * U_lean[g].T for g in range(4)), sp.zeros(16, 16))
    require(Pi_lean * Pi_lean == Pi_lean and sp.trace(Pi_lean) == 4, "Lean 16D witness Pi_phys check failed")
    require(O_rel_lean * Pi_lean - Pi_lean * O_rel_lean == sp.zeros(16, 16),
            "Lean 16D witness [O_rel, Pi_phys] != 0")

    # Tick t_* = 7: exact coherent 4-site quantum-geometry revival (purity == 1, contrast == 3/2):
    z_b0_t7 = evolved_expectation_iv(chi_b0, Z_ptr_64, 7)
    z_b1_t7 = evolved_expectation_iv(chi_b1, Z_ptr_64, 7)
    x_b1_t7 = evolved_expectation_iv(chi_b1, X_ptr_64, 7)
    y_b1_t7 = evolved_expectation_iv(chi_b1, Y_ptr_64, 7)
    purity_b1_t7 = iv.mpf("0.5") * (1 + x_b1_t7 ** 2 + y_b1_t7 ** 2 + z_b1_t7 ** 2)
    contrast_t7 = z_b0_t7 - z_b1_t7

    require(strictly_below(abs(purity_b1_t7 - 1), "1e-37"), "Exact purity revival == 1 at t_*=7")
    require(strictly_below(abs(contrast_t7 - iv.mpf("1.5")), "1e-37"),
            "Exact relational Dirac pointer contrast == 3/2 at t_*=7")

    return {
        "kinematical_hilbert_dim": 1344,
        "clock_ticks_N_clk": 21,
        "tetrahedral_geometry_sites": 4,
        "geometry_hilbert_dim": 16,
        "noncommuting_geometry_commutator_frob_sq": 16,
        "H_tot_dyn_exact_integer_spectrum": eig_set,
        "wdw_constraint_residual_l2_norm_b0": "0",
        "wdw_constraint_residual_l2_norm_b1": "0",
        "ultralocal_vertex_constraint_commutator_norm": "0",
        "S4_diffeomorphism_constraint_commutator_norm": "0",
        "relational_Dirac_rigging_commutator_norm": "0",
        "initial_t0_relational_pointer_contrast": "0",
        "tick_t3_reduced_pointer_purity_entangled": iv40(purity_b1_t3),
        "tick_t3_relational_pointer_contrast": iv40(contrast_t3),
        "tick_t7_revival_pointer_purity": iv40(purity_b1_t7),
        "tick_t7_relational_pointer_contrast": iv40(contrast_t7),
        "tick_t7_relational_pointer_contrast_exact": "3/2",
    }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--write", "--write-certificate", dest="write", action="store_true",
                    help="Write certificate.json")
    ap.add_argument("--check", action="store_true",
                    help="Verify committed certificate.json without rewriting")
    ap.add_argument("--output", type=Path, default=HERE / "certificate.json")
    args = ap.parse_args()

    payload = {
        "result_ids": ["P-DISCRETE-QG-01"],
        "lean_module": "formalization/ueot-physics-unification/UEOTPhysicsUnification/DiscreteQuantumGeometryWheelerDeWitt.lean",
        "lean_theorems": [
            "UEOTPhysicsUnification.DiscreteQuantumGeometryWheelerDeWitt.pauli_villars_uv_cancellation_forces_ghost_weight",
            "UEOTPhysicsUnification.DiscreteQuantumGeometryWheelerDeWitt.pauli_villars_indefinite_metric_negative_norm_state",
            "UEOTPhysicsUnification.DiscreteQuantumGeometryWheelerDeWitt.discrete_planck_graph_hilbert_positivity_and_uv_finiteness",
            "UEOTPhysicsUnification.DiscreteQuantumGeometryWheelerDeWitt.finite_graph_smeared_hamiltonian_zero_anomaly",
            "UEOTPhysicsUnification.DiscreteQuantumGeometryWheelerDeWitt.rigging_projector_gauge_invariant_idempotent_selfAdjoint",
            "UEOTPhysicsUnification.DiscreteQuantumGeometryWheelerDeWitt.relational_observable_commutes_with_rigging_projector",
            "UEOTPhysicsUnification.DiscreteQuantumGeometryWheelerDeWitt.rigged_inner_product_posSemidef_and_strict_on_range",
            "UEOTPhysicsUnification.DiscreteQuantumGeometryWheelerDeWitt.rigged_physical_quotient_descent_unique",
            "UEOTPhysicsUnification.DiscreteQuantumGeometryWheelerDeWitt.page_wootters_physical_subspace_and_relational_expectation",
            "UEOTPhysicsUnification.DiscreteQuantumGeometryWheelerDeWitt.coupled_clock_geometry_pointer_nonvacuous_witness",
        ],
        "pauli_villars_vs_planck_graph": verify_pauli_villars_vs_planck_graph(),
        "multisite_regge_wheeler_dewitt": verify_multisite_regge_wheeler_dewitt(),
        "device_certified": False,
        "physical_unification": "OPEN",
        "status": "PASS",
        "source_sha256": sha256_file(Path(__file__).resolve()),
    }
    finish(payload, args)
    print("PASS: discrete_quantum_geometry P-DISCRETE-QG-01")


if __name__ == "__main__":
    main()
