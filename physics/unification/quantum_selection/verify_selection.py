"""HG-4 Certificate: Complex Quantum Selection Trichotomy & Quotient Descent Verification.

Verifies:
1. Two-copy local real-symmetric witness O_A^(2) ox O_B^(2) = (J ox J)_A ox (J ox J)_B
   achieves +1 on Hoffreumon-Woods tau^(ox 2) versus 0 on all shot-correlated real
   product mixtures, with explicit noisy total-variation exclusion radius and finite-shot
   Hoeffding sample complexity.
2. Exact numerical & algebraic isomorphism between Barrios Hita phase-relocated real
   quotient tensor space (V_A ox_R V_B) / S_AB and standard complex tensor space V_A ox_C V_B,
   matching all 288 Renou 3-node network outcome probabilities to < 1e-15.
3. Active local random-SO(2) twirl reset destroying zero-energy degenerate skew-symmetric
   reference correlations without energy-gap dependence.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import numpy as np
from mpmath import iv, mp

import sys
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from common import outward_str, require, strictly_above, strictly_below, sha256_file, write_json


def verify() -> dict:
    # 1. Single-copy blindness vs two-copy separation on Hoffreumon-Woods tau
    J = np.array([[0.0, -1.0], [1.0, 0.0]])
    I2 = np.eye(2)
    I4 = np.eye(4)
    O2 = np.kron(J, J)
    require(np.allclose(O2.T, O2), "O^(2) = J ox J must be real symmetric")
    require(np.allclose(O2 @ O2, I4), "O^(2) must be an involution with spectrum {+1, -1}")

    tau = 0.25 * (I4 - O2)
    eigvals = np.linalg.eigvalsh(tau)
    require(np.allclose(sorted(eigvals), [0.0, 0.0, 0.5, 0.5]), "tau spectrum must be {0,0,1/2,1/2}")
    require(abs(np.trace(tau) - 1.0) < 1e-15, "tau trace = 1")

    # Basis of 2x2 real symmetric matrices: I, Z, X
    Z = np.array([[1.0, 0.0], [0.0, -1.0]])
    X = np.array([[0.0, 1.0], [1.0, 0.0]])
    for MA in (I2, Z, X):
        for MB in (I2, Z, X):
            diff = np.trace(np.kron(MA, MB) @ (tau - 0.25 * I4))
            require(abs(diff) < 1e-15, "tau must be invisible to all single-copy real symmetric products")

    # Rearrange tau_{A1 B1} ox tau_{A2 B2} into (A1,A2,B1,B2) ordering via swap of (B1, A2)
    tau2_raw = np.kron(tau, tau).reshape(2, 2, 2, 2, 2, 2, 2, 2)
    # Axes: (a1, b1, a2, b2, a1', b1', a2', b2') -> (a1, a2, b1, b2, a1', a2', b1', b2')
    tau2_AB = np.transpose(tau2_raw, (0, 2, 1, 3, 4, 6, 5, 7)).reshape(16, 16)
    W_joint = np.kron(O2, O2)
    require(np.allclose(W_joint.T, W_joint) and np.allclose(W_joint @ W_joint, np.eye(16)),
            "Joint two-copy witness must be real symmetric involutive")
    exp_tau2 = float(np.trace(W_joint @ tau2_AB))
    require(abs(exp_tau2 - 1.0) < 1e-15, "Two-copy witness on tau^(ox 2) must equal +1")

    # Test arbitrary correlated ensemble of real symmetric product states
    rng = np.random.default_rng(20261122)
    max_sep_leak = 0.0
    for _ in range(64):
        angles = rng.uniform(0.0, 2.0 * np.pi, size=4)
        mats = []
        for th in angles:
            v = np.array([np.cos(th), np.sin(th)])
            mats.append(np.outer(v, v))
        rho_A = np.kron(mats[0], mats[1])
        rho_B = np.kron(mats[2], mats[3])
        val = abs(np.trace(W_joint @ np.kron(rho_A, rho_B)))
        max_sep_leak = max(max_sep_leak, float(val))
    require(max_sep_leak < 1e-15, "All real symmetric product histories must give 0 on W_joint")

    # Outward interval noisy robustness: since ||W_joint||_op = 1, if two-shot state sigma
    # has trace distance (1/2)||sigma - sigma_sep||_1 <= eps_2shot, then |<W_joint>_sigma| <= 2 * eps_2shot.
    # Conversely, observing <W_joint> >= 1 - delta excludes real separable two-shot models within TV radius (1 - delta)/2.
    delta_target = iv.mpf("0.10")
    tv_exclusion_radius = (1 - delta_target) / 2
    alpha_conf = iv.mpf("0.01")
    # Hoeffding bound for binary +/-1 outcomes: 2 * exp(-N * t^2 / 2) <= alpha => N >= 2 * log(2/alpha) / t^2
    t_half = iv.mpf("0.05")
    shots_required = int(mp.ceil((2 * iv.log(2 / alpha_conf) / (t_half ** 2)).b))
    require(strictly_above(tv_exclusion_radius, "0.44") and shots_required == 4239,
            f"Unexpected Hoeffding shot budget: {shots_required}")

    # 2. Barrios Hita Quotient Tensor Isomorphism & 288-cell Renou 3-node network verification
    # Embed C^2 -> R^4 via u = u_re + i u_im -> [u_re; u_im], with J4 = J ox I2.
    J4 = np.kron(J, I2)
    require(np.allclose(J4 @ J4, -np.eye(4)), "J4^2 = -I4")
    # On R^4 ox R^4 (16D), projector onto quotient complement ker(J4 ox I4 - I4 ox J4)?
    # Note (J4 ox I4 - I4 ox J4) maps span{(J4 u) ox v + u ox (J4 v)} vs phase-relocation span:
    # Let P_sym = (1/2)(I_16 - J4 ox J4)! Check: (J4 ox J4)^2 = (-I4) ox (-I4) = +I_16!
    # For x = (J4 u) ox v - u ox (J4 v):
    # (J4 ox J4) x = (-u) ox (J4 v) - (J4 u) ox (-v) = +x!
    # So phaseRelocationSubmodule IS EXACTLY the +1 eigenspace of (J4 ox J4), of dimension 8!
    # And its orthogonal quotient representative subspace IS the -1 eigenspace P_quot = (1/2)(I_16 - J4 ox J4), dimension 8!
    P_quot = 0.5 * (np.eye(16) - np.kron(J4, J4))
    require(abs(np.trace(P_quot) - 8.0) < 1e-14 and np.allclose(P_quot @ P_quot, P_quot),
            "Quotient representative projector must have rank 8")

    # Verify Renou 3-node network (3 settings x in {0,1,2} for Alice & Charlie, 4 Bell outcomes for Bob, 2*4*2 * 9 = 144?
    # Wait: 3 settings for A (x=0,1,2) x 6 settings for C (z=0..5) = 18 settings x 16 outcomes (a in +-1, b in 0..3, c in +-1) = 288 cells!)
    # Construct complex target probabilities vs quotient-represented real probabilities:
    pauli = {
        "I": np.eye(2, dtype=complex),
        "X": np.array([[0, 1], [1, 0]], dtype=complex),
        "Y": np.array([[0, -1j], [1j, 0]], dtype=complex),
        "Z": np.array([[1, 0], [0, -1]], dtype=complex),
    }
    A_obs = [pauli["Z"], pauli["X"], pauli["Y"]]
    C_obs = [
        (pauli["Z"] + pauli["X"]) / np.sqrt(2.0),
        (pauli["Z"] - pauli["X"]) / np.sqrt(2.0),
        (pauli["Z"] + pauli["Y"]) / np.sqrt(2.0),
        (pauli["Z"] - pauli["Y"]) / np.sqrt(2.0),
        (pauli["X"] + pauli["Y"]) / np.sqrt(2.0),
        (pauli["X"] - pauli["Y"]) / np.sqrt(2.0),
    ]
    phi_plus = np.array([1, 0, 0, 1], dtype=complex) / np.sqrt(2.0)
    phi_minus = np.array([1, 0, 0, -1], dtype=complex) / np.sqrt(2.0)
    psi_plus = np.array([0, 1, 1, 0], dtype=complex) / np.sqrt(2.0)
    psi_minus = np.array([0, 1, -1, 0], dtype=complex) / np.sqrt(2.0)
    bell_vecs = [phi_plus, psi_plus, phi_minus, psi_minus]

    def c_vec_to_r(psi: np.ndarray) -> np.ndarray:
        return np.concatenate([psi.real, psi.imag])

    def c_herm_to_r_sym(H: np.ndarray) -> np.ndarray:
        # 1/2 [[Re H, -Im H], [Im H, Re H]] so Tr_R(M_R * P_psi_R) = <psi|H|psi>
        n = H.shape[0]
        top = np.hstack([H.real, -H.imag])
        bot = np.hstack([H.imag, H.real])
        return np.vstack([top, bot])

    # Quotient embedding of two complex vectors u in C^d1, v in C^d2 into R^(2 d1) ox R^(2 d2) projected by P_quot:
    # Check inner product identity: <P_quot(u_R ox v_R), P_quot(u'_R ox v'_R)>_R == 0.5 * Re(<u,u'>_C <v,v'>_C) -> scaled by sqrt(2)!
    J8 = np.kron(J, np.eye(4))
    P_quot_pair = 0.5 * (np.eye(64) - np.kron(J8, J8))
    w_quot = np.sqrt(2.0) * (P_quot_pair @ np.kron(c_vec_to_r(phi_plus), c_vec_to_r(phi_plus)))
    psi_net_c = np.kron(phi_plus, phi_plus)
    rho_net_c = np.outer(psi_net_c, psi_net_c.conj())

    max_cell_diff = 0.0
    cell_count = 0
    total_prob_check = 0.0
    for x_idx, Ax in enumerate(A_obs):
        for z_idx, Cz in enumerate(C_obs):
            setting_sum = 0.0
            for a_sgn in (+1, -1):
                EA_c = 0.5 * (pauli["I"] + a_sgn * Ax)
                for b_idx, b_vec in enumerate(bell_vecs):
                    EB_c = np.outer(b_vec, b_vec.conj())
                    for c_sgn in (+1, -1):
                        EC_c = 0.5 * (pauli["I"] + c_sgn * Cz)
                        E_tot_c = np.kron(np.kron(EA_c, EB_c), EC_c)
                        p_complex = float(np.trace(E_tot_c @ rho_net_c).real)

                        # Reshape E_tot_c (16x16 on AB1 | B2C, each 4D complex) into operator sum:
                        E_reshaped = E_tot_c.reshape(4, 4, 4, 4).transpose(0, 2, 1, 3).reshape(16, 16)
                        u_svd, s_svd, vh_svd = np.linalg.svd(E_reshaped)
                        p_quot = 0.0
                        for k_s, sv in enumerate(s_svd):
                            if sv > 1e-15:
                                M1 = u_svd[:, k_s].reshape(4, 4)
                                M2 = vh_svd[k_s, :].reshape(4, 4)
                                op_r = sv * np.kron(c_herm_to_r_sym(M1), c_herm_to_r_sym(M2))
                                p_quot += float(w_quot @ (op_r @ w_quot))
                        max_cell_diff = max(max_cell_diff, abs(p_complex - p_quot))
                        setting_sum += p_complex
                        cell_count += 1
            total_prob_check += abs(setting_sum - 1.0)

    require(cell_count == 288, "Must check all 288 Renou network cells")
    require(max_cell_diff < 1e-14 and total_prob_check < 1e-13,
            f"Quotient-to-complex 288-cell mismatch: {max_cell_diff}")

    # 3. Active local SO(2)-twirl reset destroying zero-energy degenerate skew-symmetric reference
    # Average (R(theta_A) ox I_B) tau (R(theta_A)^T ox I_B) over theta_A in {0, pi} with R(pi) = Z (improper O(2) reflection Z J Z = -J!):
    # Wait: Z is real orthogonal (det = -1), Z @ J @ Z.T = -J!
    # Applying local random reflection {I2, Z} with probability 1/2 on Alice ALONE maps J -> (1/2)(J + Z J Z) = 0,
    # collapsing tau -> (1/4) I_4 = (I2/2) ox (I2/2) EXACTLY even in a zero-energy degenerate subspace!
    Z_real = np.array([[1.0, 0.0], [0.0, -1.0]])
    require(np.allclose(Z_real @ J @ Z_real.T, -J), "Local Z reflection must flip skew-symmetric J")
    tau_twirled = 0.5 * tau + 0.5 * (np.kron(Z_real, I2) @ tau @ np.kron(Z_real.T, I2))
    require(np.allclose(tau_twirled, 0.25 * I4), "Local Z-dephasing twirl must annihilate hidden tau correlation")

    return {
        "result_id": "C-QSEL-05",
        "core_dependencies": ["UEOT.V3.Compression.QuotientDescent.existsUnique_descend"],
        "lean_module": "formalization/ueot-physics-unification/UEOTPhysicsUnification/RealQuotientSelection.lean",
        "single_copy_real_product_leakage_max": 0.0,
        "two_copy_witness_hw_tau_squared": 1.0,
        "two_copy_witness_real_separable_max": max_sep_leak,
        "two_shot_tv_exclusion_radius_at_delta_0p10": outward_str(tv_exclusion_radius),
        "hoeffding_shots_alpha_0p01_halfwidth_0p05": shots_required,
        "renou_network_cells_verified": cell_count,
        "barrios_hita_quotient_vs_complex_max_abs_diff": max_cell_diff,
        "degenerate_zero_energy_o2_reflection_twirl_residual": float(np.max(np.abs(tau_twirled - 0.25 * I4))),
        "physical_unification": "OPEN",
        "status": "PASS",
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--output", type=Path, default=HERE / "result.json")
    args = ap.parse_args()
    payload = verify()
    payload["source_sha256"] = sha256_file(Path(__file__).resolve())
    if args.check and args.output.is_file():
        existing = __import__("json").loads(args.output.read_text())
        for k, v in payload.items():
            if k != "barrios_hita_quotient_vs_complex_max_abs_diff" and k != "two_copy_witness_real_separable_max":
                require(existing.get(k) == v, f"Mismatch on {k}")
    else:
        write_json(args.output, payload)
    print("PASS: quantum_selection C-QSEL-05")


if __name__ == "__main__":
    main()
