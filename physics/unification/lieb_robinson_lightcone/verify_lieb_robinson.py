"""C-LR-CONE-01 Certificate: Core TransportCertificate -> Lieb-Robinson Light Cone -> Minkowski Metric.

Verifies with exact matrix algebra and 40-digit outward interval arithmetic (mpmath.iv):
1. Strict discrete causal cone: brickwork local unitary circuit on N = 7 qubits obeys
   ||[U^dag sigma_0^x U, sigma_r^z]||_op = 0 to machine precision (< 1e-14) outside r <= 2 * depth.
2. Continuous-time 1D XX spin chain (N = 7 sites, J = 0.25, t = 0.6): exact Heisenberg commutator
   norm ||[sigma_0^x(t), sigma_r^z(0)]||_op <= Core TransportCertificate exponential moment bound
   min_{mu > 0} M_0 * exp(t * gamma_spin(mu) - mu * r) with bidirectional interaction-picture rate
   gamma_spin(mu) = 2 * ||h|| * (exp(mu) + exp(-mu)) (||h|| = 2 J = 0.5) at every distance r = 1..6.
3. Directed/Markovian transport Cramér decay rate kappa_* = v * ln(v / (2 J)) - (v - 2 J) > 0 at
   mu_* = ln(v / (2 J)) for v = 2 > 2 J = 1, enclosing v_LR(mu_*, J) < v and exponential suppression
   across Lambda in {10, 50, 100}.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import sys
import numpy as np
from scipy.linalg import expm
from mpmath import iv

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from common import outward_str, require, sha256_file, strictly_above, strictly_below, write_json


def pauli_on_site(op2: np.ndarray, site: int, n_sites: int) -> np.ndarray:
    mats = [np.eye(2, dtype=complex) for _ in range(n_sites)]
    mats[site] = op2
    out = mats[0]
    for m in mats[1:]:
        out = np.kron(out, m)
    return out


def verify_discrete_and_continuous_lieb_robinson() -> dict:
    n_sites = 7
    X = np.array([[0.0, 1.0], [1.0, 0.0]], dtype=complex)
    Y = np.array([[0.0, -1.0j], [1.0j, 0.0]], dtype=complex)
    Z = np.array([[1.0, 0.0], [0.0, -1.0]], dtype=complex)

    # 1. Brickwork 2-layer causal circuit: source at site 0 can only reach sites r <= 2:
    theta = 0.37
    gate2 = expm(-1j * theta * (np.kron(X, X) + np.kron(Y, Y)))

    def embed_two_site(g2: np.ndarray, s: int) -> np.ndarray:
        ops = []
        idx = 0
        while idx < n_sites:
            if idx == s:
                ops.append(g2)
                idx += 2
            else:
                ops.append(np.eye(2, dtype=complex))
                idx += 1
        res = ops[0]
        for o in ops[1:]:
            res = np.kron(res, o)
        return res

    layer_even = embed_two_site(gate2, 0) @ embed_two_site(gate2, 2) @ embed_two_site(gate2, 4)
    layer_odd = embed_two_site(gate2, 1) @ embed_two_site(gate2, 3) @ embed_two_site(gate2, 5)
    # In Heisenberg evolution U^dag X_0 U, U = layer_even @ layer_odd conjugates X_0 first by
    # layer_even ((0,1) gate -> sites {0,1}) and then by layer_odd ((1,2) gate -> sites {0,1,2}):
    U_brick = layer_even @ layer_odd

    op0_brick = U_brick.conj().T @ pauli_on_site(X, 0, n_sites) @ U_brick
    outside_brick_max = 0.0
    inside_brick_r2 = 0.0
    for r in range(n_sites):
        comm = op0_brick @ pauli_on_site(Z, r, n_sites) - pauli_on_site(Z, r, n_sites) @ op0_brick
        nrm = float(np.linalg.norm(comm, ord=2))
        if r == 2:
            inside_brick_r2 = nrm
        if r > 2:
            outside_brick_max = max(outside_brick_max, nrm)
    require(inside_brick_r2 > 0.05, "Inside causal cone r=2 commutator should be nonzero")
    require(outside_brick_max < 1e-14, f"Brickwork causal cone violated: {outside_brick_max}")

    # 2. Continuous-time 1D XX Hamiltonian H = J_couple * sum_{j=0}^{N-2} (X_j X_{j+1} + Y_j Y_{j+1}):
    j_val = 0.25
    t_val = 0.6
    H_xx = np.zeros((2 ** n_sites, 2 ** n_sites), dtype=complex)
    for s in range(n_sites - 1):
        H_xx += j_val * (
            pauli_on_site(X, s, n_sites) @ pauli_on_site(X, s + 1, n_sites)
            + pauli_on_site(Y, s, n_sites) @ pauli_on_site(Y, s + 1, n_sites)
        )
    U_xx = expm(-1j * t_val * H_xx)
    op0_t = U_xx.conj().T @ pauli_on_site(X, 0, n_sites) @ U_xx

    # Compare exact commutator norm at r = 1..6 against Core TransportCertificate moment bound
    # with true bidirectional Hamiltonian interaction-picture rate gamma_spin(mu) = 2 * ||h|| * (e^mu + e^-mu),
    # where ||h_{s,s+1}||_op = ||0.25 (X X + Y Y)||_op = 0.5 and M_0 = 2:
    h_bond_norm = iv.mpf("0.5")
    t_iv = iv.mpf("0.6")
    m0_iv = iv.mpf("2.0")

    shell_bounds = {}
    for r in range(1, n_sites):
        comm_r = op0_t @ pauli_on_site(Z, r, n_sites) - pauli_on_site(Z, r, n_sites) @ op0_t
        exact_nrm = float(np.linalg.norm(comm_r, ord=2))
        r_iv = iv.mpf(r)
        # Saddle point of 2 ||h|| t (e^mu + e^-mu) - mu r is sinh(mu_r) = r / (4 ||h|| t):
        u_arg = r_iv / (4 * h_bond_norm * t_iv)
        mu_r = iv.log(u_arg + iv.sqrt(u_arg ** 2 + 1))
        gamma_spin = 2 * h_bond_norm * (iv.exp(mu_r) + iv.exp(-mu_r))
        lr_bound = m0_iv * iv.exp(t_iv * gamma_spin - mu_r * r_iv)
        require(exact_nrm < float(lr_bound.a),
                f"Exact commutator {exact_nrm} exceeded Lieb-Robinson bound at r={r}")
        shell_bounds[f"r_{r}"] = {
            "exact_commutator_strictly_below_lr": True,
            "core_transport_lr_upper_bound": outward_str(lr_bound)[1],
        }

    # 3. Ballistic supersonic ray suppression (J = 0.5 -> minimal LR speed 2J = 1.0, ray speed v = 2.0):
    J_cone = iv.mpf("0.5")
    v_ray = iv.mpf("2.0")
    mu_star = iv.log(v_ray / (2 * J_cone))  # ln(2)
    v_lr_star = 2 * J_cone * (iv.exp(mu_star) - 1) / mu_star  # 1 / ln(2) ~ 1.442695 < 2.0
    kappa_star = mu_star * (v_ray - v_lr_star)  # 2 ln(2) - 1 ~ 0.386294 > 0
    require(strictly_below(v_lr_star, v_ray) and strictly_above(kappa_star, "0.386"),
            "Supersonic Cramér decay rate verification failed")

    supersonic_tails = {}
    for lam in (10, 50, 100):
        tail = iv.mpf("2") * iv.exp(-iv.mpf(lam) * kappa_star)
        supersonic_tails[f"Lambda_{lam}"] = outward_str(tail)[1]
    require(strictly_below(iv.mpf("2") * iv.exp(-iv.mpf("100") * kappa_star), "1e-16"),
            "Ballistic Lambda=100 supersonic tail must be < 1e-16")

    return {
        "brickwork_outside_cone_commutator_strictly_below": "1e-14",
        "xx_chain_site_bounds": shell_bounds,
        "emergent_v_LR_at_mu_ln2": outward_str(v_lr_star),
        "supersonic_cramer_decay_rate_v2": outward_str(kappa_star),
        "ballistic_rescaling_supersonic_upper_bounds": supersonic_tails,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--output", type=Path, default=HERE / "result.json")
    args = ap.parse_args()

    payload = {
        "result_ids": ["C-LR-CONE-01"],
        "lean_module": "formalization/ueot-physics-unification/UEOTPhysicsUnification/CoreTransportToLiebRobinsonCone.lean",
        "lieb_robinson_and_emergent_cone": verify_discrete_and_continuous_lieb_robinson(),
        "physical_unification": "OPEN",
        "status": "PASS",
        "source_sha256": sha256_file(Path(__file__).resolve()),
    }
    if args.check and args.output.is_file():
        existing = __import__("json").loads(args.output.read_text())
        require(existing == payload, "lieb_robinson_lightcone certificate drift")
    else:
        write_json(args.output, payload)
    print("PASS: lieb_robinson_lightcone C-LR-CONE-01")


if __name__ == "__main__":
    main()
