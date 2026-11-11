#!/usr/bin/env python3
"""Source-derived finite controls for the UEOT micro/truncation bridge.

This is an exact symbolic finite check plus labelled floating diagnostics.
It is neither an infinite-dimensional proof nor hardware data.
Run with --output receipt.json to bind the receipt to this source's SHA-256.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import platform
from datetime import datetime, timezone
from pathlib import Path

import numpy as np
import scipy
import sympy as sp
from scipy.linalg import expm


EXACT: list[dict] = []
FLOAT: list[dict] = []


def exact(name: str, condition, detail: str = "") -> None:
    ok = bool(condition)
    EXACT.append({"name": name, "pass": ok, "detail": detail})
    if not ok:
        raise AssertionError(name)


def equal_matrix(a: sp.Matrix, b: sp.Matrix) -> bool:
    return all(sp.simplify(x) == 0 for x in a - b)


def diagcheck(name: str, value: float, limit: float = 2e-12) -> None:
    value = float(value)
    ok = bool(abs(value) <= limit)
    FLOAT.append({"name": name, "value": value, "limit": limit, "pass": ok})
    if not ok:
        raise AssertionError(name)


def sym_channel(kraus: list[sp.Matrix], rho: sp.Matrix) -> sp.Matrix:
    return sum((k * rho * k.H for k in kraus), sp.zeros(rho.rows))


def symbolic_controls() -> dict:
    I, ii = sp.eye(3), sp.I
    G = sp.diag(0, 1, 1)  # |g,0>, |e,0>, |g,1>
    z = sp.Rational(3, 5) + ii * sp.Rational(4, 5)
    U0 = sp.diag(1, z, 1)
    U1 = sp.Matrix([[1, 0, 0], [0, sp.Rational(3, 5), -ii * sp.Rational(4, 5)],
                    [0, -ii * sp.Rational(4, 5), sp.Rational(3, 5)]])
    exact("phase_unitary", equal_matrix(U0.H * U0, I))
    exact("jc_unitary", equal_matrix(U1.H * U1, I))
    exact("phase_conserves_G", equal_matrix(U0 * G, G * U0))
    exact("jc_conserves_G", equal_matrix(U1 * G, G * U1))
    excited = sp.diag(0, 1, 0)
    rho01 = U1 * U0 * excited * U0.H * U1.H
    rho10 = U0 * U1 * excited * U1.H * U0.H
    exact("ordered_actual_CP_maps_differ", not equal_matrix(rho01, rho10),
          "Tests outputs of actual conjugation maps, not Kraus anticommutation.")
    ket_e = sp.Matrix([0, 1, 0])
    overlap = (U0 * U1 * ket_e).H * (U1 * U0 * ket_e)
    d_squared = sp.simplify(1 - sp.Abs(overlap[0]) ** 2)
    exact("ordered_actual_CP_distance_squared", d_squared == sp.Rational(576, 3125))

    # Independent B2 check derives the Bloch matrices from actual 2x2
    # conjugation maps. The basis here is |g,1>, |e,0>, in that order.
    pauli = [sp.Matrix([[0, 1], [1, 0]]), sp.Matrix([[0, -ii], [ii, 0]]),
             sp.diag(1, -1)]
    phase2 = sp.diag(1, z)
    jc2 = sp.Matrix([[sp.Rational(3, 5), -ii*sp.Rational(4, 5)],
                     [-ii*sp.Rational(4, 5), sp.Rational(3, 5)]])
    def bloch(U):
        return sp.Matrix(3, 3, lambda i, j: sp.simplify(sp.trace(pauli[i]*U*pauli[j]*U.H)/2))
    R0, R1 = bloch(phase2), bloch(jc2)
    exact("Bloch_R0_derived", equal_matrix(R0, sp.Matrix([[sp.Rational(3, 5), -sp.Rational(4, 5), 0],
                  [sp.Rational(4, 5), sp.Rational(3, 5), 0], [0, 0, 1]])))
    exact("Bloch_R1_derived", equal_matrix(R1, sp.Matrix([[1, 0, 0],
                  [0, -sp.Rational(7, 25), -sp.Rational(24, 25)],
                  [0, sp.Rational(24, 25), -sp.Rational(7, 25)]])))
    A = ((R0+R1)/2)**2
    safety = sp.Rational(81, 100)*sp.eye(3)-A.T*A
    minors = [sp.factor(safety[:k, :k].det()) for k in (1, 2, 3)]
    expected_minors = [sp.Rational(4941, 12500), sp.Rational(422733249, 3906250000),
                       sp.Rational(29552508909, 390625000000)]
    exact("two_step_contraction_principal_minors", minors == expected_minors)
    exact("two_step_contraction_strict_positive", all(m > 0 for m in minors))
    exact("uniform_two_step_bound_rational", sp.Rational(9, 10)+4*sp.Rational(1, 50) == sp.Rational(49, 50))

    # The 3-level flag has zero excitation in every level. Its preparation
    # and its readout are physical resources, not free operations.
    source_rows = []
    for q in [sp.Rational(12, 25), sp.Rational(1, 2), sp.Rational(13, 25)]:
        s = 1 - q / 2
        R01 = sp.Matrix([[sp.sqrt(1-q), -sp.sqrt(q), 0],
                         [sp.sqrt(q), sp.sqrt(1-q), 0], [0, 0, 1]])
        R0f = sp.Matrix([[sp.sqrt(s), 0, -sp.sqrt(1-s)],
                         [0, 1, 0], [sp.sqrt(1-s), 0, sp.sqrt(s)]])
        W = R01 * R0f
        suffix = str(q)
        exact("flag_preparation_unitary:" + suffix, equal_matrix(W.H * W, I))
        Us = [U0, U1, I]
        control = sp.zeros(9)
        for j, U in enumerate(Us):
            projector = sp.zeros(3)
            projector[j, j] = 1
            control += sp.kronecker_product(U, projector)
        V = control * sp.kronecker_product(I, W)
        joint_G = sp.kronecker_product(G, I)
        exact("joint_unitary:" + suffix, equal_matrix(V.H * V, sp.eye(9)))
        exact("joint_conservation:" + suffix, equal_matrix(V * joint_G, joint_G * V))
        K = [sp.Matrix(3, 3, lambda r, c: V[3*r+j, 3*c]) for j in range(3)]
        expected = [sp.sqrt(s*(1-q))*U0, sp.sqrt(s*q)*U1, sp.sqrt(1-s)*I]
        exact("instrument_derived_from_joint_unitary:" + suffix,
              all(equal_matrix(a, b) for a, b in zip(K, expected)))
        exact("source_completeness:" + suffix,
              equal_matrix(sum((k.H*k for k in K), sp.zeros(3)), I))
        # Stop on f; otherwise query the original source a second time.
        raw = {"f": K[2], "0f": K[2]*K[0], "1f": K[2]*K[1]}
        for a in range(2):
            for b in range(2):
                raw[str(a)+str(b)] = K[b]*K[a]
        exact("seven_leaf_completeness:" + suffix,
              equal_matrix(sum((k.H*k for k in raw.values()), sp.zeros(3)), I))
        H = sum((raw[h].H*raw[h] for h in ["00", "01", "10", "11"]), sp.zeros(3))
        exact("acceptance_effect_derived:" + suffix, equal_matrix(H, s*s*I))
        exact("source_failed_labels_retained:" + suffix, len(raw) == 7)
        source_rows.append({"q": str(q), "s": str(s), "acceptance": str(s*s),
                            "mean_source_calls": str(1+s), "raw_leaves": list(raw)})

    # A microscopic oscillator-vacuum collision in the one-excitation joint
    # basis |g0,0>, |e0,0>, |g1,0>, |g0,1>. The 2x2 block is an exchange.
    joint = sp.eye(4)
    c, s = sp.Rational(4, 5), sp.Rational(3, 5)
    joint[2, 2] = joint[3, 3] = c
    joint[2, 3] = joint[3, 2] = -ii*s
    exact("vacuum_exchange_joint_unitary", equal_matrix(joint.H*joint, sp.eye(4)))
    J = sp.diag(0, 1, 1, 1)
    exact("vacuum_exchange_joint_conservation", equal_matrix(joint*J, J*joint))
    L0 = sp.diag(1, 1, c)
    L1 = sp.zeros(3)
    L1[0, 2] = -ii*s
    exact("vacuum_exchange_complete", equal_matrix(L0.H*L0+L1.H*L1, I))
    exact("vacuum_exchange_readout_derived", equal_matrix(joint[:3, :3], L0)
          and equal_matrix(sp.Matrix([[joint[3, j] for j in range(3)], [0, 0, 0], [0, 0, 0]]), L1))

    swap = sp.Matrix([[1, 0, 0], [0, 0, -ii], [0, -ii, 0]])
    D0 = sp.diag(1, 1, 0)
    D1 = sp.zeros(3)
    D1[0, 2] = -ii
    after_loss = sym_channel([D0, D1], swap*excited*swap.H)
    before_loss = swap*sym_channel([D0, D1], excited)*swap.H
    exact("loss_after_JC_is_vacuum", equal_matrix(after_loss, sp.diag(1, 0, 0)))
    exact("JC_after_loss_is_oscillator_excitation", equal_matrix(before_loss, sp.diag(0, 0, 1)))
    exact("noncommuting_channel_distance_one", sp.trace(after_loss*before_loss) == 0)

    # Mean-energy preservation does not imply preservation of each cutoff.
    G3, P1 = sp.diag(0, 1, 2), sp.diag(1, 1, 0)
    energy_K = []
    for out, inp, coeff in [(0, 0, 1), (0, 1, sp.sqrt(2)/2),
                             (2, 1, sp.sqrt(2)/2), (2, 2, 1)]:
        k = sp.zeros(3)
        k[out, inp] = coeff
        energy_K.append(k)
    exact("mean_energy_control_complete", equal_matrix(sum((k.H*k for k in energy_K), sp.zeros(3)), I))
    exact("mean_energy_control_preserves_G_for_all_inputs", equal_matrix(sum((k.H*G3*k for k in energy_K), sp.zeros(3)), G3))
    escape = (I-P1)*energy_K[2]*P1
    exact("mean_energy_control_escapes_cutoff", not equal_matrix(escape, sp.zeros(3)))
    exact("naive_restriction_loses_half_mass", sp.simplify(sp.trace(P1*sym_channel(energy_K, excited)*P1)) == sp.Rational(1, 2))
    return {"source_rows": source_rows, "rational_CP_order_distance_squared": str(d_squared),
            "G1_bloch_basis": ["|g,1>", "|e,0>"],
            "G1_two_step_sylvester_minors": [str(m) for m in minors],
            "G1_uniform_two_step_contraction_bound": "49/50",
            "source_model_is_state_independent_flagging": True}


def basis(M: int) -> list[tuple[int, int]]:
    return [(0, 0)] + [(q, m-q) for m in range(1, M+1) for q in (1, 0)]


def JC(M: int, alpha: float, phase: float = 0.0) -> np.ndarray:
    bs = basis(M)
    d = len(bs)
    T = np.zeros((d, d), complex)
    index = {x: i for i, x in enumerate(bs)}
    for (q, n), i in index.items():
        if q == 0 and n:
            j = index[(1, n-1)]
            T[j, i] = np.sqrt(n)*np.exp(1j*phase)
            T[i, j] = T[j, i].conjugate()
    return expm(-1j*alpha*T)


def phase_gate(M: int, phi: float) -> np.ndarray:
    return np.diag([np.exp(-1j*phi*q) for q, n in basis(M)])


def collision(M: int, chi: float, mode: str) -> list[np.ndarray]:
    bs, index = basis(M), {x: i for i, x in enumerate(basis(M))}
    d = len(bs)
    L0, L1 = np.zeros((d, d), complex), np.zeros((d, d), complex)
    for i, (q, n) in enumerate(bs):
        m = n if mode == "oscillator" else q
        L0[i, i] = np.cos(chi*np.sqrt(m))
        if m:
            destination = (q, n-1) if mode == "oscillator" else (0, n)
            L1[index[destination], i] = -1j*np.sin(chi*np.sqrt(m))
    return [L0, L1]


def trace_distance(A: np.ndarray, B: np.ndarray) -> float:
    X = (A-B + (A-B).conj().T)/2
    return float(np.sum(np.abs(np.linalg.eigvalsh(X)))/2)


def cq_distance(A: dict, B: dict) -> float:
    assert A.keys() == B.keys()
    return sum(trace_distance(A[k], B[k]) for k in A)


def apply(K: np.ndarray, rho: np.ndarray, r: int) -> np.ndarray:
    KR = np.kron(K, np.eye(r))
    return KR@rho@KR.conj().T


def adaptive_leaves(M: int) -> dict[str, np.ndarray]:
    first = [k@JC(M, 0.47) for k in collision(M, 0.39, "oscillator")]
    second = [k@phase_gate(M, 0.71)@JC(M, 0.23, 0.34)
              for k in collision(M, 0.53, "probe")]
    return {"1:stop_click": first[1], "00:timeout": second[0]@first[0],
            "01:stop_click": second[1]@first[0]}


def floating_controls() -> dict:
    M, N, r = 3, 1, 2
    bs, small = basis(M), basis(N)
    d, dn = len(bs), len(small)
    E = np.zeros((d, dn), complex)
    for j, state in enumerate(small):
        E[bs.index(state), j] = 1
    P, ER = E@E.conj().T, np.kron(E, np.eye(r))
    psi = np.zeros(d*r, complex)
    psi[bs.index((0, 0))*r] = np.sqrt(0.75)
    psi[bs.index((0, 2))*r+1] = 0.5
    rho = np.outer(psi, psi.conj())
    PR = np.kron(P, np.eye(r))
    projected = PR@rho@PR
    success = float(np.trace(projected).real)
    rhoN = ER.conj().T@projected@ER/success
    G = np.diag([q+n for q, n in bs])
    mean = float(np.trace(np.kron(G, np.eye(r))@rho).real)
    tail_bound = mean/(N+1)
    diagcheck("tail_probability_is_one_quarter", (1-success)-0.25)
    diagcheck("projection_bound_is_saturated", trace_distance(rho, ER@rhoN@ER.conj().T)-np.sqrt(tail_bound))

    full, finite = adaptive_leaves(M), adaptive_leaves(N)
    diagcheck("adaptive_complete", float(np.max(np.abs(sum(k.conj().T@k for k in full.values())-np.eye(d)))))
    diagcheck("finite_adaptive_complete", float(np.max(np.abs(sum(k.conj().T@k for k in finite.values())-np.eye(dn)))))
    for h in full:
        diagcheck("leaf_intertwining:"+h, float(np.max(np.abs(full[h]@E-E@finite[h]))))
    omega = {h: apply(k, rho, r) for h, k in full.items()}
    omegaN = {h: ER@apply(finite[h], rhoN, r)@ER.conj().T for h in full}
    dist = cq_distance(omega, omegaN)
    if dist > np.sqrt(tail_bound)+2e-12:
        raise AssertionError("adaptive truncation bound")
    FLOAT.append({"name": "adaptive_full_CQ_truncation", "value": dist,
                  "upper_bound": float(np.sqrt(tail_bound)), "pass": True})

    q = 12/25
    s = 1-q/2
    source = [np.sqrt(s*(1-q))*phase_gate(M, -np.arctan2(4, 3)),
              np.sqrt(s*q)*JC(M, np.arctan2(4, 3)), np.sqrt(1-s)*np.eye(d)]
    words = {str(a)+str(b): source[b]@source[a]/s for a in range(2) for b in range(2)}
    target = {h: apply(k, rho, r) for h, k in words.items()}
    targetP = {h: apply(k, ER@rhoN@ER.conj().T, r) for h, k in words.items()}
    diagcheck("flagged_conditional_channel_complete", float(np.max(np.abs(sum(k.conj().T@k for k in words.values())-np.eye(d)))))
    diagcheck("flagged_conditional_truncation_saturates", cq_distance(target, targetP)-0.5)

    # Keep physical filter failure as an additional orthogonal record.
    # Equality below is a sharp control for this purified input; generic
    # mixed inputs obey <= by partial trace and channel contraction.
    filter_failure = (np.eye(d*r)-PR)@rho@(np.eye(d*r)-PR)
    actual_blocks = {"pass:"+h: success*block for h, block in targetP.items()}
    ideal_blocks = {"pass:"+h: block for h, block in target.items()}
    actual_blocks["filter_fail"] = filter_failure
    ideal_blocks["filter_fail"] = np.zeros_like(rho)
    physical_distance = cq_distance(actual_blocks, ideal_blocks)
    delta = 1-success
    sharp_prep_bound = 0.5*(np.sqrt(delta*(4-3*delta))+delta)
    diagcheck("filter_flag_bound_is_saturated", physical_distance-sharp_prep_bound)
    assert physical_distance > np.sqrt(delta)
    FLOAT.append({"name":"filter_fail_cannot_be_erased", "normalized_projection_distance":float(np.sqrt(delta)),
                  "full_physical_distance":physical_distance,"pass":True})
    dsmall = 1/4096
    return {"reference_dimension": r, "full_excitation_cutoff_for_diagnostic": M,
            "target_cutoff": N, "input_mean_excitation": mean,
            "input_filter_success": success, "adaptive_full_CQ_distance": dist,
            "normalized_projection_bound": float(np.sqrt(tail_bound)),
            "physical_filter_flag_distance": physical_distance,
            "physical_filter_sharp_bound": float(sharp_prep_bound),
            "N4095_memoryless_bound_safe": float(np.sqrt(dsmall)+dsmall+51/2500),
            "N4095_memoryless_bound_sharp": float((np.sqrt(dsmall*(4-3*dsmall))+dsmall)/2+51/2500),
            "N4095_adaptive_bound_safe": float(np.sqrt(dsmall)+dsmall+1/50),
            "N4095_adaptive_bound_sharp": float((np.sqrt(dsmall*(4-3*dsmall))+dsmall)/2+1/50)}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    symbolic = symbolic_controls()
    floating = floating_controls()
    receipt = {
        "schema": "ueot-micro-truncation-check/1",
        "completed_at_utc": datetime.now(timezone.utc).isoformat(),
        "baseline_commit": "16a89154183c22030d4526413167d095d94e6890",
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "python": platform.python_version(), "sympy": sp.__version__,
        "numpy": np.__version__, "scipy": scipy.__version__,
        "validation_kind": {"exact": "finite symbolic matrix identities",
                            "floating": "explicit finite diagnostics; not interval certificates",
                            "empirical": "none", "Lean": "not executed by this script"},
        "exact_count": len(EXACT), "floating_count": len(FLOAT),
        "exact": EXACT, "floating": FLOAT, "symbolic_summary": symbolic,
        "floating_summary": floating, "status": "PASS",
        "not_covered": ["infinite-dimensional universal quantifiers", "infinite references",
                        "unbounded stopping times", "coherent controllers", "real-device calibration",
                        "rotating-wave model discrepancy", "hardware costs"]}
    rendered = json.dumps(receipt, ensure_ascii=False, indent=2)+"\n"
    if args.output:
        args.output.write_text(rendered)
    print(json.dumps({"status": receipt["status"], "source_sha256": receipt["source_sha256"],
                      "exact_count": len(EXACT), "floating_count": len(FLOAT),
                      "floating_summary": floating}, indent=2))


if __name__ == "__main__":
    main()
