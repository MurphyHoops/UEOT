"""Finite restrictions derived from the separated sideband block actions.

This is a floating witness of the analytic growing-carrier theorem. It never
claims that exponentiating a fixed compressed Hamiltonian gives the full
oscillator process on arbitrary inputs.
"""
from __future__ import annotations

import numpy as np


def basis(cutoff: int) -> list[tuple[str, int]]:
    if not isinstance(cutoff, int) or cutoff < 0:
        raise ValueError("cutoff must be a nonnegative integer")
    return [("g", 0)] + [state for k in range(1, cutoff + 1)
                         for state in [("g", k), ("e", k - 1)]]


def embedding(source: int, target: int) -> np.ndarray:
    if target < source:
        raise ValueError("embedding must not decrease the cutoff")
    return np.eye(2 * target + 1, 2 * source + 1, dtype=complex)


def red(cutoff: int, alpha: float) -> np.ndarray:
    u = np.eye(2 * cutoff + 1, dtype=complex)
    for k in range(1, cutoff + 1):
        c, s = np.cos(alpha * np.sqrt(k)), np.sin(alpha * np.sqrt(k))
        i, j = 2 * k - 1, 2 * k
        u[i, i] = u[j, j] = c
        u[i, j] = u[j, i] = -1j * s
    return u


def phase(cutoff: int, phi: float) -> np.ndarray:
    return np.diag([np.exp(-1j * phi) if spin == "e" else 1
                    for spin, _ in basis(cutoff)])


def blue_restriction(source: int, beta: float) -> np.ndarray:
    """Exact infinite-operator columns H_source -> H_(source+2)."""
    src, dst = basis(source), basis(source + 2)
    index = {state: i for i, state in enumerate(dst)}
    b = np.zeros((len(dst), len(src)), complex)
    for j, (spin, n) in enumerate(src):
        if spin == "e" and n == 0:
            b[index[(spin, n)], j] = 1
            continue
        coupling = np.sqrt(n + 1 if spin == "g" else n)
        partner = ("e", n + 1) if spin == "g" else ("g", n - 1)
        b[index[(spin, n)], j] = np.cos(beta * coupling)
        b[index[partner], j] = -1j * np.sin(beta * coupling)
    return b


def stage_gates(source: int, phi: float, alpha: float, beta: float):
    j = embedding(source, source + 2)
    return (j @ phase(source, phi), blue_restriction(source, beta) @ red(source, alpha), j)


def ambient_gates(cutoff: int, phi: float, alpha: float, beta: float):
    """Unitary completion for the old square-matrix interpreter.

    Only columns reached before the last step are used. Unpaired upper-edge
    basis vectors are left fixed; this completion is not asserted to equal the
    oscillator blue unitary on those vectors.
    """
    states = basis(cutoff)
    index = {state: i for i, state in enumerate(states)}
    b = np.eye(len(states), dtype=complex)
    for spin, n in states:
        if spin != "g" or ("e", n + 1) not in index:
            continue
        i, j = index[("g", n)], index[("e", n + 1)]
        c, s = np.cos(beta * np.sqrt(n + 1)), np.sin(beta * np.sqrt(n + 1))
        b[i, i] = b[j, j] = c
        b[i, j] = b[j, i] = -1j * s
    return phase(cutoff, phi), b @ red(cutoff, alpha), np.eye(len(states), dtype=complex)


def rectangular_law(rho, cutoff, reference, q, phi, alpha, beta, compiled=False,
                    policy=None):
    """Full finite two-step instrument, including each stopping leaf."""
    if compiled and (policy is None or len(policy) != 3
                     or any(not 0 <= w <= 1 for w in policy)):
        raise ValueError("compiled execution requires three legal frozen visible-history weights")
    records = {}
    maximum = cutoff + 4

    def visit(state, current, history):
        if len(history) == 2 or (history and history[-1] == "f"):
            j = np.kron(embedding(current, maximum), np.eye(reference))
            records[history] = j @ state @ j.conj().T
            return
        if compiled:
            w = policy[0] if not history else policy[1 if history[0] == "0" else 2]
            masses = (1 - w, w, 0.)
        else:
            s = 1 - q / 2
            masses = (s * (1 - q), s * q, 1 - s)
        for label, mass, gate in zip(("0", "1", "f"), masses,
                                      stage_gates(current, phi, alpha, beta)):
            k = np.sqrt(mass) * np.kron(gate, np.eye(reference))
            visit(k @ state @ k.conj().T, current + 2, history + (label,))
    visit(rho, cutoff, ())
    return records
