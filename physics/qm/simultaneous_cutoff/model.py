"""Actual finite Galerkin generators and complete two-slot output.

Compression is performed on H before exponentiation. These gates predict the
specified infinite model to the separately proved error; they are not assumed
to be available physical actions or exact invariant restrictions.
"""
from __future__ import annotations

import math
from fractions import Fraction
import numpy as np
from scipy.linalg import expm

RECORDS = ("f", "0f", "1f", "00", "01", "10", "11")
Q = {"00": Fraction(313, 1250), "01": Fraction(312, 1250),
     "10": Fraction(312, 1250), "11": Fraction(313, 1250)}


def basis(cutoff):
    if not isinstance(cutoff, int) or cutoff < 0:
        raise ValueError("cutoff must be a nonnegative integer")
    return [("g", 0)] + [s for k in range(1, cutoff + 1)
                           for s in (("g", k), ("e", k - 1))]


def embedding(source, target, reference=1):
    if target < source or reference < 1:
        raise ValueError("invalid common carrier")
    return np.kron(np.eye(2 * target + 1, 2 * source + 1), np.eye(reference))


def hamiltonian(cutoff, omega=0., delta=0., g=0., h=0.):
    states = basis(cutoff)
    index = {s: i for i, s in enumerate(states)}
    a = np.zeros((len(states), len(states)), complex)
    for j, (spin, n) in enumerate(states):
        a[j, j] = omega*n + delta*(spin == "e")
        if spin == "g":
            for partner, coupling in [(("e", n-1), g*np.sqrt(n)),
                                      (("e", n+1), h*np.sqrt(n+1))]:
                if partner in index:
                    i = index[partner]
                    a[i, j] = a[j, i] = coupling
    return a


def gates(cutoff, x, phi=np.pi/3):
    v0 = np.diag([np.exp(-1j*phi) if spin == "e" else 1
                  for spin, _ in basis(cutoff)])
    return v0, expm(-1j*hamiltonian(cutoff, g=x, h=x))


def raw_weights(q):
    s = 1-q/2
    return {"f": 1-s, "0f": s*(1-q)*(1-s), "1f": s*q*(1-s),
            "00": s*s*(1-q)**2, "01": s*s*q*(1-q),
            "10": s*s*q*(1-q), "11": s*s*q*q}


def law(rho, cutoff, reference, q, x, compiled=False, normalized_target=False):
    if compiled and normalized_target:
        raise ValueError("compiler and source target are different objects")
    vv = gates(cutoff, x)
    vv = [np.kron(v, np.eye(reference)) for v in vv]
    weights = {r: float(Q.get(r, 0)) for r in RECORDS} if compiled else raw_weights(q)
    if normalized_target:
        s = 1-q/2
        weights = {r: w/(s*s) if "f" not in r else 0 for r, w in weights.items()}
    out = {}
    for r in RECORDS:
        state = rho
        for letter in r:
            if letter in "01":
                v = vv[int(letter)]
                state = v @ state @ v.conj().T
        out[tuple(r)] = weights[r]*state
    return out


def remainder_squared(n, l, exposure):
    """Square of 2*c_(L+1), exactly rational; no sampled infinite tail."""
    x = Fraction(exposure)
    j = l+1
    product = math.prod(n+2*k-1 for k in range(1, j+1))
    return 4*x**(2*j)*product / math.factorial(j)**2


def remainder_float(n, l, exposure):
    return min(1., math.sqrt(float(remainder_squared(n, l, exposure))))
