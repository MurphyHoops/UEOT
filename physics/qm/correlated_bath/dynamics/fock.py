"""Independent Schrodinger-picture Galerkin method on n1+n2 <= K.

No displacement, Gaussian influence functional or history sum enters this solver.
Only the frozen clock, qubit instrument, input checks and parameter domain are
shared with correlated_cq. Numerical outputs are floating diagnostics.
"""
from math import sqrt, comb, factorial, isqrt
from fractions import Fraction as Q

import numpy as np
from scipy.linalg import eigh_tridiagonal
from scipy.sparse import coo_matrix, diags
from scipy.sparse.linalg import expm_multiply

from correlated_cq import FAIL, PASS_OPS, RECORDS, TIMES, input_state, parameters


def _check_cutoff(k):
    if isinstance(k, bool) or not isinstance(k, (int, np.integer)) or k < 0:
        raise ValueError("K must be a nonnegative integer")
    return int(k)


def _start(s):
    return s*(s+1)//2


def _hamiltonians(k, lam):
    """Basis row start(s)+i is |i,s-i> in the physical frequency basis."""
    energy, rows, cols, values = [], [], [], []
    for s in range(k+1):
        for i in range(s+1):
            energy.append(i + 1.5*(s-i))
            if s < k:
                rows.extend((_start(s+1)+i+1, _start(s+1)+i))
                cols.extend([_start(s)+i]*2)
                values.extend((lam*sqrt(i+1), .6*lam*sqrt(s-i+1)))
    d = len(energy)
    up = coo_matrix((values, (rows, cols)), shape=(d, d)).tocsr()
    free, drive = diags(energy, format="csr"), up+up.T
    return free+drive, free-drive


def _thermal_factor(k, n, c):
    """Columns factor the normalized projected state, retaining within-shell coherence."""
    d = _start(k+1)
    r_plus, r_minus = ((n+sign*c)/(1+n+sign*c) for sign in (1, -1))
    pieces, weights = [], []
    for s in range(k+1):
        h = np.arange(s+1)
        w = (1-r_plus)*(1-r_minus)*r_plus**h*r_minus**(s-h)
        nonzero = w > 0
        if not np.any(nonzero):
            continue
        # Xmix = a1† a2 + a2† a1 = N_plus - N_minus. Ordered eigenvalue 2h-s.
        offdiag = np.sqrt(np.arange(1, s+1)*np.arange(s, 0, -1))
        _, modes = eigh_tridiagonal(np.zeros(s+1), offdiag)
        col = np.zeros((d, np.count_nonzero(nonzero)))
        col[_start(s):_start(s+1)] = modes[:, nonzero]*np.sqrt(w[nonzero])
        pieces.append(col)
        weights.extend(w[nonzero])
    return np.hstack(pieces)/sqrt(sum(weights))


def _reduce(v):
    # (S,R,E,bath-purification) -> SR density block by a single partial trace.
    z = v.reshape(v.shape[0]*v.shape[1], -1)
    return z @ z.conj().T


def galerkin_blocks(lam, n, c, cutoff, timing="deployment", rho_sr=None):
    """Run the actual finite source, mixed inputs allowed, reference retained."""
    parameters(lam, n, c, timing)
    k = _check_cutoff(cutoff)
    rho = input_state(rho_sr)
    r = len(rho)//2
    hams = _hamiltonians(k, lam)
    factor = _thermal_factor(k, n, c)
    d, rank = factor.shape
    result = {label: np.zeros(rho.shape, complex) for label in RECORDS}
    eig, vectors = np.linalg.eigh(rho)
    for weight, vector in zip(eig, vectors.T):
        if weight <= 0:
            continue
        v = sqrt(weight)*vector.reshape(2, r, 1, 1)*factor
        for j, t in enumerate(TIMES[timing]):
            evolved = np.empty(v.shape, complex)
            for z, h in enumerate(hams):
                rhs = v[z].transpose(1, 0, 2).reshape(d, r*rank)
                out = expm_multiply((-1j*t)*h, rhs)
                evolved[z] = out.reshape(d, r, rank).transpose(1, 0, 2)
            result[RECORDS[j]] += _reduce(FAIL.diagonal()[:, None, None, None]*evolved)
            v = (PASS_OPS[j] @ evolved.reshape(2, -1)).reshape(evolved.shape)
        result["ppp"] += _reduce(v)
    return result


def thermal_tail(n, c, k):
    """Exact probability N_total > k for rational inputs, including rank-one endpoints."""
    k = _check_cutoff(k)
    n, c = Q(str(n)), Q(str(c))
    if not 0 <= abs(c) <= n <= Q(3, 5):
        raise ValueError("expected |c| <= n <= 3/5")
    a, b = (p/(1+p) for p in (n+c, n-c))
    # Sum over first mode i<=k with second mode >=k+1-i, or first mode >k.
    return a**(k+1) + (1-a)*sum(a**i*b**(k+1-i) for i in range(k+1))


def _flux(k, s):
    """Rational upper bound on integrated Galerkin boundary flux from shell s."""
    d = k-s
    x = Q(9, 10)  # >= (2/5)(23/12)*sqrt(34/25), both timings
    ratio = factorial(k+1)//factorial(s)
    scale = 10**12
    root = Q(isqrt(ratio*scale**2)+1, scale)
    series = sum(Q(comb(s, j), factorial(d+j)*(d+2*j+1))*x**(2*j)
                 for j in range(s+1))
    return min(Q(1), root*x**(d+1)*series/(1-x*x/2))


def uniform_bound(cutoff):
    """Exact rational, all inputs, all allowed parameters, half-trace CQ distance."""
    k = _check_cutoff(cutoff)
    a, b = Q(6, 11), Q(3, 8)  # stochastic dominators of sorted thermal occupancies
    bound, running = Q(1), Q(0)
    for s in range(k+1):
        mass = (1-a)*(1-b)*sum(a**h*b**(s-h) for h in range(s+1))
        running = max(running, _flux(k, s))
        bound -= mass*(1-running)
    return bound
