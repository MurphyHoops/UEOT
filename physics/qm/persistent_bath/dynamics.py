"""Frozen persistent two-mode bath: independent Weyl and Galerkin backends.

Numerical functions use floating arithmetic and are diagnostics unless an explicit
external numerical enclosure is supplied.  Analytic truncation/parameter bounds
are separate functions, not inferred from matrix agreement.
"""
from __future__ import annotations

import itertools
import math
from functools import lru_cache
from typing import Iterable

import numpy as np
from scipy.linalg import expm

OMEGA = np.array([1.0, 1.5])
C = np.array([1.0, 0.6])
DEFAULT_TIMES = (2.0 / 3.0, 3.0 / 4.0, 1.0 / 2.0)
I2 = np.eye(2, dtype=complex)
X = np.array([[0, 1], [1, 0]], dtype=complex)
Y = np.array([[0, -1j], [1j, 0]], dtype=complex)
Z = np.diag([1.0, -1.0]).astype(complex)
F = np.diag(np.sqrt([1.0 / 8.0, 1.0 / 4.0])).astype(complex)
P = np.diag(np.sqrt([7.0 / 8.0, 3.0 / 4.0])).astype(complex)
PROJECTIONS = (np.diag([1, 0]).astype(complex), np.diag([0, 1]).astype(complex))


def rotation(axis: str, angle: float) -> np.ndarray:
    pauli = {"x": X, "y": Y, "z": Z}[axis.lower()]
    return math.cos(angle / 2.0) * I2 - 1j * math.sin(angle / 2.0) * pauli


def _rotations(times, rotations=None):
    n = len(times)
    if rotations is not None:
        if len(rotations) != n:
            raise ValueError("one post-pass rotation is required per slot")
        return [np.asarray(r, dtype=complex) for r in rotations]
    if n == 1:
        return [I2]
    if n == 2:
        return [rotation("y", math.pi / 2), I2]
    if n == 3:
        return [rotation("y", math.pi / 2), rotation("x", math.pi / 3), I2]
    raise ValueError("provide explicit rotations outside the frozen one/two/three-slot cases")


def bell_density() -> np.ndarray:
    v = np.array([1, 0, 0, 1], dtype=complex) / math.sqrt(2)
    return np.outer(v, v.conj())


def _input(rho_sr):
    rho = bell_density() if rho_sr is None else np.asarray(rho_sr, dtype=complex)
    if rho.ndim != 2 or rho.shape[0] != rho.shape[1] or rho.shape[0] % 2:
        raise ValueError("rho_SR must be a square matrix on S tensor finite R")
    if not np.all(np.isfinite(rho)) or not np.allclose(rho, rho.conj().T, atol=1e-12, rtol=0):
        raise ValueError("rho_SR must be finite and Hermitian")
    if abs(np.trace(rho).real - 1) > 1e-10 or np.linalg.eigvalsh(rho).min() < -1e-10:
        raise ValueError("rho_SR must be a normalized positive density matrix")
    return rho, rho.shape[0] // 2


def _configuration(times, rotations):
    ts = tuple(DEFAULT_TIMES if times is None else map(float, times))
    if not ts or any(t < 0 for t in ts):
        raise ValueError("nonempty nonnegative slot times required")
    return ts, _rotations(ts, rotations)


def cal_coherence(lam: float, t: float) -> float:
    """Vacuum coherence for a fresh |+x> probe, with no F/P instrument."""
    xi = float(lam) * C / OMEGA * np.expm1(-1j * OMEGA * float(t))
    return float(np.exp(-2 * np.vdot(xi, xi).real))


def bath_path(lam: float, times: Iterable[float], signs: Iterable[int]):
    """U_path = exp(i phase) D(beta) exp(-i H_E sum(times))."""
    times, signs = tuple(times), tuple(signs)
    if len(times) != len(signs) or any(z not in (-1, 1) for z in signs):
        raise ValueError("one sign in {-1,+1} is required for each time")
    beta = np.zeros(2, dtype=complex)
    phase = 0.0
    for t, z in zip(times, signs):
        t = float(t)
        rot = np.exp(-1j * OMEGA * t)
        xi = float(lam) * C / OMEGA * (rot - 1)
        displaced = int(z) * xi
        beta_rot = rot * beta
        phase += float(np.sum((float(lam) * C / OMEGA) ** 2 * (OMEGA * t - np.sin(OMEGA * t))))
        phase += float(np.imag(np.vdot(beta_rot, displaced)))
        beta = beta_rot + displaced
    return beta, phase


def gaussian_influence(beta, phase, beta_prime, phase_prime, total_time,
                       mean=None, covariance=None):
    """Exact finite-mode Gaussian *initial-state* history-pair factor.

    This does not assume Gaussian conditional baths after interventions.  This
    generalized formula is outside the executed frozen-vacuum certificate.
    Quadratures are (q1,p1,q2,p2), with [q,p]=i.
    """
    d = np.zeros(4) if mean is None else np.asarray(mean, dtype=float)
    v = np.eye(4) / 2 if covariance is None else np.asarray(covariance, dtype=float)
    if d.shape != (4,) or v.shape != (4, 4):
        raise ValueError("two-mode Gaussian mean/covariance dimensions are 4 and 4x4")
    symplectic = np.zeros((4, 4))
    for k, w in enumerate(OMEGA):
        co, si = math.cos(w * total_time), math.sin(w * total_time)
        symplectic[2*k:2*k+2, 2*k:2*k+2] = [[co, si], [-si, co]]
    d_rot = symplectic @ d
    v_rot = symplectic @ v @ symplectic.T
    delta = np.asarray(beta) - np.asarray(beta_prime)
    xi = np.array([math.sqrt(2)*delta[0].imag, -math.sqrt(2)*delta[0].real,
                   math.sqrt(2)*delta[1].imag, -math.sqrt(2)*delta[1].real])
    weyl_phase = np.imag(np.vdot(beta_prime, beta))
    return np.exp(1j * (phase - phase_prime + weyl_phase + xi @ d_rot)
                  - 0.5 * xi @ v_rot @ xi)


def _history_operators(lam, times, kraus):
    out = []
    for indices in itertools.product((0, 1), repeat=len(times)):
        op = I2.copy()
        for k, zindex in enumerate(indices):
            op = kraus[k] @ PROJECTIONS[zindex] @ op
        beta, phase = bath_path(lam, times, [1 if z == 0 else -1 for z in indices])
        out.append((op, beta, phase))
    return out


def exact_output(lam: float, times=None, rho_sr=None, rotations=None,
                 *, omit_history_phase=False) -> dict[str, np.ndarray]:
    """Infinite-bath Weyl answer for all terminal records, before readout.

    The output blocks are unnormalized and include fail branches and finite R.
    omit_history_phase is an intentionally incorrect negative-control switch.
    """
    ts, rs = _configuration(times, rotations)
    rho, rdim = _input(rho_sr)
    result = {}
    for stop in range(len(ts) + 1):
        if stop < len(ts):
            count = stop + 1
            label = "p" * stop + "f"
            ks = [rs[j] @ P for j in range(stop)] + [F]
        else:
            count = len(ts)
            label = "p" * count
            ks = [rs[j] @ P for j in range(count)]
        histories = _history_operators(lam, ts[:count], ks)
        block = np.zeros_like(rho, dtype=complex)
        for op, beta, phase in histories:
            left = np.kron(op, np.eye(rdim))
            for opp, betap, phasep in histories:
                right = np.kron(opp, np.eye(rdim))
                ph = 0.0 if omit_history_phase else phase - phasep
                influence = np.exp(1j * ph - 0.5 * (np.vdot(beta, beta).real + np.vdot(betap, betap).real)
                                   + np.vdot(betap, beta))
                block += influence * (left @ rho @ right.conj().T)
        result[label] = (block + block.conj().T) / 2
    return result


@lru_cache(maxsize=256)
def _mode_propagators(lam: float, t: float, cutoff: int):
    n = cutoff + 1
    annihilation = np.diag(np.sqrt(np.arange(1, n)), 1).astype(complex)
    number = np.diag(np.arange(n)).astype(complex)
    plus, minus = [], []
    for w, c in zip(OMEGA, C):
        plus.append(expm(-1j * t * (w * number + lam * c * (annihilation + annihilation.conj().T))))
        minus.append(expm(-1j * t * (w * number - lam * c * (annihilation + annihilation.conj().T))))
    return (np.kron(plus[0], plus[1]), np.kron(minus[0], minus[1]))


def _apply_s(op, v):
    return np.einsum('ij,jre->ire', op, v, optimize=True)


def _sr_reduce(v):
    matrix = v.reshape(v.shape[0] * v.shape[1], v.shape[2])
    return matrix @ matrix.conj().T


def galerkin_output(lam: float, times=None, rho_sr=None, rotations=None,
                    *, cutoff=12) -> dict[str, np.ndarray]:
    """Actual P_K H P_K evolution, independent of the Weyl formula."""
    if not isinstance(cutoff, (int, np.integer)) or cutoff < 0:
        raise ValueError("cutoff must be a nonnegative integer")
    ts, rs = _configuration(times, rotations)
    rho, rdim = _input(rho_sr)
    evals, evecs = np.linalg.eigh((rho + rho.conj().T) / 2)
    labels = ["p" * j + "f" for j in range(len(ts))] + ["p" * len(ts)]
    out = {label: np.zeros_like(rho, dtype=complex) for label in labels}
    edim = (cutoff + 1) ** 2
    for value, eigenvector in zip(evals, evecs.T):
        if value <= 0:
            continue
        v = np.zeros((2, rdim, edim), dtype=complex)
        v[:, :, 0] = math.sqrt(float(value)) * eigenvector.reshape(2, rdim)
        for j, t in enumerate(ts):
            propagators = _mode_propagators(float(lam), float(t), cutoff)
            for zindex in (0, 1):
                v[zindex] = v[zindex] @ propagators[zindex].T
            failed = _apply_s(F, v)
            out['p' * j + 'f'] += _sr_reduce(failed)
            v = _apply_s(rs[j] @ P, v)
        out['p' * len(ts)] += _sr_reduce(v)
    return out


def reset_bath_output(lam: float, times=None, rho_sr=None, rotations=None):
    """Wrong memory model, retained only as a declared negative control."""
    ts, rs = _configuration(times, rotations)
    rho, rdim = _input(rho_sr)
    active = rho.copy()
    out = {}
    for j, t in enumerate(ts):
        shaped = active.reshape(2, rdim, 2, rdim).copy()
        coherence = cal_coherence(lam, t)
        shaped[0, :, 1, :] *= coherence
        shaped[1, :, 0, :] *= coherence
        active = shaped.reshape(2 * rdim, 2 * rdim)
        fail_op, pass_op = np.kron(F, np.eye(rdim)), np.kron(rs[j] @ P, np.eye(rdim))
        out['p' * j + 'f'] = fail_op @ active @ fail_op.conj().T
        active = pass_op @ active @ pass_op.conj().T
    out['p' * len(ts)] = active
    return out


def cq_distance(left, right):
    if set(left) != set(right):
        raise ValueError("full terminal record sets differ")
    return float(sum(np.sum(np.abs(np.linalg.eigvalsh((left[k]-right[k] + (left[k]-right[k]).conj().T)/2)))
                     for k in left) / 2)


def acceptance_effect(lam: float, times=None, rotations=None):
    """Reconstruct the accepted effect from the same exact source, R trivial."""
    ts, _ = _configuration(times, rotations)
    label = 'p' * len(ts)
    states = [np.array([[1,0],[0,0]],complex), np.array([[0,0],[0,1]],complex),
              np.array([[.5,.5],[.5,.5]],complex), np.array([[.5,-.5j],[.5j,.5]],complex)]
    probs = [np.trace(exact_output(lam, times=ts, rotations=rotations, rho_sr=rho)[label]).real for rho in states]
    a, b = probs[:2]
    re = probs[2] - (a+b)/2
    im = (a+b)/2 - probs[3]
    return np.array([[a,re+1j*im],[re-1j*im,b]],complex)


def truncation_bound(cutoff: int, lam_max=0.4, total_time=sum(DEFAULT_TIMES)):
    """Floating display of the proven finite-Duhamel bound, not enclosure.

    For the product cutoff n1,n2<=K, the total-number subspaces N<=K
    suffice to match the first K interaction orders. This conservative bound
    is uniform over finite R and arbitrary S-only complete controls/stops.
    """
    if not isinstance(cutoff, (int, np.integer)) or cutoff < 0:
        raise ValueError("cutoff must be a nonnegative integer")
    if lam_max < 0 or total_time < 0:
        raise ValueError("nonnegative exposure parameters required")
    j = int(cutoff) + 1
    x = abs(float(lam_max)) * float(total_time) * float(np.linalg.norm(C))
    coeff = x ** j / math.factorial(j)
    for k in range(1, j + 1):
        coeff *= math.sqrt(k - 1) + math.sqrt(k)
    return min(1.0, 2.0 * coeff)


def parameter_error_bound(lam, lam_hat):
    if not (0.2 <= lam <= 0.4 and 0.2 <= lam_hat <= 0.4):
        raise ValueError("parameter bound is certified only on [1/5,2/5]")
    return min(1.0, 5.1 * abs(float(lam) - float(lam_hat)))


def source_energy_bound(t, lam_max=0.4):
    """Uniform full-record mean total bath occupation, initially vacuum.

    Stopped branches may evolve freely until the common horizon. This is an
    unconditional statement; normalized rare branches need their own bound.
    """
    if t < 0 or lam_max < 0:
        raise ValueError("nonnegative time and coupling required")
    return float((lam_max * np.linalg.norm(C) * t) ** 2)


def sharp_parameter_lipschitz_display(lam_max=0.4, total_time=sum(DEFAULT_TIMES)):
    """Floating display of gamma*T+lam_max*gamma^2*T^2, bounded by 51/10."""
    gamma = float(np.linalg.norm(C))
    return gamma * total_time + lam_max * gamma * gamma * total_time * total_time


def apply_stored_choi(choi_blocks, rho_sr):
    """Apply a stored normalized-Choi representation; local arithmetic is floating.

    A certificate for the stored matrices defines a linear map in exact
    arithmetic. This convenience contraction introduces further floating
    roundoff and is not independently enclosed by that certificate.
    """
    rho, rdim = _input(rho_sr)
    blocks = {}
    rho4 = rho.reshape(2, rdim, 2, rdim)
    for label, choi in choi_blocks.items():
        j = np.asarray(choi).reshape(2, 2, 2, 2)
        out = 2 * np.einsum('aibj,irjs->arbs', j, rho4, optimize=True)
        blocks[label] = out.reshape(2 * rdim, 2 * rdim)
    return blocks


def conditional_bath_fourth_cumulant(lam: float, t=DEFAULT_TIMES[0]):
    """Exact fourth cumulant in the actual first-pass bath marginal.

    Bell input gives weights7/13,6/13 for the opposite coherent branches;
    use the mode1 quadrature aligned with its displacement. A Gaussian state
    has zero fourth cumulant, so a nonzero value rejects single-Gaussian closure.
    """
    beta, _ = bath_path(lam, [t], [1])
    mu = math.sqrt(2) * abs(beta[0])
    m = 1.0 / 13.0
    return float(mu ** 4 * (-2.0 + 8.0 * m*m - 6.0 * m**4))
