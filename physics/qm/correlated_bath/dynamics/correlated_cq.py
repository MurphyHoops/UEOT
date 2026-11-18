"""Fixed persistent two-mode instrument. Public numbers are in floating arithmetic.

exact_blocks and event_probabilities default to a normalized Bell input on S,R.
The covariance N of the initial, phase-locked bath is [[n,c],[c,n]].
The original terminal tester puts S first, then R, and reports minus before plus.
"""
from functools import lru_cache
from itertools import product

import numpy as np

TIMES = {"deployment": (2/3, 3/4, 1/2), "changed_intervals": (3/4, 2/3, 1/2)}
RECORDS = ("f", "pf", "ppf", "ppp")
OBSERVABLES = ("XX", "XY", "YZ", "ZZ")
PAULI = {"I": np.eye(2), "X": np.array([[0, 1], [1, 0]]),
         "Y": np.array([[0, -1j], [1j, 0]]), "Z": np.diag([1, -1])}
OMEGA = np.array([1., 1.5])
G = np.array([1., .6])
FAIL = np.diag(np.sqrt([1/8, 1/4]))
PASS = np.diag(np.sqrt([7/8, 3/4]))
PASS_OPS = (np.array([[1., -1.], [1., 1.]]) @ PASS / np.sqrt(2),
            (np.sqrt(3)*PAULI["I"] - 1j*PAULI["X"]) @ PASS / 2, PASS)


def parameters(lam, n, c, timing):
    if timing not in TIMES:
        raise ValueError("timing must be deployment or changed_intervals")
    if not (.2 <= lam <= .4 and 0 <= n <= .6 and abs(c) <= n):
        raise ValueError("expected .2 <= lam <= .4, |c| <= n <= .6")


def input_state(rho_sr):
    if rho_sr is None:
        bell = np.array([1, 0, 0, 1])
        return np.outer(bell, bell)/2
    rho = np.asarray(rho_sr, dtype=complex)
    if (rho.ndim != 2 or rho.shape[0] != rho.shape[1] or
            not rho.shape[0] or rho.shape[0] % 2 or not np.isfinite(rho).all()):
        raise ValueError("expected a finite square matrix on S tensor R")
    if (np.max(np.abs(rho-rho.conj().T)) > 1e-12 or
            abs(np.trace(rho)-1) > 1e-12 or np.linalg.eigvalsh(rho)[0] < -1e-12):
        raise ValueError("expected a normalized positive Hermitian SR input")
    return rho


@lru_cache(maxsize=2)
def _histories(timing):
    """Store unit-lambda coefficients, rotating the displacement back to shot time zero."""
    result = {}
    for record in RECORDS:
        times = TIMES[timing][:len(record)]
        ops, betas, phases = [], [], []
        for history in product((0, 1), repeat=len(record)):
            a = np.eye(2)
            beta = np.zeros(2, complex)
            phase = 0.
            for j, (index, t) in enumerate(zip(history, times)):
                rotate = np.exp(-1j*OMEGA*t)
                xi = (1-2*index)*G/OMEGA*(rotate-1)
                previous = rotate*beta
                # The scalar forced-oscillator phase is common to both histories.
                phase += np.vdot(previous, xi).imag
                beta = previous + xi
                kraus = FAIL if record[j] == "f" else PASS_OPS[j]
                a = kraus[:, index:index+1] @ a[index:index+1, :]
            ops.append(a)
            betas.append(beta)
            phases.append(phase)
        b, p = np.array(betas), np.array(phases)
        delta = (b[:, None, :]-b[None, :, :])*np.exp(1j*OMEGA*sum(times))
        square = np.sum(abs(delta)**2, axis=-1)
        cross = 2*(delta[..., 0].conj()*delta[..., 1]).real
        phase = p[:, None]-p[None, :] + (b @ b.conj().T).imag
        result[record] = (np.array(ops), square, cross, phase)
    return result


def exact_blocks(lam, n, c, timing="deployment", rho_sr=None):
    """Evaluate the infinite-bath formula for all unnormalized terminal SR blocks."""
    parameters(lam, n, c, timing)
    rho = input_state(rho_sr)
    r = len(rho)//2
    output = {}
    for record, (ops, square, cross, phase) in _histories(timing).items():
        influence = np.exp(lam**2*(1j*phase - (n+.5)*square - c*cross))
        kernel = np.einsum("hai,hk,kbj->aibj", ops, influence, ops.conj(), optimize=True)
        block = np.einsum("aibj,irjs->arbs", kernel, rho.reshape(2, r, 2, r))
        output[record] = block.reshape(rho.shape)
    return output


def events_from_blocks(blocks, eta, name):
    """Eight joint probabilities for a Pauli product on two qubits, S first."""
    if not .9 <= eta <= 1:
        raise ValueError("expected .9 <= eta <= 1")
    if len(name) != 2 or any(axis not in PAULI for axis in name):
        raise ValueError("expected a two-letter Pauli product")
    obs = np.kron(PAULI[name[0]], PAULI[name[1]])
    events = []
    for record in RECORDS:
        b = blocks[record]
        if b.shape != (4, 4):
            raise ValueError("this terminal tester uses a qubit reference")
        weight, moment = np.trace(b).real, np.trace(obs @ b).real
        events.extend(((weight-eta*moment)/2, (weight+eta*moment)/2))
    return np.array(events)


def event_probabilities(lam, n, c, eta, name, timing="deployment", rho_sr=None):
    """Return f-,f+,pf-,pf+,ppf-,ppf+,ppp-,ppp+ for a fixed binary tester."""
    return events_from_blocks(exact_blocks(lam, n, c, timing, rho_sr), eta, name)
