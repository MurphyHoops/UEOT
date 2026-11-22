"""Compare the B snapshot with independently time-ordered interaction-picture displacements."""
import hashlib
import itertools
import json
import os
import subprocess
import sys
from pathlib import Path

import numpy as np
from scipy.linalg import expm

root = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(root / "dynamics"))
import correlated_cq as candidate
from fock import galerkin_blocks

from fractions import Fraction

pin = "44b6cd200cd01eccf15d4dc817311388d317a1af"


def upstream_repo():
    override = os.environ.get("UEOT_UPSTREAM_REPO")
    paths = [Path(override).expanduser()] if override else [root, Path.home() / "Documents" / "ueotlean"]
    for path in paths:
        if subprocess.run(["git", "-C", path, "cat-file", "-e", pin + "^{commit}"],
                          stderr=subprocess.DEVNULL).returncode == 0:
            return path.resolve()
    raise SystemExit(f"Set UEOT_UPSTREAM_REPO to a Git checkout containing {pin}.")


repo = upstream_repo()


def pinned_blob(name):
    return subprocess.check_output(["git", "-C", repo, "show",
                                    f"{pin}:physics/qm/persistent_bath/{name}"])


spec_bytes = pinned_blob("SHARED_MODEL.json")
spec = json.loads(spec_bytes)
omega, coupling, deployment, fail_sq, pass_sq = [
    np.array([float(Fraction(s)) for s in spec[key]])
    for key in ("omega", "relative_couplings", "slot_durations",
                "failure_Kraus_squared", "pass_Kraus_squared")
]
x = np.array([[0, 1], [1, 0]])
y = np.array([[0, -1j], [1j, 0]])
eye = np.eye(2)
rotations = (expm(-1j*np.pi*y/4), expm(-1j*np.pi*x/6), eye)
assert spec["post_pass_unitaries"] == ["Ry(pi/2)", "Rx(pi/3)", "I"]


def kicks(signs, times, lam):
    ends = np.cumsum(times)
    starts = ends - times
    # Each row is a displacement in the interaction picture at shot time zero.
    delta = (np.exp(1j*np.outer(starts, omega)) - np.exp(1j*np.outer(ends, omega)))
    return lam * np.asarray(signs)[:, None] * (coupling/omega) * delta


def influence(left, right, times, lam, n, c, *, exchange=True):
    a, b = (kicks(hist, times, lam) for hist in (left, right))
    # Trace D_right^dagger D_left, with later Weyl factors on the left.
    chronological = np.concatenate((-b, a[::-1]))
    phase = sum(np.vdot(v, u).imag for i, u in enumerate(chronological)
                for v in chronological[i+1:])
    diff = chronological.sum(axis=0)
    metric = np.array([[n+.5, c], [c, n+.5]])
    return np.exp(1j*(phase if exchange else 0) - np.vdot(diff, metric @ diff).real)


def blocks(rho, times, lam, n, c, *, exchange=True):
    ref = np.eye(len(rho)//2)
    result = {}
    for record in spec["records"]:
        histories = list(itertools.product((1, -1), repeat=len(record)))
        operators = []
        for hist in histories:
            op = eye
            for slot, (label, sign) in enumerate(zip(record, hist)):
                index = (1-sign)//2
                projection = np.outer(eye[index], eye[index])
                action = (np.diag(np.sqrt(fail_sq)) if label == "f" else
                          rotations[slot] @ np.diag(np.sqrt(pass_sq)))
                op = action @ projection @ op
            operators.append(np.kron(op, ref))
        block = np.zeros_like(rho, dtype=complex)
        for i, h in enumerate(histories):
            for j, k in enumerate(histories):
                block += influence(h, k, times[:len(record)], lam, n, c,
                                   exchange=exchange) * operators[i] @ rho @ operators[j].conj().T
        result[record] = block
    return result


def distance(a, b):
    return .5 * sum(np.linalg.svd(a[key]-b[key], compute_uv=False).sum() for key in a)


def main():
    for name in ("correlated_cq.py", "fock.py"):
        print(name, hashlib.sha256((root / "dynamics" / name).read_bytes()).hexdigest())
    a, b = deployment[:2]
    f = 4*np.sum((coupling/omega)**2 *
                 (np.sin(omega*a)+np.sin(omega*b)-np.sin(omega*(a+b))))
    print(f"signed-response coefficient F = {f:.12f}")
    for lam, n, c in ((.3, .5, .25), (1/3, .31, 81/400)):
        for s in (1, -1):
            z = influence((s, 1), (s, -1), (a, b), lam, n, c)
            assert abs(np.angle(z) - s*lam**2*f) < 1e-12
            print(f"lambda={lam:.9f} first={s:+d} arg(2rho01)={np.angle(z):+.10f}"
                  f" Y={-.96*z.imag:+.10f}")
        reset = influence((1,), (-1,), (b,), lam, n, c)
        assert abs(reset.imag) < 1e-14
        print(f"fresh centered bath Y={-.96*reset.imag:.10f}")
    # Complex entangled S x R with dim R=3 and a mixed component.
    psi = np.array([1, 0, 1j, 0, 2, -1j])
    rho = .8 * np.outer(psi, psi.conj()) / np.vdot(psi, psi) + .2*np.eye(6)/6
    for timing, times, n, c in (("deployment", deployment, .5, .25),
                               ("changed_intervals", deployment[[1, 0, 2]], .2, -.2)):
        expected = blocks(rho, times, .3, n, c)
        actual = candidate.exact_blocks(.3, n, c, timing, rho)
        assert list(actual) == spec["records"]
        assert abs(sum(np.trace(v) for v in actual.values())-1) < 1e-12
        assert min(np.linalg.eigvalsh(v)[0] for v in actual.values()) >= -1e-12
        error = distance(actual, expected)
        ablated = distance(actual, blocks(rho, times, .3, n, c, exchange=False))
        print(f"{timing}, R=3 full CQ distance={error:.3g}, omit all Weyl phases={ablated:.9g}")
        assert error < 2e-12 and ablated > .001
    # A low-occupation interior point also checks the sign/order against a Hamiltonian solver.
    rho = np.outer(psi, psi.conj()) / np.vdot(psi, psi)
    expected = blocks(rho, deployment, .3, .12, -.08)
    errors = [distance(expected, galerkin_blocks(.3, .12, -.08, k, rho_sr=rho)) for k in (4, 8)]
    print("direct Fock half-CQ errors K=4,8:", *[f"{e:.10g}" for e in errors])
    assert errors[1] < errors[0] and errors[1] < 1e-5


if __name__ == "__main__":
    main()
