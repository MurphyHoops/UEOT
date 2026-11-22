"""Check the linear defect obtained by measuring and retaining both reset flags."""
from fractions import Fraction
import math

import numpy as np
from mpmath import iv


def trace_distance(a, b):
    return np.abs(np.linalg.eigvalsh(a-b)).sum()/2


ground = np.eye(9)[0]
bell = (np.eye(9)[4]+np.eye(9)[8])/np.sqrt(2)
G, B = np.outer(ground, ground), np.outer(bell, bell)
P = np.diag([1, 0, 0])
Q = np.eye(3)-P
bad_projector = np.kron(Q,Q)
# On bad flags every real product state has Bell fidelity <=1/2. Shared classical labels preserve this.
witness = 2*B-bad_projector
assert np.max(np.abs(np.linalg.eigvalsh(witness))) <= 1+1e-15
for p in (1e-6, 0.02, 0.25):
    psi = np.sqrt(1-p)*ground + np.sqrt(p)*bell
    state = np.outer(psi, psi)
    blocks = []
    for l in (P,Q):
        for r in (P,Q):
            proj = np.kron(l,r)
            blocks.append(proj@state@proj)
    assert np.isclose(trace_distance(state,G), np.sqrt(p), rtol=1e-12, atol=1e-15)
    # The flagged E1 comparison uses the same joint flag distribution and locally fresh grounds.
    replacement = [np.trace(block)*G for block in blocks]
    distance = sum(trace_distance(orig, product) for orig, product in zip(blocks,replacement))
    assert abs(distance-p) < 1e-14 and abs(np.trace(witness@blocks[-1])-p)<1e-14
    assert abs(sum(np.trace(block) for block in blocks)-1)<1e-14

# One-sided all-start affine bound for a distinct IID calibration of the joint bad flag only.
iv.dps = 45
q = Fraction(4,10**8)
n = math.ceil(math.log(0.05)/math.log1p(-float(q)))
good = 1-iv.mpf(q.numerator)/q.denominator
alpha = iv.mpf(1)/20
assert good**n <= alpha and good**(n-1) > alpha
print(f"PASS: flagged distance p, real-separable lower bound p/2; zero bad flags at N={n} for upper 4e-8 (95%)")
