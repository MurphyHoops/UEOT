"""Exact finite rational calculation only; no Lean, tests, or repository writes."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json

OUT = Path(__file__).resolve().parent / "RATIONAL_COUNTEREXAMPLE.json"
assert not OUT.exists(), "Preserve an already recorded calculation"

L = [[F(3, 8), F(3, 8), F(1, 4)],
     [F(1, 8), F(1, 8), F(3, 4)],
     [F(0), F(0), F(1)]]
p0 = [F(1, 2), F(1, 2), F(0)]
Q = [row[:2] for row in L[:2]]
r = p0[:2]
h = [F(3), F(1)]
rho = F(1, 2)

def row_apply(v, matrix):
    return [sum((v[i] * matrix[i][j] for i in range(len(v))), F(0))
            for j in range(len(matrix[0]))]

def col_apply(matrix, v):
    return [sum((x * y for x, y in zip(row, v)), F(0)) for row in matrix]

def multiply(a, b):
    return [[sum((a[i][k] * b[k][j] for k in range(len(b))), F(0))
             for j in range(len(b[0]))] for i in range(len(a))]

def tv(a, b):
    return sum((abs(x - y) for x, y in zip(a, b)), F(0)) / 2

assert all(sum(row) == 1 and all(x >= 0 for x in row) for row in L)
assert sum(p0) == 1
assert row_apply(r, Q) == [rho * x for x in r]
assert col_apply(Q, h) == [rho * x for x in h]
assert multiply(Q, Q) == [[rho * x for x in row] for row in Q]

pairing = sum((x * y for x, y in zip(r, h)), F(0))
tilted = [r[i] * h[i] / pairing for i in range(2)]
R = [[Q[i][j] * h[j] / (rho * h[i]) for j in range(2)] for i in range(2)]
assert R == [[F(3, 4), F(1, 4)]] * 2
assert row_apply(tilted, R) == tilted
unconditional_joint = [[p0[i] * L[i][j] for j in range(3)] for i in range(3)]
safe_joint = [row[:2] for row in unconditional_joint[:2]]
survival = sum(sum(row) for row in safe_joint)
conditioned = [[x / survival for x in row] for row in safe_joint]
conditioned_initial = [sum(row) for row in conditioned]
conditioned_terminal = [sum(conditioned[i][j] for i in range(2)) for j in range(2)]
doob_r = [[r[i] * R[i][j] for j in range(2)] for i in range(2)]
doob_tilted = [[tilted[i] * R[i][j] for j in range(2)] for i in range(2)]
flatten = lambda matrix: [x for row in matrix for x in row]
assert survival == F(1, 2) and conditioned == Q
assert conditioned_initial == tilted and conditioned_terminal == r
assert tv(flatten(conditioned), flatten(doob_r)) == F(1, 4)
assert tv(flatten(conditioned), flatten(doob_tilted)) == F(1, 4)

H = [[F(1), F(1)]]
for m in range(1, 4):
    H.append(col_apply(Q, H[-1]))
    assert H[m] == [rho ** m * x / 2 for x in h]
finite_kernels = {}
for m in range(1, 4):
    kernel = [[Q[i][j] * H[m - 1][j] / H[m][i]
               for j in range(2)] for i in range(2)]
    assert kernel == ([r] * 2 if m == 1 else R)
    finite_kernels[str(m)] = kernel

enumerated = []
for T in (1, 2, 3):
    actual, doob = [], []
    initial_mass = [F(0), F(0)]
    terminal_mass = [F(0), F(0)]
    for path in product(range(2), repeat=T + 1):
        w = r[path[0]]
        d = tilted[path[0]]
        for i, j in zip(path, path[1:]):
            w *= Q[i][j]
            d *= R[i][j]
        c = w / rho ** T
        actual.append(c)
        doob.append(d)
        initial_mass[path[0]] += c
        terminal_mass[path[-1]] += c
        assert d == c * h[path[-1]] / 2
    assert sum(actual) == sum(doob) == 1
    assert initial_mass == tilted and terminal_mass == r
    assert tv(actual, doob) == F(1, 4)
    enumerated.append({"horizon": T, "safe_path_count": len(actual),
                       "survival": rho ** T, "conditioned_initial": initial_mass,
                       "conditioned_terminal": terminal_mass,
                       "path_TV_to_tilted_Doob": tv(actual, doob)})

data = {
    "status": "EXACT_RATIONAL_IDENTITIES_CHECKED_NOT_LEAN",
    "scope": "One actual three-state Markov source, one unit action, fixed policy; exact finite arithmetic, no sampling or empirical claim.",
    "states": ["0", "1", "cemetery"], "safe_states": ["0", "1"],
    "source_kernel_L": L, "actual_initial_p0": p0, "killed_restriction_Q": Q,
    "left_law_r": r, "rho": rho, "positive_right_vector_h": h,
    "left_eigen_row": row_apply(r, Q), "right_eigen_column": col_apply(Q, h),
    "pairing_r_h": pairing, "normalized_right_vector_for_BiEigenData": [x / pairing for x in h],
    "Doob_kernel_R": R, "Doob_invariant_tilted_law": tilted,
    "original_unconditional_joint_3x3": unconditional_joint,
    "safe_unconditional_joint_2x2": safe_joint, "survival_1": survival,
    "actual_survival_conditioned_joint_2x2": conditioned,
    "conditioned_initial": conditioned_initial, "conditioned_terminal": conditioned_terminal,
    "Doob_joint_from_r": doob_r, "Doob_joint_from_tilted_initial": doob_tilted,
    "path_TV_to_Doob_from_r": tv(flatten(conditioned), flatten(doob_r)),
    "path_TV_to_Doob_from_tilted": tv(flatten(conditioned), flatten(doob_tilted)),
    "H_0_through_H_3": H, "finite_kernel_by_remaining_steps": finite_kernels,
    "small_horizon_exact_enumerations": enumerated,
    "general_all_horizon_claim": "The accompanying mathematical proof uses Q^2=rho Q; the finite enumerations are checks, not an all-horizon Lean proof.",
    "Lean_execution": False, "native_execution": False, "repository_modification": False
}
OUT.write_text(json.dumps(data, ensure_ascii=False, indent=2, default=str) + "\n")
print(json.dumps({"output": str(OUT), "status": data["status"],
                  "survival_1": str(survival), "both_path_TV": "1/4"}, ensure_ascii=False))
