"""Fresh exact audit of displayed UEOT-QM v30.11 formulas (stdlib only).

This is NOT the archived verify_v30_11.py and does NOT reproduce its 27 checks.
No network, subprocesses, or archive extraction. Output is JSON on stdout.
Uses rational Laurent polynomials in Nc, Nf, z=beta/sqrt(3), with Nc nonzero.
"""
from fractions import Fraction as F
import json


class P:
    def __init__(self, x=0):
        self.d = ({k: F(v) for k, v in x.items() if v}
                  if isinstance(x, dict) else ({(0, 0, 0): F(x)} if x else {}))

    @staticmethod
    def coerce(x):
        return x if isinstance(x, P) else P(x)

    def __add__(self, other):
        d = self.d.copy()
        for k, v in P.coerce(other).d.items():
            d[k] = d.get(k, F(0)) + v
        return P(d)

    __radd__ = __add__

    def __neg__(self):
        return P({k: -v for k, v in self.d.items()})

    def __sub__(self, other):
        return self + -P.coerce(other)

    def __rsub__(self, other):
        return P.coerce(other) + -self

    def __mul__(self, other):
        d = {}
        for k, v in self.d.items():
            for l, w in P.coerce(other).d.items():
                p = tuple(a + b for a, b in zip(k, l))
                d[p] = d.get(p, F(0)) + v * w
        return P(d)

    __rmul__ = __mul__

    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        y = P(1)
        for _ in range(n):
            y *= self
        return y

    def __truediv__(self, q):
        return self * (F(1) / F(q))

    def __eq__(self, other):
        return self.d == P.coerce(other).d

    def evaluate(self, c, f, z):
        return sum(v * F(c)**p[0] * F(f)**p[1] * F(z)**p[2]
                   for p, v in self.d.items())


C = P({(1, 0, 0): 1})
CI = P({(-1, 0, 0): 1})
N = P({(0, 1, 0): 1})
Z = P({(0, 0, 1): 1})
K = N * (1 - CI) / 2
XL = -P(F(1, 2)) - Z / 2
E = -P(F(1, 2)) - 3 * Z / 2

checks = []


def check(name, passed, detail):
    checks.append({"name": name, "pass": bool(passed), "detail": detail})


survivors = [(c, f, k) for c in range(3, 21) for f in range(1, 6)
             for k in range(f + 1)
             if 2 * c * k + f == c * f and f * (c + 1) < 22]
check("selector_without_atomicity_complete_bounded_enumeration",
      survivors == [(3, 3, 1)],
      {"survivors": survivors,
       "bounds_proven_in_note": "3<=Nc<=20, 1<=Nf<=5, 0<=k<=Nf"})

for c in range(2, 101):
    d = 2 if c % 2 else 1
    f0, k0 = 2 * c // d, (c - 1) // d
    assert 2 * c * k0 + f0 == c * f0
check("primitive_formula_integer_checks_2_through_100", True,
      "A finite arithmetic check, not the proof of the all-integer formula.")

for mode in ("fixed_observed_charges", "generalized_Nc_charges"):
    qbar = P(F(1, 6)) if mode == "fixed_observed_charges" else CI / 2
    u = P(F(2, 3)) if mode == "fixed_observed_charges" else (1 + CI) / 2
    d = P(-F(1, 3)) if mode == "fixed_observed_charges" else (-1 + CI) / 2
    XP, XM = qbar - Z / 2, qbar + Z / 2
    JP, JM = qbar - 3 * Z / 2, qbar + 3 * Z / 2
    AL2X = (N * XL + C * K * XP + C * (N - K) * XM) / 2
    AX3 = (N * (3 * XL**3 + 1 - E**3)
           + C * K * (3 * XP**3 - u**3 - d**3 - JP**3)
           + C * (N - K) * (3 * XM**3 - u**3 - d**3 - JM**3))
    AGR = (N * (3 * XL + 1 - E)
           + C * K * (3 * XP - u - d - JP)
           + C * (N - K) * (3 * XM - u - d - JM))
    AC2X = (K * (3 * XP - u - d - JP)
            + (N - K) * (3 * XM - u - d - JM)) / 2
    expected_L = N * (C - 3) / 12 if mode == "fixed_observed_charges" else P()
    expected_X = -N * (C - 3) * (1 + 3 * Z**2) / 4 if mode == "fixed_observed_charges" else P()
    check(mode + "_complete_spectrum_symbolic", AL2X == expected_L and AX3 == expected_X and AGR == 0 and AC2X == 0,
          "Exact rational Laurent-polynomial identities; includes E^c of charge -qE.")
    if mode == "fixed_observed_charges":
        check("missing_Ec_gravitational_residual", AGR + N * E == N * E,
              {"formula": "Nf*qE = -Nf*(1+3*z)/2",
               "Nc3_Nf3_beta0": str((AGR + N * E).evaluate(3, 3, 0))})
        check("missing_Ec_cubic_residual", AX3 + N * E**3 - expected_X == N * E**3,
              {"extra_term": "Nf*qE^3",
               "Nc3_Nf3_beta0": str((AX3 + N * E**3).evaluate(3, 3, 0))})


def anomaly_vector(rows):
    # row = multiplicity, dC, dL, A(C), A(L), T(C), T(L), X
    out = {k: F(0) for k in ("C3", "L3", "C2X", "L2X", "gravX", "X3")}
    for m, dc, dl, ac, al, tc, tl, x in rows:
        out["C3"] += m * dl * ac
        out["L3"] += m * dc * al
        out["C2X"] += m * dl * tc * x
        out["L2X"] += m * dc * tl * x
        out["gravX"] += m * dc * dl * x
        out["X3"] += m * dc * dl * x**3
    return out


hal = F(1, 2)
rhn = [
    (3, 1, 3, 0, 1, 0, hal, -F(1, 3)),
    (3, 1, 1, 0, 0, 0, 0, F(1)),
    (1, 3, 3, 1, 1, hal, hal, F(1, 3)),
    (2, 3, 3, 1, -1, hal, hal, F(0)),
    (4, 3, 1, -1, 0, hal, 0, -F(2, 3)),
    (5, 3, 1, -1, 0, hal, 0, F(1, 3)),
]
av = anomaly_vector(rhn)
check("331RHN_six_local_anomalies_independent_rational_check",
      all(v == 0 for v in av.values()), {k: str(v) for k, v in av.items()})

two_family = [
    (1, 1, 3, 0, 1, 0, hal, -hal),
    (1, 1, 3, 0, -1, 0, hal, -hal),
    (2, 1, 1, 0, 0, 0, 0, F(1)),
    (2, 1, 1, 0, 0, 0, 0, hal),
    (1, 3, 3, 1, 1, hal, hal, F(1, 6)),
    (1, 3, 3, 1, -1, hal, hal, F(1, 6)),
    (2, 3, 1, -1, 0, hal, 0, -F(2, 3)),
    (2, 3, 1, -1, 0, hal, 0, F(1, 3)),
    (2, 3, 1, -1, 0, hal, 0, -F(1, 6)),
]
av = anomaly_vector(two_family)
check("two_family_countermodel_if_leptons_may_use_both_3_and_3bar",
      all(v == 0 for v in av.values()) and 2 * (3 + 1) < 22,
      {"local_anomalies": {k: str(v) for k, v in av.items()},
       "Nc_Nf_l_k": [3, 2, 1, 1], "beta": 0,
       "scope": "Local anomaly spectrum witness only; no scalar vacuum/global anomaly/phenomenology certification."})

ablations = [
    ("complex_color_lower_bound", 2, 4, 1),
    ("weak_positive_slope", 3, 6, 2),
    ("anomaly_equation", 3, 1, 0),
    ("positive_family_count", 4, 0, 0),
]
for dropped, c, f, k in ablations:
    conditions = {
        "complex_color_lower_bound": c >= 3,
        "weak_positive_slope": f * (c + 1) < 22,
        "anomaly_equation": f + c * (2 * k - f) == 0,
        "positive_family_count": f > 0,
        "quark_multiplicity_range": 0 <= k <= f,
    }
    check("drop_" + dropped,
          not conditions[dropped] and all(v for key, v in conditions.items() if key != dropped),
          {"Nc_Nf_k": [c, f, k], "anomaly_residual": f + c * (2 * k - f),
           "weak_budget": f * (c + 1), "conditions": conditions})
check("drop_integer_k", 2 * 4 * F(3, 2) + 4 == 4 * 4 and 4 * 5 < 22,
      {"Nc": 4, "Nf": 4, "k": "3/2"})

report = {
    "audit": "New v30.11 displayed-formula audit, not archival rerun",
    "algebra": "Python stdlib fractions.Fraction; sparse Laurent polynomials over Q",
    "selector": "No primitive/atomicity hypothesis used",
    "count": len(checks), "passed": sum(c["pass"] for c in checks), "checks": checks,
}
print(json.dumps(report, indent=2, ensure_ascii=False))
assert all(c["pass"] for c in checks)
