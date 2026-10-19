#!/usr/bin/env python3
"""Exact, small UEOT-QM bridge regressions using only Python's standard library.

These are finite mathematical witnesses, not Lean proofs or experimental data.
The matrix formulas assume standard quantum instrument/trace semantics; they do
not derive the Born rule. Run with Python 3; JSON is printed to standard output.
"""

from fractions import Fraction as F
import json


def matrix(rows):
    return tuple(tuple(F(x) for x in row) for row in rows)


I = matrix([[1, 0], [0, 1]])
Z0 = matrix([[1, 0], [0, 0]])
Z1 = matrix([[0, 0], [0, 1]])
H0 = matrix([[1, 1], [1, -1]])  # H = H0/sqrt(2); conjugation uses H0 twice / 2.
RHO_PLUS = matrix([[F(1, 2), F(1, 2)], [F(1, 2), F(1, 2)]])
RHO_MINUS = matrix([[F(1, 2), F(-1, 2)], [F(-1, 2), F(1, 2)]])


def mul(a, b):
    return tuple(
        tuple(sum(a[i][k] * b[k][j] for k in range(len(b)))
              for j in range(len(b[0])))
        for i in range(len(a))
    )


def scale(c, a):
    return tuple(tuple(F(c) * x for x in row) for row in a)


def subtract(a, b):
    return tuple(tuple(x - y for x, y in zip(ra, rb))
                 for ra, rb in zip(a, b))


def trace(a):
    return sum(a[i][i] for i in range(len(a)))


def sandwich(k, a, factor=F(1)):
    # Every k used in these witnesses is real symmetric, so k*=k.
    return scale(factor, mul(mul(k, a), k))


def rank(matrices):
    """Exact row rank of flattened 2x2 matrices; no floating point tolerance."""
    rows = [list(x for row in m for x in row) for m in matrices]
    r = 0
    for c in range(4):
        pivot = next((i for i in range(r, len(rows)) if rows[i][c]), None)
        if pivot is None:
            continue
        rows[r], rows[pivot] = rows[pivot], rows[r]
        divisor = rows[r][c]
        rows[r] = [x / divisor for x in rows[r]]
        for i in range(len(rows)):
            if i != r:
                coefficient = rows[i][c]
                rows[i] = [x - coefficient * y
                           for x, y in zip(rows[i], rows[r])]
        r += 1
        if r == len(rows):
            break
    return r


def observable_closure(include_h):
    """W <- span(W, I_y^*(W)) for the exact Z and optional H instruments."""
    basis = [I]
    dimensions = [1]
    while True:
        old = list(basis)
        candidates = [sandwich(z, e) for e in old for z in (Z0, Z1)]
        if include_h:
            candidates.extend(sandwich(H0, e, F(1, 2)) for e in old)
        for e in candidates:
            if rank(basis + [e]) > len(basis):
                basis.append(e)
        dimensions.append(len(basis))
        assert len(basis) <= 4, "Hermitian 2x2 ambient dimension exceeded"
        if len(basis) == len(old):
            return basis, dimensions


def tv(p, q):
    assert sum(p) == sum(q) == 1
    assert all(x >= 0 for x in p + q)
    return sum(abs(x - y) for x, y in zip(p, q)) / 2


def z_distribution(rho):
    return tuple(trace(sandwich(z, rho)) for z in (Z0, Z1))


def protocol_closure_witness():
    z_basis, z_dims = observable_closure(False)
    hz_basis, hz_dims = observable_closure(True)
    difference = subtract(RHO_PLUS, RHO_MINUS)
    assert len(z_basis) == 2
    assert len(hz_basis) == 3
    assert all(trace(mul(difference, e)) == 0 for e in z_basis)
    assert any(trace(mul(difference, e)) != 0 for e in hz_basis)
    z_plus = z_distribution(RHO_PLUS)
    z_minus = z_distribution(RHO_MINUS)
    h_plus = sandwich(H0, RHO_PLUS, F(1, 2))
    h_minus = sandwich(H0, RHO_MINUS, F(1, 2))
    hz_plus = z_distribution(h_plus)
    hz_minus = z_distribution(h_minus)
    assert z_plus == z_minus == (F(1, 2), F(1, 2))
    assert hz_plus == (F(1), F(0))
    assert hz_minus == (F(0), F(1))
    assert tv(z_plus, z_minus) == 0
    assert tv(hz_plus, hz_minus) == 1
    # Explicitly verify closure, not merely its dimension.
    for basis, use_h in ((z_basis, False), (hz_basis, True)):
        for e in basis:
            images = [sandwich(z, e) for z in (Z0, Z1)]
            if use_h:
                images.append(sandwich(H0, e, F(1, 2)))
            assert all(rank(basis + [image]) == len(basis) for image in images)
    return {
        "status": "PASS",
        "z_closure_dimensions": z_dims,
        "h_z_closure_dimensions": hz_dims,
        "z_plus": list(z_plus),
        "z_minus": list(z_minus),
        "h_then_z_plus": list(hz_plus),
        "h_then_z_minus": list(hz_minus),
        "z_record_tv": 0,
        "h_then_z_record_tv": 1,
        "meaning": "A Z-only predictive quotient is invalid once H is an allowed action.",
        "scope": "Exact specified 2x2 instruments; does not reconstruct quantum kinematics.",
    }


def postselection_witness():
    rows = []
    for denominator in (10, 100, 1000, 1000000):
        epsilon = F(1, denominator)
        # Records: (success,0), (success,1), failure.
        p = (epsilon, F(0), 1 - epsilon)
        q = (F(0), epsilon, 1 - epsilon)
        p_success, q_success = p[0] + p[1], q[0] + q[1]
        conditioned_p = tuple(x / p_success for x in p[:2])
        conditioned_q = tuple(x / q_success for x in q[:2])
        assert tv(p, q) == epsilon
        assert p_success == q_success == epsilon > 0
        assert tv(conditioned_p, conditioned_q) == 1
        rows.append({
            "unconditional_tv": epsilon,
            "both_success_probabilities": epsilon,
            "conditional_tv": F(1),
        })
    return {
        "status": "PASS",
        "examples": rows,
        "meaning": "Small full-record error can become maximal after rare-event selection.",
        "scope": "Exact positive-probability records; success rates must remain in the certificate.",
    }


def finite_ccr_trace_witness():
    q = matrix([[1, 0], [0, -1]])
    p = matrix([[0, 1], [1, 0]])
    qp, pq = mul(q, p), mul(p, q)
    commutator = subtract(qp, pq)
    assert trace(qp) == trace(pq)
    assert trace(commutator) == 0
    assert trace(I) == 2
    # The coefficients of hbar in Re/Im Tr(i*hbar*I_2) are (0, 2).
    rhs_hbar_coefficient = (F(0), trace(I))
    assert rhs_hbar_coefficient != (F(0), F(0))
    return {
        "status": "PASS",
        "q": q,
        "p": p,
        "commutator": commutator,
        "trace_commutator": trace(commutator),
        "trace_i_hbar_identity_real_imag_hbar_coefficients": rhs_hbar_coefficient,
        "general_argument": "Tr(QP)=sum_ij Q_ij P_ji=Tr(PQ) by exchanging i,j.",
        "meaning": "Finite dimension d>0 and hbar!=0 obstruct exact [Q,P]=i*hbar*I_d.",
        "scope": "Finite rational witness plus stated trace argument; no unbounded-operator proof.",
    }


def nonprimitive_selector_witness():
    # The positive integer inequality nf*(nc+1)<22 with nf>=1 bounds nc<=20.
    # No atomicity, primitivity, or gcd filter appears in the candidate search.
    survivors = []
    candidates_checked = 0
    for nc in range(3, 21):
        for nf in range(1, 21 // (nc + 1) + 1):
            for k in range(nf + 1):
                candidates_checked += 1
                if nf + nc * (2 * k - nf) == 0:
                    survivors.append({"Nc": nc, "Nf": nf, "k": k})
    assert survivors == [{"Nc": 3, "Nf": 3, "k": 1}]
    # Necessary-premise witnesses: remove complex color or the weak upper bound.
    assert 4 + 2 * (2 * 1 - 4) == 0 and 4 * (2 + 1) < 22
    assert 6 + 3 * (2 * 2 - 6) == 0 and 6 * (3 + 1) >= 22
    return {
        "status": "PASS",
        "candidate_tuples_checked": candidates_checked,
        "survivors_without_atomicity_filter": survivors,
        "without_complex_color": {"Nc": 2, "Nf": 4, "k": 1},
        "without_weak_bound": {"Nc": 3, "Nf": 6, "k": 2},
        "meaning": "Atomicity is redundant for the declared integer selector with the strict weak bound.",
        "scope": "Exact finite enumeration with an analytically derived exhaustive bound; no HGP applicability proof.",
    }


def rational_json(x):
    if isinstance(x, F):
        return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"
    raise TypeError(f"Cannot encode {type(x).__name__}")


def main():
    results = {
        "schema": "ueot-qm-bridge-exact-witnesses/1",
        "evidence_kind": "finite_exact_regression_not_lean_or_real_data",
        "protocol_closure": protocol_closure_witness(),
        "rare_event_postselection": postselection_witness(),
        "finite_dimensional_ccr": finite_ccr_trace_witness(),
        "selector_without_atomicity": nonprimitive_selector_witness(),
    }
    results["summary"] = {"groups_passed": 4, "status": "PASS"}
    print(json.dumps(results, default=rational_json, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
