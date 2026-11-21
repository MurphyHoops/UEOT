"""Spacelike common-field noise on two Bell links: interval and direct matrix checks."""
import itertools
import json
import math
import sys
from pathlib import Path

import numpy as np
from mpmath import iv

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "cross_domain/field"))
import match

I, X, Y, Z = (np.eye(2), np.array([[0, 1], [1, 0]]),
              np.array([[0, -1j], [1j, 0]]), np.diag([1, -1]))


def field_noise(last):
    setting = next(e for e in match.design["experiments"] if e["id"] == "strict_spacelike")
    a, b, gap = (match.q(setting[k]) for k in ("a", "b", "gap"))
    lam, n, c = (match.q(match.design["point"][k]) for k in ("lambda", "n", "c"))
    assert setting["antipodal"] and match.probe.length*(match.q("1/2")-2*match.q("23/120")) > a+gap+b
    qa, qb, cross, retarded = (match.q(0) for _ in range(4))
    for j in range(last + 1):
        w, g = match.mode(j)
        u = lam * match.pulse(w, g, 0, a)
        v = lam * match.pulse(w, (-1)**j*g, a+gap, b)
        dot = lambda u, v: u.real*v.real + u.imag*v.imag
        occupation_weight = 1 + 2*n if j < 2 else 1
        qa += 2*occupation_weight*match.abs2(u)
        qb += 2*occupation_weight*match.abs2(v)
        cross += 4*occupation_weight*dot(u, v)
        retarded += 4*(u.real*v.imag - u.imag*v.real)
        if j == 0:
            u0, v0 = u, v
        if j == 1:
            qa += 8*c*dot(u0, u)
            qb += 8*c*dot(v0, v)
            cross += 8*c*(dot(u0, v) + dot(u, v0))
    tail = lam**2 * match.htail(last)
    qa += iv.mpf([0, 8])*tail
    qb += iv.mpf([0, 8])*tail
    cross += iv.mpf([-16, 16])*tail
    retarded += iv.mpf([-16, 16])*tail
    assert 0 in retarded and 4*qa*qb > cross**2
    return qa, qb, cross


def direct_network(a, b, c):
    # Logical basis |ii jj>, parties A, B_left, B_right, C. Gaussian characteristic function.
    rho = np.zeros((16, 16), complex)
    for i, j, k, l in itertools.product(range(2), repeat=4):
        d, e = i-k, j-l
        rho[12*i+3*j, 12*k+3*l] = math.exp(-a*d*d-b*e*e-c*d*e)/4
    assert np.linalg.eigvalsh(rho).min() > -1e-12 and abs(np.trace(rho)-1) < 1e-14
    left, right = np.trace(rho.reshape(4,4,4,4), axis1=1, axis2=3), np.trace(rho.reshape(4,4,4,4), axis1=0, axis2=2)
    # X-basis dephasing of both logical rebits gives a real separable minimizer.
    indices = [0, 3, 12, 15]
    logical = rho[np.ix_(indices, indices)]
    hadamard = np.array([[1, 1], [1, -1]]) / math.sqrt(2)
    change = np.kron(hadamard, hadamard)
    real_weights = np.diag(change @ logical @ change.T).real
    assert min(real_weights) >= -1e-14 and abs(sum(real_weights)-1) < 1e-14
    candidate = change.T @ np.diag(real_weights) @ change
    distance_separable = np.linalg.norm(logical-candidate, ord="nuc") / 2
    joint_y = np.kron(Y, Y)
    dual_lower = abs(np.trace(logical @ joint_y)) / 2
    assert np.allclose(np.diag(change @ (logical-candidate) @ change.T), 0, atol=1e-14)
    # Two i.i.d. copies, reordered into their left and right labs. YY is real locally.
    reorder = np.arange(16).reshape(2,2,2,2).transpose(0,2,1,3).ravel()
    two_copy = np.kron(logical, logical)[np.ix_(reorder, reorder)]
    twirled = np.kron(candidate, candidate)[np.ix_(reorder, reorder)]
    assert np.max(abs(joint_y.imag)) == 0
    parity_gap = np.trace((two_copy-twirled) @ np.kron(joint_y, joint_y)).real
    assert abs(parity_gap - (2*dual_lower)**2) < 1e-14
    assert abs(distance_separable-dual_lower) < 1e-14
    product_distance = np.linalg.norm(rho-np.kron(left, right), ord="nuc") / 2
    assert abs(product_distance-distance_separable) < 1e-14
    labels = [np.array(v)/math.sqrt(2) for v in ([1,0,0,1], [0,1,1,0], [1,0,0,-1], [0,1,-1,0])]
    axes = [Z, X, Y]
    contributions, all_prob = [], []
    for label, bell in enumerate(labels):
        projector = np.outer(bell, bell)
        signs = [(-1)**(label % 2), (-1)**(label // 2), -(-1)**((label % 2) + (label // 2))]
        term = 0.
        for i, j in ((0,1), (0,2), (1,2)):
            for sign in (1, -1):
                charlie = (axes[i] + sign*axes[j])/math.sqrt(2)
                for x, alice in enumerate(axes):
                    correlation = 0.
                    for aa, cc in itertools.product((1, -1), repeat=2):
                        effect = np.kron(np.kron((I+aa*alice)/2, projector), (I+cc*charlie)/2)
                        probability = np.trace(rho @ effect).real
                        assert probability >= -1e-14
                        all_prob.append(probability)
                        correlation += aa*cc*probability
                    if x == i:
                        term += signs[i]*correlation
                    if x == j:
                        term += sign*signs[j]*correlation
        contributions.append(term)
    probabilities = np.array(all_prob).reshape(4,6,3,2,2)
    np.testing.assert_allclose(probabilities.sum(axis=(0,3,4)), np.ones((6,3)), rtol=0, atol=1e-14)
    np.testing.assert_allclose(probabilities.sum(axis=(3,4)), .25, rtol=0, atol=1e-14)
    return product_distance, contributions, probabilities.transpose(2, 1, 3, 0, 4)


def result():
    qa, qb, cross = field_noise(320)
    zero_cross = iv.exp(-qa-qb)
    plus, minus = iv.exp(cross), iv.exp(-cross)
    xx = zero_cross*((plus+minus)/2 - 1)
    yy = zero_cross*(plus-minus)/2
    distance = abs(yy)/2
    score = 2*iv.sqrt(2)*(1 + zero_cross*(plus+minus))
    product_score = 2*iv.sqrt(2)*(1 + 2*zero_cross)
    num_distance, terms, _ = direct_network(*(float(t.mid) for t in (qa, qb, cross)))
    assert abs(num_distance - float(distance.mid)) < 2e-14
    assert abs(sum(terms) - float(score.mid)) < 2e-13
    assert min(terms) < max(terms) and abs(yy) > xx > 0 and score > match.q("7.67")
    _, no_cross, _ = direct_network(float(qa.mid), float(qb.mid), 0.)
    assert abs(sum(no_cross)-float(product_score.mid)) < 2e-13
    # Separate dose chosen from 1-exp(-u)<=u, before evaluating the new table.
    weak_scale = match.q("1/100")**2
    analytic_epsilon = match.q("0.00006")  # strictly inside Theorem 2
    tv_radius = match.q("0.0000001")
    weak_deficits = [4*iv.sqrt(2)*(1-iv.exp(-weak_scale*(qa+qb+sgn*cross))) for sgn in (1,-1)]
    _, weak_terms, _ = direct_network(*(float((weak_scale*t).mid) for t in (qa,qb,cross)))
    for label, term in enumerate(weak_terms):
        deficit = weak_deficits[label % 2]
        assert abs((6*math.sqrt(2)-4*term) - float(deficit.mid)) < 1e-13
        assert (analytic_epsilon-deficit)/4 > (24+6*iv.sqrt(2)-analytic_epsilon)*tv_radius
    assert tv_radius < analytic_epsilon
    # Fixed-source question: allow every local real measurement on this known matrix.
    # Uniformly bound the distance to its X-dephased, real separable competitor.
    rmax = match.q("1/200")**2  # lambda <= .0015 relative to lambda=.3
    real_distance_upper = rmax*abs(cross)*iv.exp(rmax*abs(cross))/2
    max_deficit = 4*iv.sqrt(2)*rmax*(qa+qb+abs(cross))
    table_radius = match.q("0.00000037")
    assert (analytic_epsilon-max_deficit)/4 > (24+6*iv.sqrt(2)-analytic_epsilon)*table_radius
    assert real_distance_upper < match.q("0.000000211") < table_radius < analytic_epsilon
    fixed_source_radius = match.q("0.000000159")
    assert real_distance_upper + fixed_source_radius < table_radius
    return {"fixed_real_source_window": {"abs_lambda_max":"3/2000",
                "real_separable_distance_upper":match.interval(real_distance_upper),
                "all_branch_deficit_upper":match.interval(max_deficit),
                "uniform_exclusion_radius_full_TV":"159/1000000000"},
            "weak_lambda": "3/1000", "weak_branch_deficits":list(map(match.interval, weak_deficits)),
            "excluded_real_neighborhood_TV_radius":"1/10000000",
            **{k:match.interval(v) for k,v in dict(Q_left=qa, Q_right=qb, cross=cross,
            excess_XX=xx, YY=yy, product_half_trace=distance, real_separable_half_trace=distance,
            single_copy_real_local_TV_to_product=abs(xx)/2, two_copy_real_local_parity_gap=yy**2,
            T_shared_field=score, T_product_marginals=product_score).items()},
            "direct_matrix_T_by_b":terms, "total_probabilities_checked":288}


if __name__ == "__main__":
    current = result()
    if sys.argv[1:] == ["--check"]:
        stored = json.loads((HERE/"source_result.json").read_text())
        np.testing.assert_allclose(current["direct_matrix_T_by_b"], stored.pop("direct_matrix_T_by_b"), atol=1e-13, rtol=0)
        del current["direct_matrix_T_by_b"]
        assert current == stored
        print("PASS: full field, two Bell links, source distances and 288 probabilities")
    else:
        print(json.dumps(current, indent=2))
