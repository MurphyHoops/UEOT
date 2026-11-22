"""Cross-check the field-to-network bridge, using Gaussian phase mixtures and no source_bridge import."""
from fractions import Fraction
import hashlib
import json
from pathlib import Path

import numpy as np
from mpmath import iv
from network import probabilities, score, X, Y

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / "source_result.json"


def mixture(qa,qb,cross,order):
    # N(0,Sigma), E exp(i d.theta) = exp(-qa*d_L^2-qb*d_R^2-cross*d_L*d_R).
    chol = np.linalg.cholesky([[2*qa,cross],[cross,2*qb]])
    nodes, weights = np.polynomial.hermite.hermgauss(order)
    pairs = np.stack(np.meshgrid(nodes,nodes,indexing="ij")).reshape(2,-1)
    theta = np.sqrt(2)*chol@pairs
    # For each quadrature node the logical two-link vector is a product (1,e^itL) x (1,e^itR)/2.
    phases = np.array([[0,0],[0,1],[1,0],[1,1]])@theta
    psi = np.exp(1j*phases)/2
    logical = (psi*(np.outer(weights,weights).ravel()/np.pi))@psi.conj().T
    rho = np.zeros((16,16),complex)
    codewords = [0,3,12,15]
    rho[np.ix_(codewords,codewords)] = logical
    return rho, logical


def intervals(entry):
    fractions = list(map(Fraction,entry))
    bounds = [iv.mpf(f.numerator)/f.denominator for f in fractions]
    return iv.mpf([bounds[0].a,bounds[1].b])


def point(args, ratio, baseline):
    qa,qb,cross = [v*ratio for v in args]
    mids = [float(v.mid) for v in (qa,qb,cross)]
    rho, logical = mixture(*mids,13)
    check, _ = mixture(*mids,9)
    p = probabilities(rho)
    assert np.max(np.abs(probabilities(check)-p)) < 1e-13
    per_b = p.sum(axis=(2,4))
    assert np.max(np.abs(per_b-.25)) < 1e-13
    total, branches = score(p)
    expected = [2*iv.sqrt(2)*(1+2*iv.exp(-qa-qb-(-1)**(b%2)*cross)) for b in range(4)]
    assert max(abs(4*t-float(e.mid)) for t,e in zip(branches,expected)) < 1e-12
    rho4 = logical.reshape(2,2,2,2)
    product = np.kron(np.trace(rho4,axis1=1,axis2=3),np.trace(rho4,axis1=0,axis2=2))
    d = np.abs(np.linalg.eigvalsh(logical-product)).sum()/2
    y = np.trace(logical@np.kron(Y,Y)).real
    assert abs(abs(y)/2-d) < 1e-14
    # The one-copy observable XX distinguishes the KG source from its product already.
    excess_x = np.trace((logical-product)@np.kron(X,X)).real
    # L1,L2 | R1,R2. Both local factors Y x Y are real symmetric.
    two = np.kron(logical,logical).reshape((2,)*8).transpose(0,2,1,3,4,6,5,7).reshape(16,16)
    parity = np.kron(Y,Y).real
    joint = np.trace(two@np.kron(parity,parity)).real
    assert abs(joint-y*y) < 1e-15
    if ratio == 1:
        assert abs(d-float(intervals(baseline['product_half_trace']).mid)) < 1e-13
        np.testing.assert_allclose(branches,baseline['direct_matrix_T_by_b'],atol=1e-13,rtol=0)
    # A conservative sub-threshold of Renou Theorem 2; use endpoint comparisons, not the quadrature.
    eps = iv.mpf(7)/100000
    margins = [(e-(6*iv.sqrt(2)-eps))/4 for e in expected]
    theorem2 = all(m>0 for m in margins)
    # Round sufficient displayed lower bounds DOWN, both for score margin and for admissible TV.
    def floor10(v):
        return int((v.a*10**10).a)/10**10 if v>0 else None
    min_margin = min(margins,key=lambda m: float(m.a))
    tv_radius = min_margin/(24+6*iv.sqrt(2)-eps)
    return dict(T=total,T_b=branches,conditional_4T_b=[4*v for v in branches],
                p_b=per_b[0,0].tolist(),max_p_b_deviation=float(np.abs(per_b-.25).max()),
                distance_to_marginal_product=float(d),half_real_YY_witness=float(abs(y)/2),
                one_copy_real_local_TV_to_product=float(abs(excess_x)/2),two_iid_copies_parity_gap=float(joint),
                hermite_9_13_max_probability_difference=float(np.abs(probabilities(check)-p).max()),
                analytic_branch_criterion=theorem2,
                sufficient_all_branch_margin_lower=floor10(min_margin),
                sufficient_extra_uniform_TV_radius_lower=floor10(tv_radius))


def main():
    if not __debug__:
        raise RuntimeError("run without -O")
    iv.dps=45
    data=SOURCE.read_bytes()
    baseline=json.loads(data)
    args=[intervals(baseline[k]) for k in ('Q_left','Q_right','cross')]
    large=point(args,1,baseline)
    small=point(args,iv.mpf(1)/10000,baseline)
    assert not large['analytic_branch_criterion'] and small['analytic_branch_criterion']
    keys = ('Q_left','Q_right','cross','product_half_trace','direct_matrix_T_by_b')
    used = {k: baseline[k] for k in keys}
    binding = hashlib.sha256(json.dumps(used,sort_keys=True,separators=(',',':')).encode()).hexdigest()
    eps = iv.mpf(7)/100000
    r = iv.sqrt(2)
    e1 = iv.sqrt(r*eps)
    n = (3+r)*e1
    e2 = (15+13*r)*e1
    g31 = 2*iv.sqrt(((2+n)/2)**2 - (1-(n+e2**2)/2)**2)
    g33 = (7+3*r)*e1+4*(1+n)*eps
    assert g31+g33 < iv.mpf(991)/1000
    print(json.dumps(dict(G31_plus_G33_verified_upper=.991,
                          scientific_inputs=used,scientific_inputs_sha256=binding,
                          method='independent correlated Gaussian product-vector quadrature',
                          lambda_0_3=large,lambda_0_003=small),indent=2))


if __name__ == '__main__':
    main()
