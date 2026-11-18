"""Independent Gaussian quadrature of local Bell preparations. No source_bridge imports."""
from fractions import Fraction as F

import numpy as np
from numpy.polynomial.hermite import hermgauss

from replay import Q, distribution, scores

# Outward field intervals at lambda=.3, transcribed from source_result.json.
INTERVALS = [
    (F(8358837468711,250000000000000), F(16717674937423,500000000000000)),
    (F(6233267234927,250000000000000), F(2493306893971,100000000000000)),
    (F(263483303749,15625000000000), F(2107866429993,125000000000000)),
]


def gaussian_preparation(qa, qb, cross, order):
    # E exp[i*(d theta+e phi)] = exp[-qa*d^2-qb*e^2-cross*d*e].
    root = np.linalg.cholesky([[2*qa,cross],[cross,2*qb]])
    nodes, weights = hermgauss(order)
    rho = np.zeros((16,16), complex)
    for i,j in np.ndindex((order,order)):
        theta, phi = np.sqrt(2)*root @ [nodes[i],nodes[j]]
        def pair(angle):
            return np.array([1,0,0,np.exp(1j*angle)])/np.sqrt(2)
        ket = np.kron(pair(theta),pair(phi))
        rho += weights[i]*weights[j]/np.pi * np.outer(ket,ket.conj())
    return rho


def review():
    results = []
    for coupling in [F(3,10),F(3,1000)]:
        scale = (coupling/F(3,10))**2
        qa,qb,c = [float(scale*(l+h)/2) for l,h in INTERVALS]
        rho = gaussian_preparation(qa,qb,c,16)
        np.testing.assert_allclose(rho,gaussian_preparation(qa,qb,c,10),rtol=0,atol=1e-14)
        p = distribution(rho)
        pb = p.sum(axis=(2,4))
        np.testing.assert_allclose(pb,.25,rtol=0,atol=2e-14)
        tb = scores(p)
        parity = np.array([1,-1,1,-1])
        np.testing.assert_allclose(4*tb,2*np.sqrt(2)*(1+2*np.exp(-qa-qb-parity*c)),rtol=0,atol=6e-14)
        blocks = rho.reshape(4,4,4,4)
        prod = np.kron(np.einsum("ijkj->ik",blocks),np.einsum("ijil->jl",blocks))
        d = sum(abs(np.linalg.eigvalsh(rho-prod)))/2
        logical_y = np.zeros((4,4),complex)
        logical_y[0,3], logical_y[3,0] = -1j,1j
        # Norm-one observable attaining the real separability lower bound.
        yy = np.trace(rho @ np.kron(logical_y,logical_y)).real
        assert abs(d-abs(yy)/2)<3e-15
        assert abs(d-abs(np.exp(-qa-qb)*np.sinh(c))/2)<3e-15
        ids = [0,3,12,15]
        encoded = rho[np.ix_(ids,ids)]
        delta = (rho-prod)[np.ix_(ids,ids)]
        x = np.array([[0,1],[1,0]])
        y = np.array([[0,-1j],[1j,0]])
        one_TV = sum(abs(np.trace(delta @ np.kron((np.eye(2)+s*x)/2,(np.eye(2)+t*x)/2)))
                     for s in (1,-1) for t in (1,-1))/2
        np.testing.assert_allclose(one_TV,np.exp(-qa-qb)*np.sinh(c/2)**2,rtol=0,atol=5e-15)
        product_copies = np.kron(encoded,encoded).reshape((2,)*8)
        product_copies = product_copies.transpose(0,2,1,3,4,6,5,7).reshape(16,16)
        parity_readout = np.kron(y,y).real
        two_parity = np.trace(product_copies @ np.kron(parity_readout,parity_readout)).real
        assert abs(two_parity-yy**2)<1e-15
        # 1-exp(-t)<=t; 141422/100000 > sqrt(2). Applies to all E3 branches.
        max_t = scale*(INTERVALS[0][1]+INTERVALS[1][1]+max(map(abs,INTERVALS[2])))
        exact_upper = 4*F(141422,100000)*max_t
        if coupling==F(3,1000):
            assert exact_upper < F(5,100000)
            assert max(Q-4*tb) < float(exact_upper)
            # Preserve Thm 2 under per-setting total variation of the full table.
            eps = F(7,100000)
            radius = F(21,100000000)
            assert radius < eps
            assert (24 + 6*F(141422,100000) - eps)*radius < (eps-exact_upper)/4
        else:
            assert abs(tb.sum()-8.16530975326)<3e-12 and abs(d-.007953798396)<1e-12
        results.append(dict(coupling=str(coupling), T=float(tb.sum()), T_b=tb.tolist(),
                            max_Bob_probability_error=float(abs(pb-.25).max()),
                            D_to_marginal_product=float(d), abs_logical_YY_over_two=float(abs(yy)/2),
                            one_copy_local_X_TV_to_product=float(one_TV),
                            two_iid_copy_real_parity=float(two_parity),
                            max_branch_deficit=float(max(Q-4*tb)),
                            rigorous_deficit_upper=str(exact_upper),
                            certified_per_setting_TV_radius="21/100000000" if coupling==F(3,1000) else None,
                            passes_thm2_with_epsilon_5e_minus5=bool(exact_upper < F(5,100000))))
    return results
