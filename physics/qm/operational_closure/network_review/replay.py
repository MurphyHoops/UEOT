"""Renou E3, real common-reference countermodel, and adverse sampling checks."""
import argparse
import hashlib
import json
from itertools import combinations, product
from pathlib import Path

import numpy as np

I = np.eye(2)
Z = np.diag([1., -1.])
X = np.array([[0., 1.], [1., 0.]])
J = np.array([[0., -1.], [1., 0.]])
Y = 1j * J
AXES = (Z, X, Y)
PAIRS = tuple(combinations(range(3), 2))
DIAGONALS = [(AXES[u] + sign*AXES[v])/np.sqrt(2)
             for u, v in PAIRS for sign in (1, -1)]
BELLS = [np.array(bits)/np.sqrt(2) for bits in
         [(1,0,0,1), (0,1,1,0), (1,0,0,-1), (0,1,-1,0)]]
BSM = [np.outer(ket,ket) for ket in BELLS]
R = 7.6605
Q = 6*np.sqrt(2)
CELLS = [(x,z) for z in range(6) for x in PAIRS[z//2]]


def weight(x, z, b):
    """E3 coefficient before multiplying a*c; x,z are zero-based."""
    u, v = PAIRS[z//2]
    q = ((-1)**(b % 2), (-1)**(b//2), -(-1)**((b//2)+(b % 2)))
    if x == u:
        return q[x]
    if x == v:
        return q[x] * (-1)**(z % 2)
    return 0


def checked_state(rho, dimension):
    rho = np.asarray(rho)
    if rho.shape != (dimension,dimension) or not np.isfinite(rho).all():
        raise ValueError("wrong state shape or nonfinite entries")
    if not np.allclose(rho,rho.conj().T,rtol=0,atol=1e-11):
        raise ValueError("non-Hermitian state")
    if abs(np.trace(rho)-1)>1e-10 or np.linalg.eigvalsh(rho)[0]<-1e-10:
        raise ValueError("state must be positive and normalized")
    return rho


def born_table(rho, axes, diagonals):
    p = np.empty((3,6,2,4,2))
    ident = np.eye(len(axes[0]))
    for x,z,i,b,j in np.ndindex(p.shape):
        ea = (ident + (-1)**i*axes[x])/2
        ec = (ident + (-1)**j*diagonals[z])/2
        effect = np.kron(np.kron(ea, BSM[b]),ec)
        value = np.einsum("ij,ji->",rho,effect)
        if abs(value.imag)>1e-11:
            raise ArithmeticError("nonreal Born probability")
        p[x,z,i,b,j] = value.real
    return checked_table(p)


def distribution(rho):
    """P[x-1,z-1,i,b,j], A,B1,B2,C order, b=Phi+,Psi+,Phi-,Psi-."""
    return born_table(checked_state(rho,16), AXES, DIAGONALS)


def checked_table(p):
    p = np.asarray(p)
    if p.shape!=(3,6,2,4,2) or not np.isrealobj(p) or not np.isfinite(p).all() or p.min() < -1e-11:
        raise ValueError("invalid probabilities or axes")
    if not np.allclose(p.sum(axis=(2,3,4)),1,rtol=0,atol=1e-10):
        raise ValueError("each setting needs one full joint distribution")
    return p


def scores(p):
    """Four joint-weighted E3 scores. Sum them for the witness."""
    p = checked_table(p)
    ac = p[:,:,0,:,0]+p[:,:,1,:,1]-p[:,:,0,:,1]-p[:,:,1,:,0]
    return np.array([sum(weight(x,z,b)*ac[x,z,b] for x,z in CELLS) for b in range(4)])


def shared_real_distribution(v=1.):
    """Fully real network, with a cross-source phase reference of strength v."""
    if not 0<=v<=1:
        raise ValueError("reference visibility must be in [0,1]")
    physical = np.kron(BSM[0],BSM[0])
    omega = (np.eye(4)-v*np.kron(J,J))/4
    # flags at A,C. Permute (fA,fC,A,B1,B2,C) to (fA,A,B1,B2,fC,C).
    permutation = (0,2,3,4,1,5)
    order = permutation + tuple(i+6 for i in permutation)
    rho = np.kron(omega,physical).reshape((2,)*12).transpose(order).reshape(64,64)
    def realify(h):
        return np.kron(I,h.real)+np.kron(J,h.imag)
    return born_table(checked_state(rho,64),list(map(realify,AXES)),list(map(realify,DIAGONALS)))


def check_reference():
    direct = distribution(np.kron(BSM[0],BSM[0]))
    ideal = np.empty_like(direct)
    for x,z,i,b,j in np.ndindex(ideal.shape):
        ideal[x,z,i,b,j] = (1+(-1)**(i+j)*weight(x,z,b)/np.sqrt(2))/16
    np.testing.assert_allclose(direct,ideal,rtol=0,atol=1e-14)
    real = shared_real_distribution()
    np.testing.assert_allclose(real,direct,rtol=0,atol=1e-14)
    np.testing.assert_allclose(scores(real),np.full(4,Q/4),rtol=0,atol=1e-13)
    for v in [0,.25,.75,1]:
        np.testing.assert_allclose(scores(shared_real_distribution(v)).sum(),
                                   (4+2*v)*np.sqrt(2),atol=1e-13,rtol=0)
    white = np.eye(4)/4
    noisy = distribution(np.kron(.9*BSM[0]+.1*white,.8*BSM[0]+.2*white))
    np.testing.assert_allclose(noisy,.72*ideal+.28/16,atol=1e-14,rtol=0)
    # Unequal b weights catch accidental branch renormalization and label swaps.
    weights = [.1,.2,.3,.4]
    flagged = sum(w*np.outer(ket,ket) for b,w in enumerate(weights)
                  for ket in [np.kron(BELLS[b],BELLS[b]).reshape((2,)*4)
                              .transpose(0,2,3,1).reshape(16)])
    unequal = distribution(flagged)
    np.testing.assert_allclose(unequal.sum(axis=(2,4)),np.tile(weights,(3,6,1)),atol=1e-14)
    np.testing.assert_allclose(scores(unequal),Q*np.array(weights),atol=1e-13)
    return {"cells_checked":int(real.size), "max_complex_vs_real_cell_error":float(abs(real-direct).max()),
            "T_b":scores(real).tolist(), "T":float(scores(real).sum()),
            "unequal_b_weight_scores":scores(unequal).tolist(), "T_Werner_090_080":float(scores(noisy).sum()),
            "v_to_match_Wu_central":float((7.83/np.sqrt(2)-4)/2)}


def operational_independence():
    # Exact integers: 16*(rho-rho_L*rho_R) on two (flag,Bell-link) sources at v=1.
    bell_twice = np.outer([1,0,0,1],[1,0,0,1])
    skew = np.kron(J.astype(int),bell_twice)
    delta16 = -np.kron(skew,skew).reshape(8,8,8,8)
    basis = []
    for i in range(8):
        for j in range(i,8):
            m = np.zeros((8,8),dtype=np.int64)
            m[i,j] = m[j,i] = 1
            basis.append(m)
    residuals = np.einsum("aij,bkl,ikjl->ab",basis,basis,delta16,optimize=True)
    assert residuals.size==1296 and not residuals.any()
    k = J.astype(int)
    joint = -np.kron(k,k)
    omega4 = np.eye(4,dtype=int)+joint
    assert (joint @ joint == np.eye(4)).all() and np.trace(omega4 @ joint)==4
    # Two independent copies. The real symmetric local signs J1*J2 have zero
    # marginal mean; the joint product reveals the square of the hidden moment.
    local = np.kron(k,k)
    two = np.kron(omega4,omega4).reshape((2,)*8)
    perm = (0,2,1,3,4,6,5,7)
    two = two.transpose(perm).reshape(16,16)
    assert np.trace(two @ np.kron(local,local))==16
    assert np.trace(two @ np.kron(local,np.eye(4)))==0
    assert np.trace(two @ np.kron(np.eye(4),local))==0
    return dict(full_source_symmetric_basis_pairs=1296, max_integer_residual=0,
                real_distance_to_separable_at_v1=.5, two_iid_copy_correlation_at_v1=1)


def leakage_attacks():
    # Share fair b and outer output bit i in advance. A ternary hidden guess g
    # is independent and uniform unless explicitly set equal to x.
    accepted = np.zeros((3,6,2,4,2))
    completed = np.zeros_like(accepted)
    leaked = np.zeros_like(accepted)
    for x,z in np.ndindex(3,6):
        for i,b in product(range(2),range(4)):
            for guess in range(3):
                j = i ^ int(weight(guess,z,b)<0)
                if guess==x:
                    accepted[x,z,i,b,j] += 1/24
                completed[x,z,i if guess==x else 0,b,j] += 1/24
            # C receives x before output (or lambda predicts that setting).
            j = i ^ int(weight(x,z,b)<0)
            leaked[x,z,i,b,j] += 1/8
    eta = accepted.sum(axis=(2,3,4))
    np.testing.assert_allclose(eta,1/3,atol=1e-14,rtol=0)
    kept = accepted/eta[:,:,None,None,None]
    np.testing.assert_allclose(kept,leaked,atol=1e-14,rtol=0)
    np.testing.assert_allclose(scores(kept),3*np.ones(4),atol=1e-14,rtol=0)
    all_score = float(scores(completed).sum())
    assert all_score <= 6+1e-14
    return dict(postselected_T=12, joint_detection_each_setting="1/3",
                T_after_default_assignment=all_score, ternary_message_T=12,
                perfect_setting_prediction_T=12, setting_TV="2/3")


def thresholds(lower):
    """One error source at a time; lower is an independently valid score lower bound."""
    return dict(L=lower, d_separable_max=(lower-R)/(2*Q),
                mean_setting_TV_max=(lower-R)/24,
                flag_for_unrestricted_channel_max=(lower-R)/(12-R),
                nonseparable_quantum_flag_max=(lower-R)/(Q-R),
                min_joint_acceptance_required=(12+R)/(12+lower))


def results():
    from kg_review import review
    here = Path(__file__).resolve().parent
    return dict(status="PASS", baseline="940541cd464d8bccb9f7c553dbd3ebfefde596b7",
                code_sha256={n:hashlib.sha256((here/n).read_bytes()).hexdigest()
                             for n in ("replay.py","kg_review.py")},
                real_reference=check_reference(), source_tests=operational_independence(),
                loopholes=leakage_attacks(), KG=review(),
                design_example=thresholds(7.74))


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Enable assertions for this verifier")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check",action="store_true")
    args = parser.parse_args()
    current = results()
    if args.check:
        archived = json.loads(Path(__file__).with_name("observed.json").read_text())
        def compare(a,b):
            if isinstance(a,dict):
                assert a.keys()==b.keys()
                for key in a:
                    compare(a[key],b[key])
            elif isinstance(a,list):
                assert len(a)==len(b)
                for u,v in zip(a,b):
                    compare(u,v)
            elif isinstance(a,float):
                np.testing.assert_allclose(a,b,rtol=0,atol=1e-12)
            else:
                assert a==b
        compare(current,archived)
        print("PASS: 288 joint cells, 1296 single-copy source tests, two-copy control, losses and both KG points")
    else:
        print(json.dumps(current,indent=2,allow_nan=False))
