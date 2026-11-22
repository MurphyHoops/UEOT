"""Run all network controls; --table LABEL prints the full x,z,a,b,c table."""
import argparse
import hashlib
from itertools import product
import json
from pathlib import Path
import sys

import numpy as np
import network as net


def factorization():
    # A source side has 8 dimensions. Integer basis spanning every real symmetric effect.
    sym = []
    for i in range(8):
        for j in range(i,8):
            m = np.zeros((8,8), dtype=int)
            m[i,j] = m[j,i] = 1
            sym.append(m)
    J = net.J.astype(int)
    tau4 = np.eye(4,dtype=int) - np.kron(J,J)
    # Balanced phase quotient: on its two-real-dimensional representative subspace
    # J on either factor has the same action. This is an algebra check, not a new source.
    phase_difference = np.kron(J,np.eye(2,dtype=int))-np.kron(np.eye(2,dtype=int),J)
    assert np.count_nonzero(phase_difference@tau4)==0 and np.linalg.matrix_rank(tau4)==2
    tau = tau4/4
    assert np.array_equal(np.linalg.eigvalsh(tau), [0,0,.5,.5])
    ref = net.reference_state(tau)
    independent = net.reference_state(np.eye(4)/4)
    scaled = 16*(ref-independent)
    exact = np.rint(scaled).astype(int)
    assert np.max(np.abs(scaled-exact)) < 1e-13
    # Construct the same signed difference directly as exact embedded -J x J /16.
    lift_l, lift_r = [np.zeros((8,2),dtype=int) for _ in range(2)]
    for flag, bit in product(range(2), repeat=2):
        lift_l[4*bit+2*flag+bit,flag] = 1   # A F B1
        lift_r[4*bit+2*bit+flag,flag] = 1   # B2 C G
    assert np.array_equal(exact,-np.kron(lift_l@J@lift_l.T,lift_r@J@lift_r.T))
    residual = np.einsum('ijkl,aki,blj->ab',exact.reshape(8,8,8,8),sym,sym,optimize=True)
    assert np.count_nonzero(residual)==0
    witness = np.kron(J,J)
    assert np.trace(tau4@witness)==-4 and np.max(abs(np.linalg.eigvalsh(witness)))==1
    assert np.abs(np.linalg.eigvalsh(tau-np.eye(4)/4)).sum()/2 == .5
    # Two independently prepared copies. Group flags F1 F2 | G1 G2.
    two = np.kron(tau,tau).reshape((2,)*8).transpose(0,2,1,3,4,6,5,7).reshape(16,16)
    local = -witness  # Y x Y, a real symmetric involution at each endpoint
    assert np.array_equal(local.T,local) and np.array_equal(local@local,np.eye(4))
    joint = np.trace(two@np.kron(local,local))
    assert joint==1 and np.trace(two@np.kron(local,np.eye(4)))==0
    assert np.trace(two@np.kron(np.eye(4),local))==0
    # Equally weighted real product Bell-link preparations with a shared classical flag.
    classical = np.diag([.5,0,0,.5])
    dprod = np.abs(np.linalg.eigvalsh(classical-np.eye(4)/4)).sum()/2
    assert dprod==.5
    return dict(full_source_side_dim=8,product_basis_pairs=len(sym)**2,integer_max_residual=0,
                phase_quotient_real_flag_dimension=2,
                shared_phase_reference_distance_to_real_separable=.5,
                iid_two_copy_local_YY_means=[0,0],iid_two_copy_joint_YY=int(joint),
                classical_shared_bit_distance_to_marginal_product=dprod,
                classical_shared_bit_distance_to_real_separable=0)


def verify():
    tables=net.candidate_tables()
    ideal=tables['complex_independent']
    # Closed form depending on signed Bell correlation tensor and Charlie's axis vector.
    full=np.zeros_like(ideal)
    for b,(sz,sx,sy) in enumerate(((1,1,-1),(-1,1,1),(1,-1,1),(-1,-1,-1))):
        diag=(sz,sx,sy)
        for z,(i,j) in enumerate(((0,1),(0,1),(0,2),(0,2),(1,2),(1,2))):
            for x, a, c in product(range(3),range(2),range(2)):
                coeff=diag[x]*((x==i)+(-1)**z*(x==j))/np.sqrt(2)
                full[x,z,a,b,c]=(1+(-1)**(a+c)*coeff)/16
    assert np.max(abs(full-ideal))<1e-14
    assert np.max(abs(ideal-tables['real_shared_reference']))<1e-14
    checked={}
    for name, expected in zip(net.LABELS,[6,4+2*np.sqrt(2),6*np.sqrt(2),6*np.sqrt(2)]):
        p=tables[name]
        t, branches=net.score(p)
        assert abs(t-expected)<2e-14
        ab=p.sum(axis=4)
        bc=p.sum(axis=2)
        assert np.max(abs(ab-ab[:,0:1]))<1e-14 and np.max(abs(bc-bc[:1]))<1e-14
        checked[name]=dict(T=t,T_b=branches,normalized_settings=18,probabilities=p.size)
    independent=net.with_flags(np.eye(4)/4)
    assert abs(net.score(independent)[0]-4*np.sqrt(2))<1e-13
    # Twirling of independent Bell links and an actual reversal of the two Bob label bits.
    v=.95
    noisy=v*net.BSM[0]+(1-v)*np.eye(4)/4
    noisy_t=net.score(net.probabilities(np.kron(noisy,noisy)))[0]
    assert abs(noisy_t-v*v*6*np.sqrt(2))<1e-13
    swapped=net.score(ideal[:,:,:,[0,2,1,3],:])[0]
    assert abs(swapped-2*np.sqrt(2))<1e-13
    # Independent trace with a complex noisy input so imaginary/transposed entries are tested.
    rng=np.random.default_rng(1701)
    v=rng.normal(size=16)+1j*rng.normal(size=16)
    rho=.8*np.outer(v,v.conj())/(v.conj()@v)+.2*np.eye(16)/16
    p=net.probabilities(rho)
    err=0.
    for x,z,a,b,c in np.ndindex(p.shape):
        effect=np.kron(np.kron(net.effects(net.AXES)[x,a],net.BSM[b]),net.effects(net.CHARLIE)[z,c])
        err=max(err,abs(np.trace(rho@effect)-p[x,z,a,b,c]))
    assert err<1e-14
    gap=6*np.sqrt(2)-7.6605
    return dict(candidates=checked,ideal_formula_max_error=float(np.max(abs(full-ideal))),
                shared_reference_max_probability_error=float(np.max(abs(ideal-tables['real_shared_reference']))),
                random_complex_state_direct_trace_max_error=float(err),independent_reference_T=net.score(independent)[0],
                interchanged_Bob_bits_T=swapped,both_visibilities_095_T=noisy_t,
                ideal_TV_threshold_if_literature_E4=gap/24,
                equal_visibility_threshold_if_literature_E4=np.sqrt(7.6605/(6*np.sqrt(2))),
                reference_and_source_cut=factorization())


def main():
    if not __debug__:
        raise RuntimeError("enable assertions")
    ap=argparse.ArgumentParser()
    ap.add_argument('--table',choices=net.LABELS)
    label=ap.parse_args().table
    if label:
        print(json.dumps(net.candidate_tables()[label].tolist(),allow_nan=False))
        return
    here=Path(__file__).resolve().parent
    summary=verify()
    print(json.dumps(dict(baseline='940541cd464d8bccb9f7c553dbd3ebfefde596b7',
                          python=sys.version.split()[0],numpy=np.__version__,
                          sha256={f:hashlib.sha256((here/f).read_bytes()).hexdigest()
                                  for f in ('CONTRACT.md','network.py','verify.py')},
                          results=summary),indent=2,allow_nan=False))


if __name__=='__main__':
    main()
