"""Exact block structure plus finite-dimensional numerical regression."""
import numpy as np
from scipy.linalg import expm
from common import finish,require,load
old='physics/qm/null_source/timelike/finite_stress/lapse_boundary/relational_coupled/all_sign_evolution.json'
load(old)
E=np.arange(5,dtype=float)+1/120
X=np.array([[0,1],[1,0]],complex)
Z=np.diag([1.,-1.])
I=np.eye(5)
W=np.diag([1.,.5])
H1=np.kron(.4*X,I)+np.kron(W,np.diag(E))
H2=np.kron(.3*Z+.2*X,I)+np.kron(W,np.diag(E))
U=expm(-.21j*H2)@expm(-.17j*H1)
V=expm(-.09j*H1)
mask=np.tile([1,1,1,0,0],2)
P=np.diag(mask)
require(np.linalg.norm(P@U-U@P)<1e-12,'source cutoff commutes')
idx=np.flatnonzero(mask)
H1s=H1[np.ix_(idx,idx)];H2s=H2[np.ix_(idx,idx)]
Us=expm(-.21j*H2s)@expm(-.17j*H1s)
require(np.linalg.norm(Us-U[np.ix_(idx,idx)])<1e-12,'exact block restriction')
rng=np.random.default_rng(20261121)
B=rng.normal(size=(10,4))+1j*rng.normal(size=(10,4))
rho=B@B.conj().T;rho/=np.trace(rho)
prob=float(np.trace(P@rho).real)
rhok=P@rho@P/prob
tracenorm=lambda a:float(np.linalg.svd(a,compute_uv=False).sum())
d=tracenorm(rhok-rho)/2
require(d<=np.sqrt(1-prob)+1e-12,'normal projection distance')
lhs=tracenorm(U@rhok@V.conj().T-U@rho@V.conj().T)
rhs=tracenorm(rhok-rho)
require(abs(lhs-rhs)<1e-12,'two-time exact trace norm identity')
require(np.linalg.eigvalsh(rhok).min()>-1e-12,'normal positive approximation')
require(abs(np.trace(U@rhok@U.conj().T)-1)<1e-12,'slice normalization')
# Complete measurement retains both records.
K0=np.kron(np.diag([1.,0.]),I);K1=np.eye(10)-K0
cq=np.zeros((20,20),complex)
for i,K in enumerate([K0,K1]):
    cq[i*10:(i+1)*10,i*10:(i+1)*10]=K@U@rho@U.conj().T@K
require(abs(np.trace(cq)-1)<1e-12,'complete CQ record')
# A raw propagator glues; a prepared mixed-state kernel does not.
F=np.kron(np.diag([1.,np.sqrt(.5)]),I)
metric=np.kron(np.diag([1.,2.]),I)
require(np.linalg.norm(F@U@F@metric@F@V@F-F@U@V@F)<1e-12,
        'weighted propagator gluing')
prepared_product=F@U@rho@F@metric@F@rho@V.conj().T@F
require(np.linalg.norm(prepared_product-F@U@rho@rho@V.conj().T@F)<1e-12,
        'prepared kernel composition contains rho squared')
require(np.linalg.norm(prepared_product-F@U@rho@V.conj().T@F)>1e-3,
        'mixed density kernel is not idempotent')
finish('joint_continuum.py',{'exact_analytic_cutoff_identity':'U_K P_K=U_infinity P_K',
 'uniform_normal_kernel_error':'||rho_K-rho||_1',
 'regression_dimension':10,'regression_tolerance':1e-12,
 'regression_all_passed':True,'mixed_state_gluing_regression':True,'positive_fixed_physical_test_lower_bound':'q/4',
 'all_normal_inputs_allowed_for_bounded_observables':True,
 'arbitrary_normal_inputs_automatically_Hadamard':False,
 'full_generator_semibounded_claimed':False},inputs=[old])
