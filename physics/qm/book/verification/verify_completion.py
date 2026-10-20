"""Independent finite checks for the unified additions; no experimental data."""
import itertools, json, platform
import numpy as np
import scipy
from scipy.integrate import quad
from scipy.linalg import expm
from scipy.stats import binom

rng=np.random.default_rng(9062048)
checks=[];metrics={}
def test(name,ok):
    if not bool(ok): raise AssertionError(name)
    checks.append(name)
def close(name,a,b,tol=1e-10):
    test(name,np.max(np.abs(np.asarray(a)-np.asarray(b)))<tol)

# Spectral gauge transport and flux periodicity, not finite exact CCR.
n=np.arange(-8,9);hbar=1.3;L=2.1;m=.7;q=.8
for j in range(5):
    theta,A,chi=rng.normal(size=3)
    energy=lambda th,aa: (hbar*(2*np.pi*n+th)/L-q*aa)**2/(2*m)
    close(f"ring_gauge_transport_{j}",energy(theta,A),energy(theta+q*chi*L/hbar,A+chi))
    close(f"ring_spectral_relabel_{j}",energy(theta+2*np.pi,A)[:-1],energy(theta,A)[1:])
close("Berry_Chern_integral",quad(lambda t:-.5*np.sin(t),0,np.pi)[0],-1)
for theta in [.2,.9,2.5]:
    close(f"Berry_patch_difference_{theta}",.5*(1+np.cos(theta))+.5*(1-np.cos(theta)),1)

for ratio in [.2,.7,1.4,2.0]:
    k=np.linspace(-np.pi,np.pi,10001)
    z=ratio+np.exp(-1j*k)
    winding=(np.unwrap(np.angle(z))[-1]-np.unwrap(np.angle(z))[0])/(2*np.pi)
    close(f"SSH_winding_{ratio}",winding,-1 if ratio<1 else 0)
for N,r in [(8,.4),(12,.7),(24,.8)]:
    H=np.zeros((2*N,2*N))
    for j in range(N):
        H[2*j,2*j+1]=H[2*j+1,2*j]=r
        if j+1<N:H[2*j+1,2*j+2]=H[2*j+2,2*j+1]=1.
    norm=np.sqrt((1-r*r)/(1-r**(2*N)))
    psi=np.zeros(2*N);psi[::2]=norm*(-r)**np.arange(N)
    residual=norm*r**N
    close(f"SSH_normalization_{N}",np.linalg.norm(psi),1)
    close(f"SSH_finite_residual_{N}",np.linalg.norm(H@psi),residual)
    test(f"SSH_near_zero_spectrum_{N}",min(abs(np.linalg.eigvalsh(H)))<=residual+1e-12)

# Direct noncommutative plaquette gauge covariance using SU(2) matrices.
pauli=[np.array([[0,1],[1,0]]),np.array([[0,-1j],[1j,0]]),np.diag([1,-1])]
def su2():
    v=rng.normal(size=3)
    return expm(1j*sum(v[i]*pauli[i] for i in range(3)))
for j in range(12):
    U=[su2() for _ in range(4)];G=[su2() for _ in range(4)]
    transformed=[G[k]@U[k]@G[(k+1)%4].conj().T for k in range(4)]
    prod=lambda a:a[0]@a[1]@a[2]@a[3]
    close(f"plaquette_gauge_covariance_{j}",prod(transformed),G[0]@prod(U)@G[0].conj().T)
    close(f"plaquette_trace_invariance_{j}",np.trace(prod(transformed)),np.trace(prod(U)))
F=(.3*pauli[0]+.7*pauli[2])/2;g=.8
for a in [.1,.05,.025]:
    exact=(1-np.trace(expm(1j*g*a*a*F)).real/2)*4/g**2
    predicted=a**4*np.trace(F@F).real
    test(f"Wilson_continuum_coefficient_{a}",abs(exact-predicted)/predicted<2e-6)

configs=np.array(list(itertools.product([-1,1],repeat=4)))
P=configs.prod(axis=1)
for beta in [0,.2,.7,1.4,3.]:
    weights=np.exp(beta*P);Z=weights.sum()
    close(f"Z2_partition_{beta}",Z,16*np.cosh(beta))
    close(f"Z2_plaquette_{beta}",weights@P/Z,np.tanh(beta))
    close(f"Z2_link_expectation_{beta}",weights@configs/Z,np.zeros(4))
for vertex in range(4):
    gauged=configs.copy();gauged[:,vertex]*=-1;gauged[:,(vertex-1)%4]*=-1
    close(f"Z2_vertex_gauge_{vertex}",gauged.prod(axis=1),P)

# Enumerate all histories in a genuinely history-dependent binary model.
p0=.13;ntrial=10;qalt=.02
histories=[((),1.)]
for t in range(ntrial):
    new=[]
    for hist,prob in histories:
        pt=p0+.3*((sum(hist)+t)%3)/2
        new += [(hist+(0,),prob*(1-pt)),(hist+(1,),prob*pt)]
    histories=new
distribution=np.zeros(ntrial+1)
for hist,prob in histories:distribution[sum(hist)]+=prob
close("history_tree_normalization",distribution.sum(),1)
for k in range(ntrial+1):
    test(f"dependent_binomial_domination_{k}",distribution[:k+1].sum()<=binom.cdf(k,ntrial,p0)+1e-12)
for pt in [p0,.3,.7,1.]:
    factor=pt*qalt/p0+(1-pt)*(1-qalt)/(1-p0)
    close(f"supermartingale_conditional_identity_{pt}",factor,1+(pt-p0)*(qalt-p0)/(p0*(1-p0)))
    test(f"supermartingale_factor_{pt}",factor<=1+1e-12)
likelihood=lambda k:(qalt/p0)**k*((1-qalt)/(1-p0))**(ntrial-k)
test("dependent_likelihood_mean",sum(distribution[k]*likelihood(k) for k in range(ntrial+1))<=1+1e-12)
test("marginal_bound_counterexample",1-p0>(1-p0)**ntrial)
pstar=(3-2*np.sqrt(2))/(4*(2+1/np.sqrt(2)))
test("ideal_zero_188_valid",(1-pstar)**188<.05)
test("ideal_zero_187_insufficient",(1-pstar)**187>.05)
metrics.update({"ideal_pstar":pstar,"zero_event_188_pvalue":(1-pstar)**188,
    "Berry_upper_band_Chern":-1,"history_model_zero_probability":distribution[0],
    "history_null_zero_bound":(1-p0)**ntrial})
result={"summary":{"status":"all_passed","checks":len(checks),"seed":9062048,
    "experimental_data":False,"formal_proof_assistant":False},
    "environment":{"python":platform.python_version(),"numpy":np.__version__,"scipy":scipy.__version__},
    "metrics":metrics,"checks":checks}
print(json.dumps(result,ensure_ascii=False,indent=2))
