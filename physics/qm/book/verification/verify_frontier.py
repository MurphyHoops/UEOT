"""Independent checks for UEOT physics frontier. No experimental data."""
import json, math, platform
from fractions import Fraction as F
import numpy as np
import scipy
from scipy.linalg import expm
from scipy.special import logsumexp
from scipy.stats import binom

rng=np.random.default_rng(9062026)
checks=[];metrics={}
def test(name,truth,detail=None):
    if not bool(truth):raise AssertionError((name,detail))
    checks.append({"name":name,"passed":True})
def close(name,a,b,tol=1e-10):
    test(name,np.allclose(a,b,atol=tol,rtol=tol),float(np.max(abs(np.asarray(a)-np.asarray(b)))))
def pure(v):return np.outer(v,v.conj())
def td(a,b):return np.linalg.eigvalsh((a-b+(a-b).conj().T)/2).__abs__().sum()/2
def off(a):return a-np.diag(np.diag(a))
def haar(n):
    z=rng.normal(size=(n,n))+1j*rng.normal(size=(n,n))
    q,r=np.linalg.qr(z)
    return q@np.diag(np.diag(r)/abs(np.diag(r)))
def psd(a):return np.linalg.eigvalsh((a+a.conj().T)/2).min()
def anomalies(rows):
    val=[F(0) for _ in range(6)]
    for n,dc,sc,dl,sl,x in rows:
        x=F(x)
        val[0]+=n*dl*sc
        val[1]+=n*dc*sl
        val[2]+=n*dl*(F(1,2) if dc>1 else 0)*x
        val[3]+=n*dc*(F(1,2) if dl>1 else 0)*x
        val[4]+=n*dc*dl*x
        val[5]+=n*dc*dl*x**3
    return val
def spectrum(nc,nf,b):
    k=F((nc-1)*nf,2*nc)
    assert k.denominator==1
    k=int(k)
    qu=F(nc+1,2*nc);qd=-F(nc-1,2*nc)
    xl=-F(1,2)-b/2;xp=F(1,2*nc)-b/2;xm=F(1,2*nc)+b/2
    qe=-F(1,2)-3*b/2;jp=F(1,2*nc)-3*b/2;jm=F(1,2*nc)+3*b/2
    return [(nf,1,0,3,1,xl),(nf,1,0,1,0,1),(nf,1,0,1,0,-qe),
            (k,nc,1,3,1,xp),(nf-k,nc,1,3,-1,xm),
            (nf,nc,-1,1,0,-qu),(nf,nc,-1,1,0,-qd),
            (k,nc,-1,1,0,-jp),(nf-k,nc,-1,1,0,-jm)]
def survivors(ns):
    ans=[]
    for nc in range(3,31):
        for nf in range(1,121):
            if (nc-1)*nf%(2*nc):continue
            bc=F(11*nc,3)-2*nf
            bl=11-F(nf*(nc+1),3)-F(ns,6)
            if bc>0 and bl>0:ans.append((nc,nf,(nc-1)*nf//(2*nc)))
    return ans
for ns in range(46):
    expected=[(3,3,1),(5,5,2)] if ns<=5 else ([(3,3,1)] if ns<=41 else [])
    test(f"UV_integer_classification_ns_{ns}",survivors(ns)==expected)
metrics["UV_three_scalar_survivors"]=survivors(3)
for nc in range(3,11):
    nf=2*nc
    for b in [F(-1),F(-1,3),F(0),F(1,2)]:
        test(f"generalized_complete_anomalies_{nc}_{b}",anomalies(spectrum(nc,nf,b))==[0]*6)
test("five_color_five_family_all_local_anomalies",anomalies(spectrum(5,5,F(-1,3)))==[0]*6)
metrics["five_color_coefficients"]={"bC":str(F(25,3)),"bL":str(F(1,2)),"low_b2":str(F(-17,6))}
# The zero-U(1) anomaly identities fail if generic charged exotic E^c is omitted.
rows=spectrum(5,5,F(0))
test("omitted_charged_Ec_detected",anomalies(rows[:2]+rows[3:])!=[0]*6)

# Flavor, computed through independent mass-basis rotations.
for rep in range(30):
    uu=haar(3);ud=haar(3);P=np.diag([1,0,0]);V=uu.conj().T@ud
    Pu=uu.conj().T@P@uu;Pd=ud.conj().T@P@ud
    close(f"flavor_CKM_transport_{rep}",Pd,V.conj().T@Pu@V)
    close(f"flavor_rank_one_minor_{rep}",Pu[0,1]*Pu[1,2],Pu[0,2]*Pu[1,1])
    close(f"flavor_cycle_real_{rep}",np.imag(Pu[0,1]*Pu[1,2]*Pu[2,0]),0)
    strength=np.linalg.norm(off(Pu))**2+np.linalg.norm(off(Pd))**2
    test(f"flavor_universal_lower_bound_{rep}",strength>=1-abs(V).max()-1e-12)
    C_u=-Pu**2/2;C_d=-Pd**2/2
    test(f"flavor_EFT_coefficient_bound_{rep}",
         np.sum(abs(off(C_u)))+np.sum(abs(off(C_d)))>=(1-abs(V).max())/2-1e-12)
# Illustrative, frozen angles; these are not a fresh fit to data.
t12,t23,t13,delta=.227,.041,.0035,1.2
c12,c23,c13=np.cos([t12,t23,t13]);s12,s23,s13=np.sin([t12,t23,t13])
V=np.array([[c12*c13,s12*c13,s13*np.exp(-1j*delta)],
            [-s12*c23-c12*s23*s13*np.exp(1j*delta),
             c12*c23-s12*s23*s13*np.exp(1j*delta),s23*c13],
            [s12*s23-c12*c23*s13*np.exp(1j*delta),
             -c12*s23-s12*c23*s13*np.exp(1j*delta),c23*c13]])
close("illustrative_CKM_unitarity",V.conj().T@V,np.eye(3))
metrics["illustrative_flavor_lower_bound_over_delta_g_squared"]=float(1-abs(V).max())

# Three-cycle complete positivity, phase loss, and the classical Poisson counterexample.
for rep in range(24):
    L=rng.normal(size=(3,2))+1j*rng.normal(size=(3,2))
    G=L@L.conj().T;di=np.diag(G).real;h=rng.normal(size=3)
    lam=G-(di[:,None]+di[None,:])/2-1j*(h[:,None]-h[None,:])
    rates=-lam.real
    omega=(lam[0,1]+lam[1,2]+lam[2,0]).imag
    bound=4*rates[0,2]*rates[1,2]-(rates[0,2]+rates[1,2]-rates[0,1])**2
    test(f"cycle_sharp_CP_{rep}",omega**2<=bound+1e-10)
    total=rates[0,1]+rates[1,2]+rates[2,0]
    test(f"cycle_phase_loss_{rep}",total>=np.sqrt(3)*abs(omega)-1e-10)
    K=np.exp(.3*lam)
    test(f"cycle_finite_CP_{rep}",psd(K)>-1e-10)
    determinant=1-abs(K[0,1])**2-abs(K[1,2])**2-abs(K[2,0])**2+2*np.real(K[0,1]*K[1,2]*K[2,0])
    close(f"cycle_determinant_identity_{rep}",determinant,np.linalg.det(K))
theta=np.array([0,2*np.pi/3,4*np.pi/3])
lam=np.exp(1j*(theta[:,None]-theta[None,:]))-1
omega=(lam[0,1]+lam[1,2]+lam[2,0]).imag
close("Poisson_saturates_phase_loss",sum(-lam.real[i,(i+1)%3] for i in range(3)),np.sqrt(3)*abs(omega))
test("Poisson_nonzero_cycle",abs(omega)>2)
metrics["classical_Poisson_cycle"]=float(omega)
bad=np.array([[0,-1+2j,-1],[-1-2j,0,-1],[-1,-1,0]])
test("excess_cycle_not_CP",psd(np.exp(.001*bad))<-1e-6)

# Four-level channel and witness.
V=np.array([[1,0],[0,1],[1,1],[1,1j]],complex);V[2:]/=np.sqrt(2)
K=V@V.conj().T
B=np.array([[-1/np.sqrt(2),-1/np.sqrt(2),1,0],
            [-1/np.sqrt(2),-1j/np.sqrt(2),0,1]],complex)
W=B.conj().T@B;kappa=3-2*np.sqrt(2);wmax=2+1/np.sqrt(2);E=W/wmax
close("four_level_nullspace",B@V,np.zeros((2,2)))
close("four_level_witness_zero",np.trace(W@K),0)
close("witness_frobenius",np.linalg.norm(W),3)
close("witness_operator_norm",np.linalg.eigvalsh(W).max(),wmax)
test("effect_valid",psd(E)>-1e-12 and psd(np.eye(4)-E)>-1e-12)
ks=[np.diag(V[:,mu]) for mu in range(2)]
close("four_level_Kraus_TP",sum(a.conj().T@a for a in ks),np.eye(4))
psi=np.ones(4)/2;rho=pure(psi)
out=sum(a@rho@a.conj().T for a in ks)
close("four_level_output",out,K/4)
joint=np.zeros((8,4),complex)
for a in range(4):joint[a*2:(a+1)*2,a]=V[a]
close("joint_isometry",joint.conj().T@joint,np.eye(4))
jointstate=joint@rho@joint.conj().T
reduced=np.einsum("abcb->ac",jointstate.reshape(4,2,4,2))
close("environment_dilation",reduced,out)
zsat=np.array([1,1,1,(1+1j)/np.sqrt(2)])
close("classical_bound_attained",np.vdot(zsat,W@zsat),kappa)
min_random=1e9
for rep in range(20):
    zz=np.exp(1j*rng.uniform(-np.pi,np.pi,size=(5000,4)))
    vals=np.einsum("ni,ij,nj->n",zz.conj(),W,zz).real
    min_random=min(min_random,float(vals.min()))
    test(f"classical_witness_random_batch_{rep}",vals.min()>=kappa-1e-12)
for eps in [0,.01,.04,kappa/4,.08,1]:
    Ke=(1-eps)*K+eps*np.eye(4)
    close(f"mixture_witness_{eps}",np.trace(W@Ke),4*eps)
pcl=kappa/(4*wmax)
n=math.ceil(math.log(.05)/math.log(1-pcl))
test("zero_event_exact_n",n==188)
test("zero_event_size",binom.cdf(0,n,pcl)<=.05)
test("one_less_shot_insufficient",binom.cdf(0,n-1,pcl)>.05)
metrics["four_level"]={"kappa":kappa,"p_classical_min":pcl,"ideal_zero_event_n95":n,
                      "noise_mixture_threshold":kappa/4,"random_min_witness":min_random,
                      "classical_pvalue_zero_188":float(binom.cdf(0,n,pcl)),
                      "population_leakage_positive_bound_limit":pcl**2/8}
# Verify the approximate population-preserving random-unitary bound on genuine unitary samples.
for rep in range(12):
    us=[]
    for j in range(4):
        h=rng.normal(size=(4,4))+1j*rng.normal(size=(4,4));h=(h+h.conj().T)/2
        us.append(expm(-1j*.002*h))
    weights=rng.dirichlet(np.ones(4))
    surv=sum(p*abs(np.diag(u))**2 for p,u in zip(weights,us))
    ell=1-surv.min()
    rout=sum(p*u@rho@u.conj().T for p,u in zip(weights,us))
    ds=[np.diag(np.diag(u)/abs(np.diag(u))) for u in us]
    rdiag=sum(p*d@rho@d.conj().T for p,d in zip(weights,ds))
    test(f"approximate_RU_distance_{rep}",td(rout,rdiag)<=np.sqrt(8*ell)+1e-12)
    test(f"approximate_RU_effect_{rep}",np.trace(E@rout).real>=pcl-np.sqrt(8*ell)-1e-12)

# Nonlinear ensemble inconsistency.
x1=.8*np.exp(-1)+.2*(-np.exp(-1))
x2=.5*.6*np.exp(-.36)+.5*.6*np.exp(-.36)
close("initial_ensemble_same_bloch",.8-.2,.6)
close("signalling_probability_difference",(x2-x1)/2,.0989390654698766)
metrics["nonlinear_signal_probability_difference"]=(x2-x1)/2

# Exact physical filtering sampler, no Euler step or negative probabilities.
p0=np.array([.2,.3,.5]);aval=np.array([-1.,.2,1.3]);gamma=.7;nsamp=120000
v0=np.dot(p0,aval**2)-np.dot(p0,aval)**2
filter_metrics=[]
for t in [.2,1.,4.]:
    labels=rng.choice(3,size=nsamp,p=p0)
    yt=2*np.sqrt(gamma)*aval[labels]*t+np.sqrt(t)*rng.normal(size=nsamp)
    logs=np.log(p0)[None,:]+2*np.sqrt(gamma)*yt[:,None]*aval-2*gamma*aval**2*t
    pp=np.exp(logs-logsumexp(logs,axis=1)[:,None])
    close(f"filter_normalization_{t}",pp.sum(axis=1),np.ones(nsamp))
    for a in range(3):
        stderr=pp[:,a].std(ddof=1)/np.sqrt(nsamp)
        test(f"filter_Born_martingale_{t}_{a}",abs(pp[:,a].mean()-p0[a])<=6*stderr+1e-4)
    bound=0.
    for a in range(3):
        for b in range(a+1,3):
            samples=np.sqrt(pp[:,a]*pp[:,b])
            theory=np.sqrt(p0[a]*p0[b])*np.exp(-gamma*(aval[a]-aval[b])**2*t/2)
            stderr=samples.std(ddof=1)/np.sqrt(nsamp)
            test(f"filter_pair_decay_{t}_{a}_{b}",abs(samples.mean()-theory)<=6*stderr+1e-4)
            bound+=theory
    variance=pp@(aval**2)-(pp@aval)**2
    test(f"filter_variance_bound_{t}",variance.mean()<=v0/(1+4*gamma*v0*t)+.004)
    err=1-pp.max(axis=1)
    test(f"filter_localization_bound_{t}",err.mean()<=bound+.002)
    filter_metrics.append({"t":t,"mean_p":pp.mean(axis=0).tolist(),
        "mean_variance":float(variance.mean()),"mean_unresolved":float(err.mean()),
        "proved_unresolved_bound":float(bound)})
metrics["exact_filtering"]=filter_metrics
# Heating commutator checked on an interior state, not as false full finite CCR.
a=np.diag(np.sqrt(np.arange(1,12)),1);q=(a+a.T)/np.sqrt(2);p=(a-a.T)/(1j*np.sqrt(2))
H=(p@p+q@q)/2
comm=lambda x,y:x@y-y@x
close("position_noise_heating_interior",-comm(q,comm(q,H))[0,0]/2,.5)
result={"summary":{"status":"all_passed","checks":len(checks),"seed":9062026,
        "experimental_data":False,"formal_proof_assistant":False},
        "environment":{"python":platform.python_version(),"numpy":np.__version__,"scipy":scipy.__version__},
        "metrics":metrics,"checks":checks}
print(json.dumps(result,ensure_ascii=False,indent=2))

