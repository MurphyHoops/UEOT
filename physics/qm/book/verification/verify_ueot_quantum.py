"""UEOT quantum master: deterministic finite/numerical regression, not formal proof."""
import json
import math
import platform
from fractions import Fraction as F
import numpy as np
import scipy
from scipy.linalg import expm, logm
from scipy.integrate import quad, dblquad
from numpy.polynomial.legendre import leggauss

rng = np.random.default_rng(31011)
checks = []
metrics = {}
I = np.eye(2, dtype=complex)
X = np.array([[0, 1], [1, 0]], complex)
Y = np.array([[0, -1j], [1j, 0]], complex)
Z = np.diag([1, -1]).astype(complex)
paulis = [I, X, Y, Z]

def check(name, value, detail=None):
    ok = bool(value)
    checks.append({"name": name, "passed": ok})
    if not ok:
        raise AssertionError((name, detail))

def close(name, a, b, atol=1e-10, rtol=1e-9):
    check(name, np.allclose(a, b, atol=atol, rtol=rtol),
          float(np.max(np.abs(np.asarray(a)-np.asarray(b)))))

def state(d):
    a = rng.normal(size=(d,d)) + 1j*rng.normal(size=(d,d))
    a = a@a.conj().T
    return a/np.trace(a)

def pure(v):
    return np.outer(v, np.conj(v))

def apply(ks, rho):
    return sum(k@rho@k.conj().T for k in ks)

def trace_out_second(rho, da, db):
    return np.einsum("abcb->ac",rho.reshape(da,db,da,db))

def td(a,b):
    return float(np.sum(np.abs(np.linalg.eigvalsh((a-b+(a-b).conj().T)/2)))/2)

def choi(ks):
    d = ks[0].shape[1]
    blocks = []
    for i in range(d):
        row = []
        for j in range(d):
            e = np.zeros((d,d),complex); e[i,j] = 1
            row.append(apply(ks,e))
        blocks.append(row)
    return np.block(blocks)

def herm_min(a):
    return float(np.linalg.eigvalsh((a+a.conj().T)/2).min())

# Complex channel construction and input-first Choi reconstruction.
for rep in range(12):
    z = rng.normal(size=(6,2))+1j*rng.normal(size=(6,2))
    v,_ = np.linalg.qr(z)
    ks = [v[i*2:(i+1)*2] for i in range(3)]
    j = choi(ks); rho = state(2)
    close(f"channel_TP_{rep}",sum(k.conj().T@k for k in ks),I)
    check(f"channel_Choi_PSD_{rep}",herm_min(j)>-1e-12)
    close(f"channel_Choi_partial_trace_{rep}",trace_out_second(j,2,2),I)
    product = np.kron(rho.T,I)@j
    recovered = np.einsum("iaib->ab",product.reshape(2,2,2,2))
    close(f"channel_reconstruction_{rep}",recovered,apply(ks,rho))
    sig=state(2)
    check(f"channel_trace_contraction_{rep}",
          td(apply(ks,rho),apply(ks,sig)) <= td(rho,sig)+1e-12)

bell=np.array([1,0,0,1],complex)/np.sqrt(2)
bellrho=pure(bell)
pt=bellrho.reshape(2,2,2,2).transpose(0,3,2,1).reshape(4,4)
close("transpose_nonCP_eigenvalue",np.linalg.eigvalsh(pt).min(),-0.5)
rho=state(2)
r=[np.trace(rho@s).real for s in [X,Y,Z]]
close("Pauli_state_tomography",rho,(I+sum(a*s for a,s in zip(r,[X,Y,Z])))/2)

# Rebit deletion witness.
rplus=(np.eye(4)+np.kron(Y,Y))/4
rminus=(np.eye(4)-np.kron(Y,Y))/4
check("rebit_positive",min(herm_min(rplus),herm_min(rminus))>-1e-12)
check("rebit_distinct_real",td(rplus,rminus)>0.99 and np.max(abs(rplus.imag))<1e-12)
for aidx,a in enumerate([I,X,Z]):
    for bidx,b in enumerate([I,X,Z]):
        close(f"rebit_local_blind_{aidx}_{bidx}",np.trace((rplus-rminus)@np.kron(a,b)),0)

# Coherent write / public records / inverse write.
cnot=np.array([[1,0,0,0],[0,1,0,0],[0,0,0,1],[0,0,1,0]],complex)
initial=pure(np.array([1,0,1,0],complex)/np.sqrt(2))
written=cnot@initial@cnot
public=sum(p@written@p for p in [np.diag([1,1,0,0]),np.diag([0,0,1,1])])
close("write_isometry",written,bellrho)
close("public_record_probabilities",np.diag(written),np.diag(public))
close("coherent_parent_distinguishability",td(written,public),0.5)
close("inverse_write_exact",cnot@written@cnot,initial)
close("inverse_write_dephased_X",np.trace((cnot@public@cnot)@np.kron(X,I)),0)

# SRN Gram kernel, block-scalar Kraus, phase-sensitive tomography.
m=3
env=rng.normal(size=(m,4))+1j*rng.normal(size=(m,4))
env/=np.linalg.norm(env,axis=1)[:,None]
K=env@env.conj().T
dims=[2,1,2]; labels=np.repeat(np.arange(m),dims)
ks=[np.diag(env[labels,mu]) for mu in range(4)]
rho=state(5)
expected=K[labels[:,None],labels[None,:]]*rho
close("SRN_block_Kraus_Schur",apply(ks,rho),expected)
for a in range(m):
    idx=np.where(labels==a)[0]
    rr=np.zeros((5,5),complex)
    rr[np.ix_(idx,idx)]=state(len(idx))
    close(f"SRN_fixes_branch_internal_{a}",apply(ks,rr),rr)
close("SRN_composition",apply(ks,apply(ks,rho)),
      (K*K)[labels[:,None],labels[None,:]]*rho)
for a in range(m):
    for b in range(a+1,m):
        for phase in [0,np.pi/2]:
            v=np.zeros(m,complex);v[a]=1/np.sqrt(2);v[b]=np.exp(1j*phase)/np.sqrt(2)
            out=K*pure(v)
            xx=np.zeros((m,m),complex);xx[a,b]=xx[b,a]=1
            close(f"QDRR_phase_{a}_{b}_{phase:.3f}",
                  np.trace(xx@out).real,(np.exp(-1j*phase)*K[a,b]).real)
n=math.ceil(2*math.log(2*m*(m-1)/0.05)/0.12**2)
metrics["QDRR_shots_per_pair_phase"]=n
check("QDRR_sample_count",n==762)

for rep in range(12):
    u=rng.normal(size=(4,3))+1j*rng.normal(size=(4,3))
    G=u@u.conj().T; diag=G.diagonal().real
    theta=rng.normal(size=4)
    lam=G-(diag[:,None]+diag[None,:])/2+1j*(theta[:,None]-theta[None,:])
    C=np.eye(4)-np.ones((4,4))/4
    check(f"SRN_generator_CPSD_{rep}",herm_min(C@lam@C)>-1e-10)
    kt=np.exp(0.4*lam)
    check(f"SRN_generator_exponential_PSD_{rep}",herm_min(kt)>-1e-10)
    close(f"SRN_generator_diagonal_{rep}",kt.diagonal(),np.ones(4))
bad=np.array([[0,-1,-1],[-1,0,-10],[-1,-10,0]],float)
z=np.array([2,-1,-1])
close("invalid_generator_quadratic",z@bad@z,-12)
check("invalid_generator_fails_CP",herm_min(np.exp(0.001*bad))<0)

# Finite CV boundary, Gaussian, spin, Bell and control.
N=9
a=np.diag(np.sqrt(np.arange(1,N)),1)
close("truncated_CCR_boundary",a@a.T-a.T@a,
      np.eye(N)-N*np.diag([0]*(N-1)+[1]))
q=(a+a.T)/np.sqrt(2);p=(a-a.T)/(1j*np.sqrt(2))
close("oscillator_vacuum_uncertainty",(q@q)[0,0]*(p@p)[0,0],0.25)
Omega=np.array([[0,1],[-1,0]],float)
check("Gaussian_vacuum_covariance",herm_min(np.eye(2)/2+1j*Omega/2)>-1e-12)
check("Gaussian_subvacuum_rejected",herm_min(np.eye(2)*0.2+1j*Omega/2)<0)
eta=.7
check("Gaussian_loss_CP",herm_min((1-eta)*np.eye(2)/2+
      1j*(Omega-eta*Omega)/2)>-1e-12)
for t in [.1,.7,1.5]:
    H=(.8*X+.6*Z)/2
    u=expm(-1j*H*t)
    close(f"Rabi_{t}",abs(u[1,0])**2,.8**2*np.sin(t/2)**2)
close("spin_commutator",(X@Y-Y@X)/4,1j*Z/2)
close("spin_time_reversal_square",(1j*Y)@(1j*Y).conj(),-I)
B=np.kron(Z,(Z+X)/np.sqrt(2))+np.kron(Z,(Z-X)/np.sqrt(2))+np.kron(X,(Z+X)/np.sqrt(2))-np.kron(X,(Z-X)/np.sqrt(2))
close("CHSH_Tsirelson",np.vdot(bell,B@bell),2*np.sqrt(2))
Hs=(np.kron(X,X)+np.kron(Y,Y)+np.kron(Z,Z))/4
close("Heisenberg_spectrum",np.linalg.eigvalsh(Hs),[-.75,.25,.25,.25])
H=.3*X+.4*Z; O=Z; psi=np.array([1,0],complex); T=.7
U=expm(-1j*H*T); psit=U@psi
chi=U.conj().T@O@psit
# integrated derivative for constant pulse, compared to central finite difference
def grad_integrand(t):
    pt=expm(-1j*H*t)@psi
    ct=expm(-1j*H*(T-t)).conj().T@O@psit
    return 2*np.imag(np.vdot(ct,X@pt))
g=quad(grad_integrand,0,T)[0]
def objective(e):
    v=expm(-1j*(H+e*X)*T)@psi
    return np.vdot(v,O@v).real
close("control_gradient_sign",g,(objective(1e-6)-objective(-1e-6))/2e-6,atol=1e-8)

# Open dynamics, KMS, causal breaks, thermodynamics.
eta=np.exp(-.7)
damp=[np.diag([1,np.sqrt(eta)]),np.array([[0,np.sqrt(1-eta)],[0,0]])]
close("amplitude_damping_TP",sum(k.conj().T@k for k in damp),I)
close("amplitude_damping_population",apply(damp,np.diag([0,1]))[1,1],eta)
beta=.8; H=np.diag([0,1.3]); th=expm(-beta*H);th/=np.trace(th)
A=X+.2*Z; BB=Y+.3*X; t=.4
def tau(t):
    return expm(1j*H*t)@BB@expm(-1j*H*t)
close("Gibbs_KMS_complex_boundary",np.trace(th@A@tau(t+1j*beta)),
      np.trace(th@tau(t)@A))
def relent(r,s):
    return np.trace(r@(logm(r)-logm(s))).real
def entropy(r):
    ev=np.linalg.eigvalsh(r);ev=ev[ev>1e-14]
    return -np.sum(ev*np.log(ev))
rho=state(2)
free=lambda r:np.trace(r@H).real-entropy(r)/beta
close("Gibbs_free_energy_identity",free(rho)-free(th),relent(rho,th)/beta)
relax=lambda r:.63*r+.37*th*np.trace(r)
check("relative_entropy_stationary_contraction",relent(relax(rho),th)<=relent(rho,th)+1e-12)
# causal break resets S, leaves previous record in E; then E controls S
reverse=np.array([[1,0,0,0],[0,0,0,1],[0,0,1,0],[0,1,0,0]],complex)
outs=[]
for bit in [0,1]:
    inp=np.zeros(4);inp[2*bit]=1
    joint=cnot@pure(inp)@cnot
    env=np.einsum("abad->bd",joint.reshape(2,2,2,2))
    reset=np.kron(np.diag([1,0]),env)
    final=reverse@reset@reverse
    outs.append(trace_out_second(final,2,2))
close("causal_break_memory_witness",td(*outs),1)

# Clifford and Dirac mass shell.
zero=np.zeros((2,2),complex)
gam=[np.block([[I,zero],[zero,-I]])]
gam += [np.block([[zero,s],[-s,zero]]) for s in [X,Y,Z]]
metric=[1,-1,-1,-1]
for mu in range(4):
    for nu in range(4):
        close(f"Clifford_{mu}_{nu}",gam[mu]@gam[nu]+gam[nu]@gam[mu],
              2*metric[mu]*np.eye(4) if mu==nu else np.zeros((4,4)))
def slash(v):
    return sum(metric[i]*v[i]*gam[i] for i in range(4))
pp=np.array([np.sqrt(1+.2**2+.3**2),.2,.3,0])
close("Dirac_mass_shell_factorization",(slash(pp)-np.eye(4))@(slash(pp)+np.eye(4)),np.zeros((4,4)))
qq=np.array([.4,.2,-.1,.3])
close("QED_tree_Ward",slash(qq),(slash(pp+qq)-np.eye(4))-(slash(pp)-np.eye(4)))

# Independent numerical spin traces for e+e- -> mu+mu-.
for costh in [-.7,0,.4,.9]:
    E=2.0; st=np.sqrt(1-costh**2)
    p1=np.array([E,0,0,E]);p2=np.array([E,0,0,-E])
    k1=np.array([E,E*st,0,E*costh]);k2=np.array([E,-E*st,0,-E*costh])
    traces=0j
    for mu in range(4):
        for nu in range(4):
            L=np.trace(slash(p2)@gam[mu]@slash(p1)@gam[nu])/4
            R=np.trace(slash(k1)@gam[mu]@slash(k2)@gam[nu])
            traces+=metric[mu]*metric[nu]*L*R
    close(f"QED_scattering_trace_{costh}",traces/(4*E*E)**2,1+costh**2)
alpha=1/137.035999084
sigma=quad(lambda c:2*np.pi*alpha**2/(4*100)*(1+c*c),-1,1)[0]
close("QED_integrated_cross_section",sigma,4*np.pi*alpha**2/300)
metrics["QED_tree_cross_section_inverse_energy_squared"]=sigma

# phi4 renormalization and EFT.
mass=1.3; cutoff=5.0
numeric=quad(lambda q:q**3/(q*q+mass*mass),0,cutoff)[0]/(8*np.pi**2)
closed=(cutoff**2-mass**2*np.log1p(cutoff**2/mass**2))/(16*np.pi**2)
close("phi4_tadpole_radial_integral",numeric,closed)
f=lambda x:np.log((1+x*(1-x)*4)/(1+x*(1-x)*25))/(16*np.pi**2)
bubble=quad(f,0,1,epsabs=1e-13)[0]
gx,gw=leggauss(100)
close("phi4_bubble_two_quadratures",bubble,np.dot(gw,[f((x+1)/2) for x in gx])/2)
close("phi4_bubble_benchmark",bubble,-.006683040905266517)
metrics["phi4_one_loop_F"]=.4-1.5*.4**2*bubble
s=5.;lam=.2;vel=np.sqrt(1-4/s)
im=lam**2*vel/(32*np.pi)
phase=quad(lambda c:vel/(16*np.pi),-1,1)[0]
close("phi4_optical_cut",2*im,lam**2*phase/2)
mass=.7;M=10.;kap=3.;p2=4.
kernel=np.array([[p2-mass**2,-kap],[-kap,p2-M*M]])
schur=kernel[0,0]-kernel[0,1]*kernel[1,0]/kernel[1,1]
close("EFT_Schur_inverse",1/schur,np.linalg.inv(kernel)[0,0])
errors=[]
for order in range(3):
    approx=kap**2/M**2*sum((p2/M**2)**j for j in range(order+1))
    err=abs(kap**2/(M*M-p2)-approx)
    bound=kap**2/M**2*(p2/M**2)**(order+1)/(1-p2/M**2)
    close(f"EFT_remainder_{order}",err,bound)
    errors.append(err)
metrics["EFT_errors_LO_NLO_NNLO"]=errors
def pi_hat(aq):
    return 2*alpha/np.pi*quad(lambda x:x*(1-x)*np.log1p(aq*x*(1-x)),0,1,epsabs=1e-13)[0]
aq=1e-5
close("QED_polarization_IR",pi_hat(aq)/(alpha*aq/(15*np.pi)),1,atol=2e-6)
aq=1e7
close("QED_polarization_UV",pi_hat(aq),alpha/(3*np.pi)*(np.log(aq)-5/3),atol=1e-8)
def threshold(aq):
    return 4*alpha**2/np.pi*quad(lambda x:aq*x*x*(1-x)**2/(1+aq*x*(1-x)),0,1)[0]
close("QED_threshold_UV",threshold(1e7)/(2*alpha**2/(3*np.pi)),1,atol=2e-6)
aq=3.;step=1e-4
close("QED_threshold_derivative",threshold(aq),
      alpha*(pi_hat(aq*np.exp(2*step))-pi_hat(aq*np.exp(-2*step)))/(2*step),
      atol=1e-11)
schwinger=dblquad(lambda y,z:z/(1-z),0,1,lambda z:0,lambda z:1-z)[0]*alpha/np.pi
close("Schwinger_parameter_integral",schwinger,alpha/(2*np.pi))
metrics["Schwinger_one_loop"]=schwinger

# Higgs and seesaw.
g=.65;gp=.36;v=246.
mat=v*v/4*np.array([[g*g,-g*gp],[-g*gp,gp*gp]])
close("Higgs_neutral_eigenvalues",np.linalg.eigvalsh(mat),[0,v*v*(g*g+gp*gp)/4],atol=1e-9)
md=.1;mr=20.;ev=np.linalg.eigvalsh([[0,md],[md,mr]])
check("seesaw_controlled_error",abs(ev[0]+md*md/mr)<md**4/mr**3*1.01)

# Exact local anomaly functions; rows = multiplicity, C dimension/sign, L dimension/sign, X.
def anomalies(rows):
    out=[F(0) for _ in range(6)]
    for mult,dc,sc,dl,sl,x in rows:
        x=F(x)
        out[0]+=mult*dl*sc
        out[1]+=mult*dc*sl
        out[2]+=mult*dl*(F(1,2) if dc>1 else 0)*x
        out[3]+=mult*dc*(F(1,2) if dl>1 else 0)*x
        out[4]+=mult*dc*dl*x
        out[5]+=mult*dc*dl*x**3
    return out
rows331=[(3,1,0,3,1,F(-1,3)),(3,1,0,1,0,1),
         (1,3,1,3,1,F(1,3)),(2,3,1,3,-1,0),
         (4,3,-1,1,0,F(-2,3)),(5,3,-1,1,0,F(1,3))]
check("331RHN_all_six_local_anomalies",anomalies(rows331)==[0]*6)
metrics["331RHN_local_anomalies"]=[str(x) for x in anomalies(rows331)]
for nc in range(3,16):
    q=F(1,2*nc); u=-F(nc+1,2*nc);d=F(nc-1,2*nc);l=F(-1,2);e=F(1)
    vals=[2*q+u+d,nc*q+l,2*nc*q+nc*u+nc*d+2*l+e,
          2*nc*q**3+nc*u**3+nc*d**3+2*l**3+e**3]
    check(f"generalized_SM_local_anomalies_{nc}",vals==[0]*4)
# Generic beta8=sqrt(3)*b, exact rational grid, including E^c.
for nc in range(3,9):
    nf=2*nc; k=nc-1
    for b in [F(-1),F(-1,3),F(0),F(2,3),F(1)]:
        xl=-F(1,2)-b/2;xp=F(1,6)-b/2;xm=F(1,6)+b/2
        qe=-F(1,2)-3*b/2;jp=F(1,6)-3*b/2;jm=F(1,6)+3*b/2
        rows=[(nf,1,0,3,1,xl),(nf,1,0,1,0,1),(nf,1,0,1,0,-qe),
              (k,nc,1,3,1,xp),(nf-k,nc,1,3,-1,xm),
              (nf,nc,-1,1,0,F(-2,3)),(nf,nc,-1,1,0,F(1,3)),
              (k,nc,-1,1,0,-jp),(nf-k,nc,-1,1,0,-jm)]
        pred=[0,0,0,F(nf*(nc-3),12),0,-F(nf*(nc-3),4)*(1+3*b*b)]
        check(f"generalized_331_full_anomaly_{nc}_{b}",anomalies(rows)==pred)
survivors=[];loose=[]
for nc in range(2,31):
    for nf in range(1,101):
        for k in range(nf+1):
            if 2*nc*k==(nc-1)*nf and nf*(nc+1)<22:
                loose.append((nc,nf,k))
                if nc>=3:survivors.append((nc,nf,k))
check("G3_no_primitive_filter",survivors==[(3,3,1)])
check("G3_complex_color_needed",(2,4,1) in loose)
check("G3_AF_needed",2*3*2==(3-1)*6)
metrics["G3_survivors_without_atomicity"]=survivors
candidates=[(nc,nf) for nc in range(3,23) for nf in range(3,23) if nf*(nc+1)<22]
close("framing_candidate_count",len(candidates),7)
framing={str(chi):[(nc,nf) for nc,nf in candidates if nf*(4*nc+3+chi)%48==0] for chi in [0,1,17,33]}
check("framing_zero_empty",framing["0"]==[])
check("framing_one_unique",framing["1"]==[(3,3)])
check("framing_seventeen_competitor",(4,4) in framing["17"])
check("framing_thirtythree_competitors",all(x in framing["33"] for x in [(3,3),(3,4),(3,5)]))
metrics["framing_survivors"]=framing

result={"summary":{"status":"all_passed","checks":len(checks),"seed":31011,
                   "formal_proof_assistant_checked":False,"experimental_data_used":False},
        "environment":{"python":platform.python_version(),"numpy":np.__version__,"scipy":scipy.__version__},
        "metrics":metrics,"checks":checks}
print(json.dumps(result,ensure_ascii=False,indent=2))
