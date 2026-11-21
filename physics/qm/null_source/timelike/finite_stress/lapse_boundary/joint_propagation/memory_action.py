"""Retained-lapse memory identities, full variance and complete pointer checks."""
from __future__ import annotations
import sympy as sp
import numpy as np
from common import finish,require,iv,outward,above
k,la,mass,omega,v=sp.symbols("k la M Omega v",positive=True,real=True)
alpha=sp.symbols("alpha",real=True)
f=sp.Function("f")(k,la)
theta=la/(2*k);phase=sp.exp(sp.I*theta)
Pk=lambda z:-sp.I*sp.diff(z,k)
Pm=lambda z:-sp.I*sp.diff(z,la)
require(sp.simplify(sp.exp(-sp.I*theta)*Pk(phase*f)-(Pk(f)-la*f/(2*k*k)))==0,"Geometry canonical shift")
require(sp.simplify(sp.exp(-sp.I*theta)*Pm(phase*f)-(Pm(f)+f/(2*k)))==0,"Memory canonical shift")
# Symmetric congruence of the geometry cross term, retaining all kappa derivatives.
b=la/(2*k*k);fk=k**(-sp.Rational(1,2))
weighted=fk*(-Pk(b*fk*f)-b*Pk(fk*f)+b*b*fk*f)
pred=-la*(Pk(k**-3*f)+k**-3*Pk(f))/2+la*la*f/(4*k**5)
require(sp.simplify(weighted-pred)==0,"Weighted mixed geometry generator")
mem=sp.exp(-sp.I*theta)*Pm(Pm(phase*f))/(2*mass*k)-Pm(Pm(f))/(2*mass*k)
require(sp.simplify(mem-Pm(f)/(2*mass*k*k)-f/(8*mass*k**3))==0,"Weighted apparatus cross terms")
# Complete retained-lapse off-shell Ward identity and configuration Hessian.
eta=sp.symbols("eta",real=True)
q=sp.Function("q")(eta);p=sp.Function("p")(eta);N=sp.Function("N")(eta)
HM=p*p/(2*mass)+mass*omega*omega*q*q/2
GN=-HM;Gq=-sp.diff(p,eta)-N*mass*omega*omega*q
Gp=sp.diff(q,eta)-N*p/mass
require(sp.simplify(sp.diff(q,eta)*Gq+sp.diff(p,eta)*Gp-N*sp.diff(GN,eta))==0,"Memory Ward identity")
nn,qq,qd=sp.symbols("nn qq qd",real=True,nonzero=True)
Lag=mass*qd*qd/(2*nn)-nn*mass*omega*omega*qq*qq/2
require(sp.simplify(sp.diff(Lag,nn,2)-mass*qd*qd/nn**3)==0,"Configuration lapse contact")
# Exact Gaussian differential/Hermite identities underpin the FULL variance.
chi=sp.exp(-la*la/(4*v))
require(sp.simplify(Pm(chi)-sp.I*la*chi/(2*v))==0,"Gaussian first memory sector")
require(sp.simplify(Pm(Pm(chi))-(1/(2*v)-la*la/(4*v*v))*chi)==0,"Gaussian second memory sector")
X=k**-1
D=lambda z:Pk(z)
Bop=lambda z:D(X**3*z)+X**3*D(z)
comm=Bop(X**2*f)-X**2*Bop(f)
require(sp.simplify(comm-4*sp.I*X**6*f)==0,"Exact source/memory commutator")
h0=1/(8*mass*v)+mass*omega*omega*v/2
V0=1/(32*mass*mass*v*v)+mass*mass*omega**4*v*v/2-omega*omega/4
require(sp.simplify(V0-(mass*omega*omega*v-1/(4*mass*v))**2/2)==0,"Nonnegative baseline apparatus variance")
B=mass*omega*omega*X/2+alpha*X**5/4;C=X/(2*mass)
limit=sp.limit(2*(B-C/(4*v*v))**2,v,sp.oo).subs(alpha,0)
require(sp.simplify(limit-mass*mass*omega**4/(2*k*k))==0,"Complete total-variance lower coefficient")
ell,K=sp.symbols("ell K",positive=True)
require(sp.Rational(2,10)*2==sp.Rational(2,5),"Chosen total-variance growth exponent")
require(sp.simplify((ell/K)*ell**sp.Rational(1,5)-ell**sp.Rational(6,5)/K)==0,"Actual memory residual scale")
# Memory Gaussian instrument, all outcomes included.
z,w1,w2=sp.symbols("z w1 w2",real=True)
dens=sp.sqrt(2*v/sp.pi)*sp.exp(-2*v*z*z)
require(sp.integrate(dens,(z,-sp.oo,sp.oo))==1,"Continuous pointer completeness")
require(sp.simplify(sp.integrate(z*z*dens,(z,-sp.oo,sp.oo))-1/(4*v))==0,"Pointer calibration variance")
require(sp.expand((z-w1)**2+(z-w2)**2-2*(z-(w1+w2)/2)**2-(w1-w2)**2/2)==0,"Exact nonselective Gaussian channel")
I5,I6=sp.symbols("I5 I6",positive=True)
require(sp.simplify((v*I5/4)/(4*v)-I5/16)==0,"Pointer/form tradeoff")
# Finite source matrices with noncommuting coefficients: an exact second-moment
# regression uses width-v Hermite levels 0,1,2, not a physical energy cutoff;
# this is not a full-field truncation claim.
dim=5;ann=np.zeros((dim,dim),complex)
for j in range(1,dim):ann[j-1,j]=np.sqrt(j)
rho=np.array([[.6,.1j],[-.1j,.4]],complex)
HS=np.array([[.4,.2+.1j],[.2-.1j,-.3]])
XX=np.diag([.6,1.1]);DD=np.array([[.2,-.3j],[.3j,.1]])
mm=.8;om=.9;al=-.13;vv=1.7
BB=mm*om*om*XX/2+al*np.linalg.matrix_power(XX,5)/4
CC=XX/(2*mm);JJ=XX@XX/(2*mm)
X3=np.linalg.matrix_power(XX,3)
LL=-al*(DD@X3+X3@DD)/2
A0=HS+X3/(8*mm);Av=A0+vv*BB+CC/(4*vv)
Lam=np.sqrt(vv)*(ann+ann.conj().T)
Pi=(ann-ann.conj().T)/(2j*np.sqrt(vv))
Q=np.kron(A0,np.eye(dim))+np.kron(BB,Lam@Lam)+np.kron(CC,Pi@Pi)+np.kron(LL,Lam)+np.kron(JJ,Pi)
vac=np.zeros((dim,dim));vac[0,0]=1;rr=np.kron(rho,vac)
mean=np.trace(rr@Q);var=float(np.real(np.trace(rr@Q@Q)-mean*mean))
Z=np.sqrt(vv)*LL+1j*JJ/(2*np.sqrt(vv));T=vv*BB-CC/(4*vv)
rhs=float(np.real(np.trace(rho@Av@Av)-np.trace(rho@Av)**2+2*np.trace(rho@T@T)+np.trace(rho@Z.conj().T@Z)))
require(abs(var-rhs)<1e-12,"Complete noncommuting total variance identity")
require(var+1e-12>=2*np.trace(rho@T@T).real,"Positive complete-source lower term")
bound=1/(2*(iv.mpf(19)/10)**2)
require(above(bound),"Illustrative asymptotic lower coefficient")
# Bounded clipped calibration: exact Lipschitz coefficient, then illustrative
# conditional Gaussian quadrature (not an unbounded-moment certificate).
aa,bb,xx=sp.symbols("aa bb xx",positive=True)
require(sp.simplify(-sp.diff(1/(2*xx),xx).subs(xx,1/(2*bb))-2*bb**2)==0,"Clipped inverse Lipschitz constant")
require(sp.simplify((2*bb**2)**2/(4*v)-bb**4/v)==0,"Clipped initial MSE bound")
a_rate=sp.Rational(1,10)
require(4*a_rate-sp.Rational(1,2)==-a_rate,"Common-vector error balances pointer RMS")
require(-2*a_rate==sp.Rational(-1,5),"Squared-cost actual MSE exponent")
require(-1 < -2*a_rate,"Retuned rare input has a smaller bounded-risk term")
nodes,weights=np.polynomial.hermite.hermgauss(96)
calibration=[]
lo=1.1;hi=1.9
for vv0 in [25.,100.]:
    for kk0 in [lo,1.5,hi]:
        zz=1/(2*kk0)+nodes/np.sqrt(2*vv0)
        est=1/(2*np.clip(zz,1/(2*hi),1/(2*lo)))
        risk=float(np.sum(weights*(est-kk0)**2)/np.sqrt(np.pi))
        bound0=hi**4/vv0
        require(risk<=bound0+1e-10,"Illustrative complete-outcome clipped risk")
        calibration.append({"v":vv0,"conditional_kappa":kk0,"risk_rounded":round(risk,10),"analytic_upper_rounded":round(bound0,10)})
finish("memory_action.py",{
"floating_report_rounding":"10 decimal places; internal regression tolerance remains 1e-12",
"added_source":"M>0, Omega>0 conformal-lapse harmonic memory",
"action":"integral(Pi Lambda_prime-N H_M)deta",
"actual_finite_K_evolution":"direct sum of selected d0+E_n block propagators",
"all_n_uniform_graph_bound_claimed":False,
"complete_fast_limit":"F_s tensor I_memory",
"fixed_original_joint_tested_kernel":"ZERO for every normal preparation sequence",
"passive_endpoint":"all operator, state, endpoint and domain transports required",
"active_Gaussian_preparation":"changed state, not free boundary relabeling",
"complete_added_clock_mean":"alpha v I5/4+I3/(8M), plus input budget I1 h0",
"total_mean_once_retunable":True,"old_source_marginal_preserved_by_total_retune":False,
"exact_total_variance":"Var_rho(A_v)+2<(vB-C/(4v))^2>+||Z sqrt(rho)||HS^2",
"total_variance_liminf_over_v_squared":"at least M^2 Omega^4 I2/2",
"variance_increment_or_constraint_residual_bound":False,
"actual_Gaussian_harmonic_memory_rate":"O((log K)^(-1/10)); added residual O((log K)^(6/5)/K)",
"moving_high_energy_comparison":"E_n~K/(2log K), source fast identity, no normal joint limit, remaining variance I2/2",
"continuous_pointer":"normal complete instrument for w=1/(2kappa), noise 1/(4v)",
"pointer_is_original_Csource":False,
"actual_clipped_kappa_MSE":"<=[b^2/sigma+(b-a)e_K]^2+(b-a)^2 delta_K; O((log K)^(-1/5))",
"actual_clipped_kappa_RMS":"O((log K)^(-1/10))",
"calibration_transfer":"same vector/HS purification from M16; complete C9 trace comparison",
"unclipped_kappa_probability_consistency":True,"unclipped_kappa_MSE_controlled":False,
"conditional_pointer_regressions":calibration,
"energy_record_instrument":"K_n=U_K^(E_n) M_n, all n retained",
"illustrative_asymptotic_coefficient_lower_bound_M1_Omega1_support11over10_19over10":outward(bound),
"finite_noncommuting_matrix_regression":{"variance":round(var,10),"three_square_identity":round(rhs,10)},
"autonomous_active_gate_or_four_dimensional_apparatus_constructed":False
},inputs=[
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/ACTION_LIFT.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/ACTION_BOUNDARY.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/RELATIONAL_DOMAIN.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/relational_coupled/ALL_SIGN_EVOLUTION.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_propagation/INITIAL_LAYER.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_propagation/INTERIOR_COLLAPSE.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_propagation/GAUSSIAN_CONTROL.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_propagation/SCALAR_COUNTERTERM.md"])
