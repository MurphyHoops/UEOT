"""Exact conditional influence, ordered blocks and branch-sensitive Gram checks."""
from __future__ import annotations
import sympy as sp
import numpy as np
from common import finish,require
th,t,a,b,q=sp.symbols("th t a b q",real=True)
v,M,Om=sp.symbols("v M Om",positive=True,real=True)
AA,bet=sp.symbols("AA bet",positive=True,real=True)
d=sp.cos(th)+sp.I*AA*sp.sin(th)
L=-sp.log(d)/2-v*((sp.cos(th)+sp.I*bet*sp.sin(th))*(a*a+b*b)-2*a*b)/(2*d)
sub={AA:M*Om*v+1/(4*M*Om*v),bet:1/(2*M*Om*v)}
phys={th:0,a:q,b:q}
h0=1/(8*M*v)+M*Om*Om*v/2
V0=1/(32*M*M*v*v)+M*M*Om**4*v*v/2-Om*Om/4
Eq=h0+q*q/(2*M);Vq=V0+q*q/(4*M*M*v)
def physical(expr):return sp.simplify(expr.subs(phys).subs(sub))
require(sp.simplify(physical(Om*sp.diff(L,th))+sp.I*Eq)==0,"Conditional first energy cumulant")
require(sp.simplify(physical(Om*Om*sp.diff(L,th,2))+Vq)==0,"Conditional second cumulant")
require(physical(sp.diff(L,a))==physical(sp.diff(L,b))==0,"Physical initial endpoint first rows")
require(physical(sp.diff(L,a,2))==-v and physical(sp.diff(L,b,2))==-v,"Endpoint self contacts")
require(physical(sp.diff(L,a,b))==v,"Initial mixed endpoint block")
require(sp.simplify(physical(Om*sp.diff(L,th,a))+sp.I*q/(2*M))==0,"Time/endpoint ordered block")
require(sp.simplify(physical(Om*sp.diff(L,th,b))+sp.I*q/(2*M))==0,"Other branch ordered block")
N=sp.Matrix([[Vq,-sp.I*q/(2*M)],[sp.I*q/(2*M),v]])
require(sp.simplify(N.det()-v*V0)==0,"Positive ordered covariance determinant")
require(sp.simplify(V0-(M*Om*Om*v-1/(4*M*v))**2/2)==0,"Ordered block positivity")
kap=sp.symbols("kap",positive=True)
require(sp.simplify(v*sp.diff(1/(2*kap),kap)**2-v/(4*kap**4))==0,"Boundary kappa covariance")
m=sp.symbols("m",positive=True)
A=m*v+1/(4*m*v);dd=sp.cos(th)+sp.I*A*sp.sin(th)
qd=1/(2*v)-sp.I*m*sp.cos(th)/sp.sin(th);qo=sp.I*m/sp.sin(th)
det=qd*qd-qo*qo
require(sp.trigsimp(det+sp.I*m*dd/(v*sp.sin(th)))==0,"Gaussian determinant")
require(sp.trigsimp(qd-v*(sp.cos(th)+sp.I*sp.sin(th)/(2*m*v))*det/dd)==0,"Gaussian diagonal inverse coefficient")
require(sp.trigsimp(qo+v*det/dd)==0,"Gaussian off-diagonal inverse coefficient")
def influence(tt,aa,bb,mm,oo,vv):
    theta=oo*tt;mu=mm*oo;AA0=mu*vv+1/(4*mu*vv);beta=1/(2*mu*vv)
    d0=np.cos(theta)+1j*AA0*np.sin(theta)
    safe=np.cos(theta)**2+AA0*np.sin(theta)**2+1j*(AA0-1)*np.sin(theta)*np.cos(theta)
    pref=np.exp(-.5j*theta)/np.sqrt(safe)
    return pref*np.exp(-vv*((np.cos(theta)+1j*beta*np.sin(theta))*(aa*aa+bb*bb)-2*aa*bb)/(2*d0))
rows=[]
for mm,oo,vv in [(.8,1.1,.2),(1.3,.7,3.)]:
    times=np.array([0,.3,np.pi/(2*oo),np.pi/oo,2*np.pi/oo+.4,5*np.pi/oo])
    endpoints=np.array([.15,.4,.65,.3,.8,.5])
    G=np.array([[influence(times[j]-times[i],endpoints[j],endpoints[i],mm,oo,vv) for j in range(6)] for i in range(6)])
    eig=np.linalg.eigvalsh(G)
    require(np.linalg.norm(G-G.conj().T,ord=2)<1e-12,"Branch-exchange Hermiticity")
    require(np.max(abs(np.diag(G)-1))<1e-12 and eig.min()>-1e-11,"Complete path Gram positivity")
    aa=.2;bb=.7
    require(abs(influence(2*np.pi/oo,aa,bb,mm,oo,vv)+np.exp(-vv*(aa-bb)**2/2))<1e-12,"Full-period zero-point phase retained")
    require(abs(influence(np.pi/oo,aa,bb,mm,oo,vv)+1j*np.exp(-vv*(aa+bb)**2/2))<1e-12,"Half-period parity retained")
    rr=.5*np.log(2*mm*oo*vv);prob=1/np.cosh(rr);weights=[prob]
    for j in range(1,200):
        prob*=((2*j-1)/(2*j))*np.tanh(rr)**2;weights.append(prob)
    require(abs(sum(weights)-1)<1e-12,"Normal squeezed energy law")
    tt=.83
    series=sum(pp*np.exp(-1j*oo*(2*j+.5)*tt) for j,pp in enumerate(weights))
    require(abs(series-influence(tt,0,0,mm,oo,vv))<1e-12,"Independent spectral influence check")
    rows.append({"M":mm,"Omega":oo,"v":vv,"Gram_min_eigenvalue":float(eig.min()),"energy_series_error":float(abs(series-influence(tt,0,0,mm,oo,vv)))})
# Round displayed regression numbers only; all assertions above use full precision.
for row in rows:
    for key,value in row.items():
        if isinstance(value,float):row[key]=round(value,10)
finish("memory_influence.py",{
"floating_report_rounding":"10 decimal places; a rounded zero is not an exact identity",
"conditional_only":True,"same_lapse_memory_and_active_endpoint_state":True,
"exact_influence":"continued d^(-1/2) times Gaussian endpoint exponential",
"real_time_branch":"continuous from zero; full period has minus sign",
"positive_Gram_and_unit_diagonal":True,
"initial_ordered_block":"[[Vq,-i q/(2M)],[i q/(2M),v]]",
"ordered_block_determinant":"v V0 >=0",
"time_endpoint_contacts":"-i q/(2M), both endpoint branches",
"kappa_cross_endpoint_contact":"v/(4 kappa_i^4)",
"interior_kappa_contacts":"included chain-rule delta terms",
"lapse_branches_varied_independently":True,
"memory_reset_or_independent_noise_assumed":False,
"CP_input":"pre-gate source density plus fixed normal preparation, not arbitrary post-gate reduced assignment",
"joint_geometry_path_integral_solved":False,"full_tensor_Einstein_CTP_solved":False,
"finite_Gram_and_energy_series_regressions":rows
},inputs=[
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_propagation/MEMORY_ACTION.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_propagation/GAUSSIAN_CONTROL.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/ACTION_BOUNDARY.md"])
