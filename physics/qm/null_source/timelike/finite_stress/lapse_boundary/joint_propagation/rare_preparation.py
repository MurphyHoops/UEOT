"""Exact rare-repair trace distance and operational comparison checks."""
from __future__ import annotations
import numpy as np
import sympy as sp
from common import finish, require

p,c,q=sp.symbols("p c q",nonnegative=True)
x=sp.symbols("x",real=True)
M=sp.Matrix([[c*(1-q)-p-c,c*sp.sqrt(q*(1-q))],
             [c*sp.sqrt(q*(1-q)),c*q]])
require(sp.simplify(M.trace()+p)==0,"Even trace")
require(sp.simplify(M.det()+c*(p+c)*q)==0,"Even determinant")
require(sp.expand((M-x*sp.eye(2)).det()-(x*x+p*x-c*(p+c)*q))==0,"Characteristic polynomial")
require(sp.expand((p+2*c)**2-(p*p+4*c*(p+c)))==0,"Distance upper endpoint")

def norm1(a):
    return float(np.linalg.svd(a,compute_uv=False).sum())
def root(a):
    w,v=np.linalg.eigh(a)
    require(w.min()>-2e-13,"Positive matrix")
    return (v*np.sqrt(np.maximum(w,0)))@v.conj().T

rows=[]
for pp,rr,zz in [(0.1,0.2,0.4+0.3j),(0.27,0.13,0j),(0.02,0.91,1+0j),(0.0,0.6,0.2j)]:
    cc=(1-pp)*rr; qq=1-abs(zz)**2
    v=np.array([1,0,0],dtype=complex); tv=np.array([zz,np.sqrt(qq),0])
    odd=np.diag([0,0,1.])
    r0=np.outer(v,v.conj())
    rep=(1-pp-cc)*r0+cc*np.outer(tv,tv.conj())+pp*odd
    # Shared entangled low/reference density; the scalar block factor is exact.
    bell=np.array([1,0,0,1],dtype=complex)/np.sqrt(2)
    omega=0.73*np.outer(bell,bell.conj())+0.27*np.eye(4)/4
    actual=norm1(np.kron(rep-r0,omega))/2
    exact=(pp+np.sqrt(pp*pp+4*cc*(pp+cc)*qq))/2
    require(abs(actual-exact)<3e-14,"Shared-reference block trace norm")
    require(pp-1e-14<=exact<=pp+cc+1e-14,"Distance interval")
    rows.append({"p":pp,"r":rr,"abs_z_squared":float(abs(zz)**2),
                 "distance_rounded":round(float(exact),10),"matrix_distance_verified":True})
rng=np.random.default_rng(20261121)
max_root_ratio=0.; max_success_ratio=0.
for _ in range(12):
    aa=rng.normal(size=(5,5))+1j*rng.normal(size=(5,5))
    bb=rng.normal(size=(5,5))+1j*rng.normal(size=(5,5))
    A=aa@aa.conj().T; A/=np.trace(A)
    B=bb@bb.conj().T; B/=np.trace(B)
    delta=norm1(A-B)/2
    lhs=float(np.linalg.norm(root(A)-root(B),"fro")**2)
    require(lhs<=2*delta+5e-13,"Square-root trace inequality")
    max_root_ratio=max(max_root_ratio,lhs/(2*delta))
    # One normal CP success branch with its actual complementary failure.
    E=np.diag([.95,.73,.4,.17,.02]); L=np.diag(np.sqrt(1-np.diag(E)**2))
    SA=E@A@E; SB=E@B@E; FA=L@A@L; FB=L@B@L
    sa=float(np.trace(SA).real); sb=float(np.trace(SB).real)
    require(norm1(SA-SB)+norm1(FA-FB)<=2*delta+5e-13,"Full flagged contraction")
    require(norm1(SA-SB)+abs(sa-sb)<=2*delta+5e-13,"Failure probability retained")
    cond=norm1(SA/sa-SB/sb)/2
    require(cond<=delta/max(sa,sb)+5e-13,"Success probability denominator")
    max_success_ratio=max(max_success_ratio,cond*max(sa,sb)/delta)
finish("rare_preparation.py",{
"exact_distance":"(p+sqrt(p^2+4c(p+c)(1-|z|^2)))/2; c=(1-p)r",
"shared_reference_scope":"same input through actual even/odd encodings; fixed p,r,b",
"distance_order":"1/(2 log K) for actual C9",
"sample_blocks":rows,"square_root_examples":12,"max_square_root_ratio_rounded":round(max_root_ratio,10),
"postselection_examples":12,"max_postselection_ratio_rounded":round(max_success_ratio,10),
"same_complete_unitary_preserves_distance":True,
"ordinary_time_prepared_GNS_gate":"ground and C9 equivalent; convergence still OPEN",
"failure_record_retained":True,"autonomous_device_constructed":False
},inputs=[
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_feedback/CORRELATED_GAUSSIAN.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_feedback/NEXT_PROPAGATOR_TEST.md"])
