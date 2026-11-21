"""Complete projection instruments, pulse constants and strength-scaling checks."""
from __future__ import annotations
import sympy as sp
import numpy as np
from common import finish,require
g=sp.symbols("g",real=True)
require(sp.trigsimp(sp.cos(g)**2+sp.sin(g)**2-1)==0,"Complete projection instrument")
K,ell,S,delta=sp.symbols("K ell S delta",positive=True)
eps=ell/K
require(sp.simplify(delta/(eps*S)-delta*K/(S*ell))==0,"Necessary peak-strength scale")
w,width,mu,C=sp.symbols("w width mu C",positive=True)
require(sp.simplify((ell/K)*(K/(ell*width))*width-1)==0,"Fixed pulse area scaling")
# Exact rank-one commutator formula in a two-component model.
a,b,t=sp.symbols("a b t",real=True)
v=sp.Matrix([sp.sqrt(3)/2,sp.Rational(1,2)])
A=v*v.T;H=sp.diag(a,b)
comm=H*A-A*H
variance=(v.T*H*H*v)[0]-(v.T*H*v)[0]**2
require(sp.simplify(comm.conjugate().T*comm-variance*sp.eye(2))==sp.zeros(2),"Rank-one commutator variance")
# Finite matrix time-ordered product regression. It is not a field/mode/geometry ODE.
freq=np.array([0.2,0.7]);Hn=-np.diag(freq)
vn=np.sqrt(np.array([0.3,0.7]));An=np.outer(vn,vn);I=np.eye(2)
sy=np.array([[0,-1j],[1j,0]])
def effect(ss):
    F=np.diag(np.exp(1j*ss*freq))
    return F.conj().T@An@F
def gate(P,gg):
    return np.kron(I-P,I)+np.kron(P,np.cos(gg)*I-1j*np.sin(gg)*sy)
commnorm=float(np.linalg.norm(Hn@An-An@Hn,ord=2))
var=float(vn@(Hn@Hn)@vn-(vn@Hn@vn)**2)
require(abs(commnorm*commnorm-var)<1e-14,"Numerical commutator norm")
center=1.3;angle=np.pi/2;Ac=effect(center);ideal=gate(Ac,angle)
require(np.linalg.norm(ideal.conj().T@ideal-np.eye(4),ord=2)<1e-13,"Normal unitary gate")
M0=I-(1-np.cos(angle))*Ac;M1=np.sin(angle)*Ac
require(np.linalg.norm(M0.conj().T@M0+M1.conj().T@M1-I,ord=2)<1e-13,"Both instrument outcomes retained")
# Source entangled with a reference, initially independent pure qubit.
psi=np.zeros(8,dtype=complex);psi[0]=1/np.sqrt(2);psi[5]=1/np.sqrt(2)
def cq(U):
    state=np.kron(U,I)@psi
    blocks=[]
    for p in [0,1]:
        ind=[ss*4+p*2+rr for ss in [0,1] for rr in [0,1]]
        vv=state[ind];blocks.append(np.outer(vv,vv.conj()))
    out=np.zeros((8,8),dtype=complex)
    out[:4,:4]=blocks[0];out[4:,4:]=blocks[1]
    return out
qideal=cq(ideal)
require(abs(np.trace(qideal)-1)<1e-13,"Complete CQ trace with reference")
rows=[]
for ww in [0.04,0.2,0.6]:
    n=64;points=(np.arange(n)+0.5)/n*2-1
    U=np.eye(4,dtype=complex)
    for rr in points:U=gate(effect(center+ww*rr),angle/n)@U
    op=float(np.linalg.norm(U-ideal,ord=2))
    # Midpoint rectangle pulse has exact discrete first absolute moment 1/2.
    bound=abs(angle)*ww*commnorm*float(np.mean(abs(points)))
    require(op<=bound+1e-12,"Time-ordered pulse Duhamel bound")
    Q=cq(U);dist=float(np.linalg.norm(Q-qideal,ord="nuc")/2)
    require(abs(np.trace(Q)-1)<1e-12 and dist<=op+1e-12,"Complete CQ contraction including reference")
    rows.append({"half_width":ww,"product_steps":n,"unitary_error":op,
                 "commutator_upper":bound,"CQ_trace_distance":dist})
# Exact algebra for the extra Gaussian composition; no compactness theorem is simulated.
W,V,F,L=sp.symbols("W V F L",commutative=False)
require(sp.expand(W*V-F*L-(W*(V-L)+(W-F)*(L-1)+(W-F)))==0,"Complete Gaussian/probe difference decomposition")
r,CM,sigma=sp.symbols("r CM sigma",positive=True)
require(sp.simplify((sp.sqrt(2*CM/sigma)*g*sp.sqrt(r))**2-2*CM*g*g*r/sigma)==0,"Hilbert-Schmidt pulse budget")
finish("probe_response.py",{
"picture":"W_K=U(u,u_i), interaction W_K^* A W_K",
"fixed_original_clock_whole_bulk_compact_couplings":"same-K free diamond difference tends to zero",
"compactness_is_operator_compactness_not_spacetime_support":True,
"necessary_peak_strength":"at least delta K/(S log K)",
"finite_K_total_dynamics":"actual bounded-perturbation Dyson unitary",
"rescaled_general_bounded_coupling":"strong unitary and normal complete-instrument limit on fixed normal inputs",
"general_uniform_input_or_diamond_fast_limit_claimed":False,
"ideal_Kraus":["I-(1-cos g)A(s0)","sin g A(s0)"],
"projection_angle":"pi/2","pulse_unitary_error":"<=|g| w mu1 ||[Hfast,A]||",
"limit_order":"fixed pulse width, K to infinity, then width to zero",
"finite_cutoff_embedding":"fixed finite-prefix rank projection; zero-extension restriction then identity-tail transfer",
"actual_C9_fixed_effect_gap":"w_L(1-|chi(s)|^2)-2delta_M >0 after one fixed M choice",
"Gaussian_compact_probe_composition":"proved three-term bound; same-K preparation, no normal limit asserted",
"Gaussian_compact_probe_full_effect":"tends to zero including retained reference",
"Gaussian_rank_r_success_upper":"r sqrt(2pi)||p_x||infinity/sigma",
"failure_record_retained":True,"local_autonomous_action_or_total_stress_constructed":False,
"finite_matrix_regressions_only":rows
},inputs=[
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_propagation/INITIAL_LAYER.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_propagation/INTERIOR_COLLAPSE.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_propagation/BOUNDED_WITNESS.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_propagation/RARE_PREPARATION.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_propagation/GAUSSIAN_CONTROL.md"])
