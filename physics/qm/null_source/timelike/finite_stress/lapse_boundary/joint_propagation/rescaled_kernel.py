"""Exact endpoint, two-time and bounded-instrument identities."""
from __future__ import annotations
import sympy as sp
import numpy as np
from common import finish, require
s,t,x=sp.symbols("s t x",real=True,positive=True)
phase=sp.exp(sp.I*(s-t)/(2*x))
require(sp.simplify(-sp.I*sp.diff(phase,s)-phase/(2*x))==0,"Left layer equation")
require(sp.simplify(sp.I*sp.diff(phase,t)-phase/(2*x))==0,"Right layer equation")
eps=sp.symbols("eps",positive=True)
require(sp.simplify(eps*(x/eps-sp.Rational(1,2)/eps)-(x-sp.Rational(1,2)))==0,"Constraint scaling factor")
kappa=np.array([1.,1.4,2.2])
R=np.diag(np.sqrt(kappa)); f=np.diag(1/np.sqrt(kappa)); K=np.diag(kappa)
def F(u):return np.diag(np.exp(1j*u/(2*kappa)))
vec=np.array([1.,2.,1j]);vec=vec/np.linalg.norm(vec)
rho=.7*np.outer(vec,vec.conj())+.3*np.eye(3)/3
Gamma=f@F(.8)@rho@F(.8).conj().T@f
require(np.linalg.norm(R@Gamma@R-F(.8)@rho@F(.8).conj().T)<1e-13,"Weighted density recovery")
require(abs(np.trace(R@Gamma@R)-1)<1e-13,"Weighted normalization")
G12=f@F(.8-.4)@f;G23=f@F(.4-.1)@f;G13=f@F(.8-.1)@f
require(np.linalg.norm(G12@K@G23-G13)<1e-13,"Weighted propagator gluing")
P12=f@F(.8)@rho@F(.4).conj().T@f
P23=f@F(.4)@rho@F(.1).conj().T@f
expected=f@F(.8)@(rho@rho)@F(.1).conj().T@f
require(np.linalg.norm(P12@K@P23-expected)<1e-13,"Prepared product includes rho squared")
require(np.linalg.norm(expected-f@F(.8)@rho@F(.1).conj().T@f)>1e-3,"Prepared kernel is not propagator")
# Positive block kernel and actual full failure instrument.
times=[0.,.3,.8]
block=np.block([[F(a)@rho@F(b).conj().T for b in times] for a in times])
require(np.linalg.eigvalsh(block).min()>-1e-12,"Two-time kernel positivity")
M0=np.diag([.2,.6,.9]);M1=np.diag(np.sqrt(1-np.diag(M0)**2))
branches=[]
for M in [M0,M1]:
    B=F(.8-.3)@M@F(.3)
    branches.append(B@rho@B.conj().T)
require(abs(sum(np.trace(v) for v in branches)-1)<1e-13,"Complete outcome normalization")
for M in [M0,M1]:
    Mr=f@M@R
    require(np.linalg.norm(R@Mr@f-M)<1e-13,"Weighted Kraus recovery")
B=np.diag(kappa*kappa/(1+kappa*kappa))
require(np.linalg.norm(F(.8).conj().T@B@F(.8)-B)<1e-13,"Diagonal readout commutes")
finish("rescaled_kernel.py",{
"normal_two_time_trace_norm_limit":"F_s rho_infinity F_t*",
"test_Jacobian":"phi_K(u)=epsilon_K^-1 Phi((u-u_i)/epsilon_K)",
"effective_constraint":"kappa P_s-1/2; combined tested limit of epsilon_K C_K",
"weighted_trace_preserved":True,"raw_density_gluing_includes_rho_squared":True,
"finite_complete_CP_histories_converge":True,"failure_records_retained":True,
"all_trace_normal_preparations_uniform_original_initial_window":"REJECTED",
"fixed_original_interior_test_convergence":"OPEN",
"raw_flat_kernel_trace_class_for_arbitrary_normal_input":False,
"operator_norm_or_diamond_convergence_claimed":False,
"local_autonomous_device_constructed":False
},inputs=[
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_propagation/INITIAL_LAYER.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_propagation/LOCAL_CONSTRAINT.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_propagation/RARE_PREPARATION.md"])
