"""Smooth Fourier preparation, resource, diagonal and record checks."""
from __future__ import annotations
import sympy as sp
import numpy as np
from common import finish, require, iv, outward, below, above
r=sp.symbols("r",integer=True,positive=True); m=sp.symbols("m",integer=True)
N=2*r+1
m2=sp.summation(m*m,(m,-r,r))/N
m4=sp.summation(m**4,(m,-r,r))/N
require(sp.simplify(m2-(N*N-1)/12)==0,"Exact symmetric quadratic phase resource")
require(sp.simplify(m4-(N*N-1)*(3*N*N-7)/240)==0,"Quartic profile average")
t=sp.symbols("t",real=True)
for j in range(-2,3):
    for k in range(-2,3):
        require(sp.simplify(sp.integrate(sp.exp(2*sp.pi*sp.I*(j-k)*t),(t,0,1))-(1 if j==k else 0))==0,"Fourier orthogonality")
for n in [3,5,9]:
    sig=np.eye(n)/n; pure=np.zeros((n,n));pure[n//2,n//2]=1
    require(abs(np.linalg.norm(sig-pure,ord="nuc")/2-(1-1/n))<1e-13,"Exact changed preparation distance")
    require(abs(np.trace(sig@sig)-1/n)<1e-13,"Exact purity")
    require(abs(np.max(np.linalg.eigvalsh(sig))-1/n)<1e-13,"Operator norm collapse")
p,al,A,DE,E0,Etarget=sp.symbols("p al A DE E0 Etarget",real=True)
pp=(Etarget-E0-al*A)/DE
require(sp.simplify(E0+al*A+pp*DE-Etarget)==0,"Once-retuned initial energy")
require(sp.simplify(pp-((Etarget-E0)/DE-al*A/DE))==0,"Retuned probability shift")
q=sp.Rational(1,10)
require(4*q-sp.Rational(1,2)==-sp.Rational(1,10),"Actual profile error exponent")
require(-q/2==-sp.Rational(1,20),"Effective hiding power")
require(2*q-1==-sp.Rational(4,5),"Unretuned mean shift exponent")
# Outward model-unit illustration, no integration of a predecessor solution.
a=iv.mpf(11)/10;b=iv.mpf(19)/10;S=4;nn=1001
L=(1/a-1/b)/2
hide=iv.sqrt(2)*S*L/iv.pi*iv.sqrt((iv.log(nn)+3)/nn)
qfi=8*L*L/iv.pi**2*(iv.log(nn)+2)/nn
Jlower=1/(b*(b-a)**2)
costlower=iv.pi**2*(nn*nn-1)*Jlower/3
require(below(hide,1),"Nontrivial effective hiding illustration")
require(above(costlower),"Positive form resource")
# Complete classical phase-label distance: all commuting branches retain it.
ph=np.array([0.2,0.9]);rho=np.ones((2,2))/2;F=np.diag(np.exp(1j*ph))
base=np.linalg.norm(F@rho@F.conj().T-rho,ord="nuc")/2
dists=[]
for mm in [-2,-1,0,1,2]:
    U=np.diag(np.exp(1j*mm*np.array([0.1,0.7])))
    rr=U@rho@U.conj().T
    dists.append(np.linalg.norm(F@rr@F.conj().T-rr,ord="nuc")/2)
require(max(abs(v-base) for v in dists)<1e-13,"Retained CQ distance unchanged")
finish("dephasing_control.py",{
"preparation":"fixed-profile smooth Fourier random-unitary channel",
"source_marginal_preserved_by_channel":True,
"old_C9_source_marginal_preserved_after_probability_retune":False,
"geometry_law_preserved":True,"initial_energy_and_current_targets":"once retuned, finite K",
"exact_form_cost":"pi^2(N^2-1)/3 * integral n(kappa)^3/kappa",
"explicit_odd_NK_order":"(log K)^(1/10)",
"actual_profile_error_order":"(log K)^(-1/10)",
"reduced_hiding_order":"sqrt(log log K)*(log K)^(-1/20)",
"trace_normal_subsequence_exists":False,"fixed_original_prepared_tested_kernel":"ZERO",
"full_retained_record_phase_gap":"preserved asymptotically; exact for effective layer",
"effective_QFI_reduced":"<=8L^2(log N+2)/(pi^2 N)",
"effective_QFI_with_record":"4 Var_mu(1/(2kappa))",
"example":{"N":nn,"S":S,"hiding_upper_outward":outward(hide),
"effective_QFI_upper_outward":outward(qfi),"added_positive_form_lower_outward":outward(costlower)},
"autonomous_device_constructed":False
},inputs=[
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_feedback/CORRELATED_GAUSSIAN.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_propagation/INITIAL_LAYER.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_propagation/RARE_PREPARATION.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_propagation/RESCALED_KERNEL.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_propagation/INTERIOR_COLLAPSE.md"])
