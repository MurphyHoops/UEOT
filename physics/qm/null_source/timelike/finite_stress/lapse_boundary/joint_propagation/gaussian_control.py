"""Exact Gaussian identities and finite-dimensional CP/Fisher regressions."""
from __future__ import annotations
import sympy as sp
import numpy as np
from common import finish,require,iv,outward,below,above
z,sigma,kappa=sp.symbols("z sigma kappa",real=True,positive=True)
gaussian=sp.exp(-z*z/(2*sigma*sigma))/(sp.sqrt(2*sp.pi)*sigma)
normal=sp.integrate(gaussian,(z,-sp.oo,sp.oo))
second=sp.integrate(z*z*gaussian,(z,-sp.oo,sp.oo))
eighth=sp.integrate(z**8*gaussian,(z,-sp.oo,sp.oo))
require(normal==1 and sp.simplify(second-sigma*sigma)==0,"Gaussian normality and variance")
require(sp.simplify(eighth-105*sigma**8)==0,"Coherent memory eighth moment")
wp=sp.diff(1/(2*kappa),kappa)
require(sp.simplify(second*wp*wp/kappa-sigma*sigma/(4*kappa**5))==0,"Complete positive-form increment")
require(sp.simplify(second*(wp/kappa)**2-sigma*sigma/(4*kappa**6))==0,"Current-variance increment")
schur=sp.integrate(sp.exp(-sigma*sigma*z*z/2),(z,-sp.oo,sp.oo))
purity=sp.integrate(sp.exp(-sigma*sigma*z*z),(z,-sp.oo,sp.oo))
require(sp.simplify(schur-sp.sqrt(2*sp.pi)/sigma)==0,"Schur convolution constant")
require(sp.simplify(purity-sp.sqrt(sp.pi)/sigma)==0,"Purity convolution constant")
p,alpha,I5,gap,E0,target=sp.symbols("p alpha I5 gap E0 target",real=True)
pp=(target-E0-alpha*sigma*sigma*I5/4)/gap
require(sp.simplify(E0+alpha*sigma*sigma*I5/4+pp*gap-target)==0,"One-time mean retuning")
require(sp.simplify(pp-(target-E0)/gap+alpha*sigma*sigma*I5/(4*gap))==0,"Probability shift")
q=sp.Rational(1,10)
require(4*q-sp.Rational(1,2)==-q,"Gaussian actual/hiding balanced exponent")
require(2*q-1==-sp.Rational(4,5),"Mean cost exponent")
V=sp.symbols("V",positive=True)
require(sp.limit(sigma*sigma/(sigma*sigma+V),sigma,sp.oo)==1,"Sharp effective Fisher sandwich")
# Illustrations of the normal Gaussian channel on a genuinely noncommuting density.
# These tolerance-based finite matrices do not replace the continuum proofs.
freq=np.array([0.1,0.35,0.7])
vec=np.sqrt(np.array([0.2,0.5,0.3]));rho0=np.outer(vec,vec)
W=np.diag(freq)
def qfi(rho,generator):
    val,U=np.linalg.eigh(rho)
    deriv=1j*(generator@rho-rho@generator)
    D=U.conj().T@deriv@U
    den=val[:,None]+val[None,:]
    return float(2*np.sum(np.divide(abs(D)**2,den,out=np.zeros_like(den),where=den>1e-14)))
rows=[]
for sig in [0.25,0.75,2.,8.]:
    kernel=np.exp(-sig*sig*(freq[:,None]-freq[None,:])**2/2)
    require(np.linalg.eigvalsh(kernel).min()>-1e-12,"Gaussian Schur kernel complete positivity")
    rho=rho0*kernel
    require(abs(np.trace(rho)-1)<1e-14 and np.linalg.eigvalsh(rho).min()>-1e-12,"Trace-one positive output")
    f=qfi(rho,W)
    require(f<=1/(sig*sig)+1e-11,"Reduced effective Fisher upper bound")
    tau=np.diag([0.3,0.7])
    require(abs(qfi(np.kron(rho,tau),np.kron(W,np.eye(2)))-f)<1e-11,"Shared mixed reference factor")
    for ss in [0.2,1.7]:
        F=np.diag(np.exp(1j*ss*freq))
        dist=float(np.linalg.norm(F@rho@F.conj().T-rho,ord="nuc")/2)
        bound=float(sp.erf(sp.Float(abs(ss)/(2*np.sqrt(2)*sig))))
        require(dist<=bound+1e-12,"Gaussian shift trace bound")
        rows.append({"sigma":sig,"s":ss,"trace_distance":dist,"Gaussian_TV_upper":bound,"effective_QFI":f})
sig=iv.mpf(10);S=iv.mpf(4)
hide=S/(iv.sqrt(2*iv.pi)*sig)
require(below(hide,1) and above(hide),"Nontrivial outward hiding example")
finish("gaussian_control.py",{
"preparation":"normal Gaussian random-phase channel, fixed once at initial slice",
"effective_trace_bound":"erf(|s|/(2sqrt(2)sigma)) <= |s|/(sqrt(2pi)sigma)",
"effective_QFI_upper":"1/sigma^2",
"fixed_C5_sharp_effective_QFI":"sigma^2 F_Q ->1",
"actual_original_C9_QFI_upper_claimed":False,
"added_positive_form":"sigma^2 I5/4","added_current_variance":"sigma^2 I6/4",
"current_mean_preserved":True,"energy_target":"once retuned p_sigma=p-alpha sigma^2 I5/(4DeltaE)",
"source_marginal_preserved_by_channel":True,"old_source_marginal_preserved_after_retune":False,
"sigma_K":"(log K)^(1/10)","actual_profile_error_and_reduced_hiding":"O((log K)^(-1/10))",
"operator_norm_bound":"sqrt(2pi)||p_x||infinity/sigma",
"purity_bound":"sqrt(pi)||p_x||infinity/sigma",
"normal_trace_one_limit":False,"fixed_original_prepared_kernel":"ZERO",
"coherent_memory":"normal isometry, complete phase distinction retained",
"continuous_classical_record":"normal L1 density field, not trace-class delta diagonal",
"positive_form_QFI_tradeoff":"F_Q q_D >= I2^2/(4b)",
"joint_cutoff_total_resource_equals_added_resource":False,
"outward_example":{"sigma":10,"S":4,"trace_upper":outward(hide)},
"finite_matrix_regressions_only":rows,
"local_autonomous_device_constructed":False
},inputs=[
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_propagation/INITIAL_LAYER.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_propagation/BOUNDED_WITNESS.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_propagation/RARE_PREPARATION.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_propagation/RARE_FISHER.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_feedback/CORRELATED_GAUSSIAN.md"])
