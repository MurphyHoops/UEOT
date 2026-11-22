"""Conditional Gaussian kernels, actual CQ mixing and causal source distinction."""
import sympy as sp
from common import *
def result():
    x,y,V,W,Cov,nu=sp.symbols("x y V W c nu",real=True)
    S=W+nu
    # Completing the square for one commuting record.
    precision=sp.Matrix([[V,Cov],[Cov,W]])
    schur=V-Cov**2/S
    assert sp.simplify(schur+Cov**2/S-V)==0
    # One canonical probe saturates uncertainty after a finite Gaussian reader.
    Bvar,nv=sp.symbols("Bvar nv",positive=True)
    Xnew=Bvar*nv/(Bvar+nv)
    Pnew=1/(4*Bvar)+1/(4*nv)
    assert sp.simplify(Xnew*Pnew-sp.Rational(1,4))==0
    Lx,Ly,Tx,Ty,Spos=sp.symbols("Lx Ly Tx Ty S",real=True)
    q=sp.symbols("q",real=True)
    product=sp.expand((q*Lx+(q*q-1/Spos)*Tx)*(q*Ly+(q*q-1/Spos)*Ty))
    moments={0:1,1:0,2:1/Spos,3:0,4:3/Spos**2}
    expected=sum(coef*moments[power[0]] for power,coef in sp.Poly(product,q).terms())
    assert sp.simplify(expected-(Lx*Ly/Spos+2*Tx*Ty/Spos**2))==0
    return {
      "Gaussian_record_covariance":"S=Cov_sym(B,B)+nu",
      "conditional_mean":"m_p+c*S^-1*(y-b_p)",
      "full_target_probe_conditional_covariance":"C-c*S^-1*c^T+(1/4)*d*nu^-1*d^T",
      "target_out_commutator_d":0,
      "probe_reader_backaction_omitted":False,
      "actual_CQ_state_mixed_with_Bayes_updated_latent_weights":True,
      "whole_CQ_mixture_assumed_Gaussian":False,
      "conditional_Hadamard_finite_rank_change":True,
      "total_noise":"posterior average of Gaussian-block noise plus covariance of block means",
      "nonselective_local_change_outside_JplusK":0,
      "conditional_covariance_change_outside_JplusK_may_be_nonzero":True,
      "conditional_inference_is_instantaneous_physical_gravity_feedback":False,
      "record_stress_covariance_one_Gaussian_block":"L(x)L(x')/S+2*T[c](x)T[c](x')/S^2",
      "full_controller_noise_and_cross_noise_supplied":False,
      "proof":"CONDITIONAL.md"}
if __name__=="__main__":finish("conditional.py",result(),["CONDITIONAL.md","kinetic_probe.json"])
