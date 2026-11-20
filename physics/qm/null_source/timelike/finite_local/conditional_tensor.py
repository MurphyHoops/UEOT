"""Both actual binary flags retain local anisotropic mean stress."""
import json,sympy as sp
from common import *
def result():
    binary=json.loads((HERE/"smooth_binary.json").read_text())
    tail=box(binary["tail_and_transition_annulus_probability_upper"])
    pmin=exact("0.5")-tail
    gradient_ratio=32*(1+2*NTHERMAL)**2/VOLUME
    assert below(gradient_ratio,70)
    coefficient=4*iv.sqrt(tail)/pmin
    relative=coefficient*gradient_ratio
    assert below(relative,"6e-7")
    w=C/2500
    ns_lower=iv.sqrt(exact(2)/3)*A/(2*w)
    each_lower=(1-relative)*ns_lower
    assert above(each_lower,"1.35e-13")
    # Bound full local tensor relative to the true homogeneous posterior mean.
    beta_abs=iv.sqrt(BETA_FIELD2)
    assert above(beta_abs,"3.3e-11") and above(BETA_FIELD2*C,"0.69")
    assert below(beta_abs*VP,"0.06")
    gamma_bound=2*exact("1.4")*(exact("0.2")+(exact(1)/2400)/exact("0.18"))*tail/(exact("3.3e-11")*pmin*(exact(1)/2500))
    d_bound=exact("0.2")**2*tail/(exact("0.69")*pmin*(exact(1)/2500)**2)
    assert below(gamma_bound,"1e-4") and below(d_bound,"1e-12")
    Ec=(1+2*NTHERMAL)**2*TIME_TV**2/(8*A**3*VOLUME)
    cross=iv.sqrt(2*Ec/A**3)
    assert below(Ec,"3e-15") and below(cross,"3.5e-15")
    local=json.loads((HERE/"local_tensor.json").read_text())
    full=box(local["full_nonselective_mean_tensor_integrated_Frobenius_upper"])+(gamma_bound+2*exact("0.06")*d_bound)*cross+2*d_bound*Ec
    assert below(full,"3.77e-11")
    x,y,c0,R=sp.symbols("x y c R",positive=True)
    P=sp.Function("P");rr=(x*x+y*y)/c0
    lap=sp.diff(P(rr),x,2)+sp.diff(P(rr),y,2)
    expected=(4/c0*(sp.diff(P(R),R)+R*sp.diff(P(R),R,2))).subs(R,rr)
    assert sp.simplify(lap-expected)==0
    # The radial score uses a chi-square_2 variable Z: E Z=2, E Z^2=8.
    assert 2**2*math.factorial(2)-4*(2*math.factorial(1))+4==4
    return {
      "scope":"same original static out slice and actual smooth two-flag instrument",
      "latent_classical_p_observed":False,
      "fine_continuous_record_physically_created":False,
      "covariance_variance":"V=beta^2*(v+w_high+w_pointer), within-p Gaussian block",
      "flag_kernel":"P_b(R)=E e_b(abs(sqrt(R)*e1+N(0,delta*I2)))",
      "exact_conditional_anisotropic_mean":"p_b*pi_b=2*s*p_b*pi[u]+D_b*pi[c]",
      "D_b":"4/(beta^2*C)*E_R[R*P_b_second(R)+P_b_prime(R)]",
      "Gaussian_score_bound":"abs(D_b)<=2*sqrt(tail)/(beta^2*V_z)",
      "c_over_u_spatial_gradient_energy_ratio_upper":outward(gradient_ratio),
      "both_flags_relative_L1_anisotropy_deviation_upper":outward(relative),
      "nonselective_anisotropic_mean_L1_strict_lower":outward(ns_lower),
      "each_flag_anisotropic_mean_L1_strict_lower":outward(each_lower),
      "both_flags_require_nonhomogeneous_geometry_or_device_compensation":True,
      "both_flags_full_mean_tensor_relative_to_true_posterior_homogeneous_tensor_upper":outward(full),
      "full_tensor_comparison_resets_high_state":False,
      "full_tensor_comparison_drops_posterior_mean_shift":False,
      "Gamma_b_absolute_upper":outward(gamma_bound),"d_b_absolute_upper":outward(d_bound),
      "high_covariance_profile_energy_upper":outward(Ec),
      "lower_bound_claimed_detectably_large":False,
      "zero_high_conditional_product_assumed":False,
      "proof":"CONDITIONAL_TENSOR.md"}
if __name__=="__main__":finish("conditional_tensor.py",result(),["CONDITIONAL_TENSOR.md","smooth_binary.json","local_tensor.json"])
