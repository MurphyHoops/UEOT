"""Normal-state counterexample and a shear-invariant source/clock resource gate."""
import json,sympy as sp
from common import *
def result():
    r,L=sp.symbols("r L",positive=True)
    mu=L+2*r;VD=1+L/(4*r);VS=4*r*L+4*r*r
    gap=sp.factor(VS-mu**2/VD)
    assert sp.simplify(gap-4*r*r*L/(L+4*r))==0
    vv,ss,cc,a=sp.symbols("vv ss cc a",real=True)
    assert sp.expand((vv+2*a*cc+a*a*ss)*ss-(cc+a*ss)**2-vv*ss+cc**2)==0
    k,alpha=sp.symbols("k alpha",positive=True)
    inverse_moment=alpha/(k-1)
    assert sp.simplify((k-1)**2*inverse_moment-2*alpha*(k-1)+alpha*k-alpha)==0
    assert sp.simplify(alpha**2*(1/alpha)-alpha)==0 # k=1, no inverse moment.
    EX=k/alpha;EX2=k*(k+1)/alpha**2
    assert sp.simplify(k*k-2*k*alpha*EX+alpha**2*EX2-k)==0
    u=sp.symbols("u",real=True)
    assert sp.expand(u*(2-u)-(1-(u-1)**2))==0 # adjacent odd mixture variance <=1.
    xx,yy,kk,al,aa=sp.symbols("xx yy kk al aa",real=True)
    anticommutator=sp.I*(kk-al*xx)-sp.I*(kk-al*yy)
    assert sp.simplify(anticommutator+sp.I*al*(xx-yy))==0
    assert sp.simplify(anticommutator/(2*al*aa**2)+sp.I*(xx-yy)/(2*aa**2))==0
    vr=sp.symbols("vr",positive=True)
    assert sp.simplify(sp.Rational(1,2)*2**2/(4*vr)-1/(2*vr))==0
    assert sp.simplify(sp.Rational(1,2)*4**2/(4*vr)-2/vr)==0
    rr=VP/C;LL=1+iv.sqrt(3)/4;mm=LL+2*rr
    single=4*rr*LL+4*rr*rr
    gamma_upper=2*rr*LL+8*rr*rr
    gamma_lower=2*rr*mm
    old_D=1+LL/(4*rr);gamma_D=1+LL/(2*rr)
    assert below(gamma_upper,"7.79e-12") and above(gamma_lower)
    source_ratio=exact("0.5")+3*rr/(2*(LL+rr))
    dilation_ratio=2-1/old_D
    assert below(source_ratio,"0.50000000001")
    assert above(dilation_ratio,"1.9999999999") and below(dilation_ratio,2)
    exact_gap=4*rr*rr*LL/(LL+4*rr)
    assert below(LL/(LL+4*rr),1)
    assert above(gamma_D,"2e11") and below(gamma_D,"3e11")
    readvar=100*old_D
    # iv precision is 120 digits, so exp(x)-1 retains the tiny positive correction.
    em1=iv.exp(1/readvar)-1
    post_variance=(1+em1)*single+mm*mm*em1
    clock_sd=A**3*iv.sqrt(old_D+readvar)/(C*mm)
    assert below(post_variance,"1.58e-11") and below(clock_sd,"2.3")
    static=json.loads((HERE/"static_preparation.json").read_text())
    high=sum((box(static[k]) for k in ["vacuum_pressure_variance_upper","thermal_density_variance","thermal_pressure_variance_upper"]),exact(0))
    post_rms=iv.sqrt(2*(M2/(3*X**2))**2*post_variance+high)
    assert below(post_rms,"1.4e-6")
    return {
      "same_reference_complete_two_point_function_and_high_state":True,
      "Gamma_candidate":"rank<=2 mixture of adjacent odd-k Schwartz vectors",
      "Gamma_shape_parameter_enclosure":outward(gamma_D),
      "Gamma_source_variance_upper":outward(gamma_upper),
      "Gamma_to_single_source_variance_ratio_upper":outward(source_ratio),
      "Gaussian_CQ_dilation_variance":outward(old_D),
      "Gamma_dilation_variance":outward(gamma_D),
      "Gamma_to_CQ_dilation_variance_ratio":outward(dilation_ratio),
      "single_ring_excess_above_fixed_D_variance_bound":outward(exact_gap),
      "general_form_domain_inequality":"VarD*VarS-Cov_sym(D,S)^2 >= mu^2",
      "known_shear_D_to_D_plus_cS_preserves_determinant":True,
      "conformal_clock_precision_product_lower":outward(X/C),
      "proper_clock_precision_product_lower":outward(A**3/C),
      "single_ring_globally_optimal_without_added_resource_constraint":False,
      "Gamma_preparation_or_local_clock_instrument_built":False,
      "Core_derives_this_extra_resource_constraint":False,
      "existing_shift_symmetric_source_reader_blind_to_zero_mode_time_encoding":True,
      "Gamma_mixture_exact_reference_SLD":"D/(alpha*A^2)",
      "Gamma_mixture_exact_reference_QFI":"kappa/(alpha^2*A^4)",
      "Gamma_mixture_QFI_uses_accessible_k_labels":False,
      "specified_Gaussian_D_instrument_mean_source_factor":"exp(1/(2*v_read))",
      "specified_Gaussian_D_instrument_second_source_moment_factor":"exp(2/v_read)",
      "new_annulus_reader_inherits_old_feedback_posterior":False,
      "specific_global_clock_readout_variance_over_original_D_variance":100,
      "specific_clock_after_fixed_mean_restoration_source_variance":outward(post_variance),
      "specific_clock_reference_proper_time_standard_deviation":outward(clock_sd),
      "specific_clock_future_same_static_source_RMS_upper":outward(post_rms),
      "specific_clock_restores_full_two_point_function":False,
      "specific_clock_is_local_total_source_implementation":False,
      "proof":"CLOCK_RESOURCE.md"}
if __name__=="__main__":finish("clock_resource.py",result(),["CLOCK_RESOURCE.md","invariant_preparation.json","static_preparation.json"])
