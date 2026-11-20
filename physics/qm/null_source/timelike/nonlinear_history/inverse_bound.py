"""A global four-derivative logarithmic inverse from the frozen two-root factor."""
import sympy as sp
from common import *
def result():
    assert HARMONICS["same_global_divisor_and_M4_cover_all_combinations"]
    assert above(SLOW,1) and below(SLOW,2)
    assert below(SIGMA,"1e6")
    assert above(2*SLOW,3)
    # Frozen all-combination M4 is reused; no spectrum or root is recomputed.
    m4=exact(HARMONICS["four_derivative_inverse_norm_upper"])
    assert below(m4,"1.73e18")
    K=10**6;cutoff=K*K
    r1=SLOW*SLOW;r2=SIGMA*SIGMA
    root_product=(1-r1/cutoff**2)*(1-r2/cutoff**2)
    assert above(root_product,exact(1)/2)
    mu_coefficient=iv.sqrt((exact(3)/4)**3)/30
    assert above(mu_coefficient,exact(1)/60)
    # mu_k>=1/(60*pi^2*x*k) for k>=K;
    # y/(y+b_k)>=1/5 if k<=lambda.
    log_inverse_large=2400*iv.pi**2*X
    log_inverse_small=m4*iv.log(2+exact(cutoff))
    assert below(log_inverse_large,"2e14")
    assert below(log_inverse_small,"4.85e19")
    # lambda>=3: (1+lambda)^4<= (4/3)^4 lambda^4;
    # log(e+lambda)<(6/5)log(2+lambda).
    weight_factor=(exact(4)/3)**4*exact(6)/5
    assert below(weight_factor,4)
    e4_small=weight_factor*log_inverse_small
    e4_large=weight_factor*log_inverse_large
    assert below(e4_small,"2e20") and below(e4_large,"2e20")
    assert above(exact("1.2")*iv.log(5)-iv.log(iv.e+3))
    t=sp.symbols("t",positive=True)
    derivative=sp.Rational(6,5)/(2+t)-1/(sp.E+t)
    numerator=(t+5*(sp.Rational(6,5)*sp.E-2))/5
    assert sp.simplify(derivative-numerator/((2+t)*(sp.E+t)))==0
    return {
      "frozen_four_derivative_inverse_upper":HARMONICS["four_derivative_inverse_norm_upper"],
      "frozen_all_combination_nonresonance":HARMONICS["all_slow_fast_combinations_nonresonant"],
      "K_positive_residue_lower_starts":K,
      "large_frequency_cutoff":cutoff,
      "positive_residue_lower":"mu_k>=1/(60*pi^2*x*k), k>=K",
      "large_frequency_characteristic_lower":"abs(P(lambda))>=lambda^4*log(2+lambda)/(2400*pi^2*x)",
      "low_frequency_lambda4_log_inverse_upper":outward(log_inverse_small)[1],
      "large_frequency_lambda4_log_inverse_upper":outward(log_inverse_large)[1],
      "E4_to_lambda4_log_weight_ratio_upper":outward(weight_factor)[1],
      "E4_inverse_low_upper":outward(e4_small)[1],
      "E4_inverse_large_upper":outward(e4_large)[1],
      "chosen_E4_inverse_upper":"2e20",
      "all_mixed_frequencies_total_degree_at_least_two":True,
      "graph_domain_equivalence_uses_bounded_DS_and_dense_polynomials":True,
      "linear_modes_slow_and_fast_removed_only_from_correction_domain":True,
      "old_spectrum_and_root_recomputed":False,
      "proof":"EXISTENCE.md"}
if __name__=="__main__":finish("inverse_bound.py",result(),["norm_bounds.py","norm_bounds.json"])
