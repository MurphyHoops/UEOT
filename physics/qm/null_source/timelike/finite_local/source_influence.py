"""Exact homogeneous source influence, actual nonselective extension and controlled phase truncation."""
import sympy as sp
from common import *
def result():
    r,nu=sp.symbols("r nu",real=True);alpha=sp.sqrt(3)/4
    z=1+2*sp.I*r*nu
    assert sp.simplify(sp.conjugate(z)-z.subs(nu,-nu))==0
    f=sp.log(sp.cos(alpha*nu/z))
    coefficients={1:0,2:-sp.Rational(3,32),3:sp.I*3*r/8,4:9*r*r/8-sp.Rational(3,1024)}
    for n,expected in coefficients.items():
        assert sp.simplify(sp.diff(f,nu,n).subs(nu,0)/sp.factorial(n)-expected)==0
    rr=VP/C
    assert below(rr,"3e-12") and above(rr)
    phase=exact("0.1")
    error=exact(3)/8*rr*phase**3*(1+rr*phase)+exact(9)/1792*phase**4
    assert below(error,"5.03e-7")
    assert sp.simplify(sp.cos(-sp.I*alpha/(2*r))-sp.cosh(alpha/(2*r)))==0
    return {
      "histories":"one common finite prescribed FLRW CTP interval, fixed initial state and canonical identification",
      "lapse_invariant_phase_integral":"I_g=integral N/a^3 dt",
      "source_history_phase":"nu=C*(I_plus-I_minus)/2",
      "exact_zero_influence":"Tr rho0 exp(-i*nu*S0)",
      "quiet_zero_influence":"(1+2*i*r*nu)^-1 exp[-i*L*nu/(1+2*i*r*nu)]",
      "two_relative_to_quiet_factor":"cos[(sqrt(3)/4)*nu/(1+2*i*r*nu)]",
      "normalization_Hermiticity_and_positive_history_Gram_kernel":True,
      "new_independent_source_draw_on_each_time_slice":False,
      "all_historical_angular_equal_source_laws_have_equal_zero_influence":True,
      "Gaussian_relative_log_quadratic":"-3*nu^2/32",
      "relative_log_cubic":"i*3*r*nu^3/8",
      "relative_log_quartic":"(9*r^2/8-3/1024)*nu^4",
      "certified_absolute_history_phase_domain":0.1,
      "relative_Gaussian_log_error_upper":outward(error),
      "corresponding_DeltaI_cutoff_enclosure":outward(exact("0.2")/C),
      "lower_variance_implies_global_influence_modulus_ordering":False,
      "relative_factor_is_independent_positive_noise_characteristic":False,
      "instrument_extension_uses_one_common_completed_preparation_and_readout":True,
      "exact_ideal_short_nonselective_restricted_factorization":True,
      "actual_zero_high_state_is_claimed_product":False,
      "factorization_automatically_applies_to_individual_flags_or_finite_kinetic_probe":False,
      "absolute_high_mode_influence_constructed":False,
      "metric_probability_law_constraints_or_stability_derived":False,
      "fixed_radius_formula_reused_for_Gamma_or_mean_restored_D_output":False,
      "influence_amplitude_claimed_fidelity_or_measured_probability":False,
      "phase_error_claimed_as_metric_error":False,
      "proof":"SOURCE_INFLUENCE.md"}
if __name__=="__main__":finish("source_influence.py",result(),["SOURCE_INFLUENCE.md","invariant_preparation.json","static_instrument.json","pulse_ward.json"])
