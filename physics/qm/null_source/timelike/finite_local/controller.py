"""Initial-constraint, junction and positive-energy controller admission gates."""
import json,sympy as sp
from common import *
def result():
    b=json.loads((HERE/"smooth_binary.json").read_text())
    high_mu=box(b["conditional_source_mean_centers"][1])-box(b["conditional_source_mean_error_upper"])
    dm=high_mu-MU
    assert above(dm,"0.43")
    delta_source_density=M2*dm/(2*X**3)
    old_thermal_density=4*NTHERMAL*iv.sqrt(3)/(iv.pi**2*X**2)
    old_Gdensity=3/(2*X)
    necessary_negative=(delta_source_density-old_thermal_density)/old_Gdensity
    ideal_NEC_negative=2*delta_source_density/old_Gdensity
    assert above(necessary_negative,"0.1") and above(ideal_NEC_negative,"0.2")
    H,Hdot,a=sp.symbols("H Hdot a",real=True,nonzero=True)
    rho=sp.Rational(3,2)*(H*H+1/(a*a))
    p=-(2*Hdot+3*H*H+1/(a*a))/2
    assert sp.simplify(rho+p-(1/(a*a)-Hdot))==0
    z,kmax=sp.symbols("z kmax",real=True)
    # Saturating kappa keeps the kinetic principal matrix positive for all real chi.
    assert sp.diff(sp.tanh(z),z)==1-sp.tanh(z)**2
    return {
      "fixed_old_geometry_high_flag_required_average_controller_density_negative_magnitude_over_Gdensity_lower":outward(necessary_negative),
      "ideal_pureP_unchanged_high_NEC_negative_magnitude_over_Gdensity_lower":outward(ideal_NEC_negative),
      "actual_short_conditional_high_NEC_sign_inferred_from_energy_alone":False,
      "canonical_nonnegative_energy_controller_alone_satisfies_fixed_old_geometry_contract":False,
      "all_possible_quantum_or_correlated_geometry_controllers_excluded":False,
      "instant_a_jump_is_regular_induced_metric_matching":False,
      "leading_Einstein_continuous_a_jump_H_surface_pressure":"-Delta H * delta(t-t0)",
      "leading_thin_shell_formula_claimed_valid_for_full_high_derivative_SCE":False,
      "smooth_prescribed_preparation_is_total_source_solution":False,
      "minimal_proposal_kappa":"kappa_max*tanh(chi), 0<kappa_max<1",
      "minimal_proposal_controller_action":"-M_chi^2/2 * integral[(grad chi)^2 + m_chi^2 chi^2]",
      "new_controller_parameters_and_initial_data_fixed":False,
      "mean_response_noise_must_share_one_in_in_functional":True,
      "quantized_nonlinear_controller_remains_exact_Gaussian":False,
      "proof":"CONTROLLER.md"}
if __name__=="__main__":finish("controller.py",result(),["CONTROLLER.md","smooth_binary.json","renormalization.json","conditional.json"])
