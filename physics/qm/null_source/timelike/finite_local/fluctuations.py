"""Two complete spatially averaged FLRW residuals on the same proper-time window."""
import json,sympy as sp
from common import *
def result():
    mean=json.loads((HERE/"ultraviolet.json").read_text())
    # Exact second- and third-integration-by-parts differential operators.
    t=sp.symbols("t");F=sp.Function("F")(t);om=sp.Function("O")(t)
    op=lambda x:sp.diff(x/om,t)
    second=sp.diff(F,t,2)/om**2-3*sp.diff(F,t)*sp.diff(om,t)/om**3-F*sp.diff(om,t,2)/om**3+3*F*sp.diff(om,t)**2/om**4
    third=sp.diff(F,t,3)/om**3-6*sp.diff(F,t,2)*sp.diff(om,t)/om**4-4*sp.diff(F,t)*sp.diff(om,t,2)/om**4+15*sp.diff(F,t)*sp.diff(om,t)**2/om**5-F*sp.diff(om,t,3)/om**4+10*F*sp.diff(om,t)*sp.diff(om,t,2)/om**5-15*F*sp.diff(om,t)**3/om**6
    assert sp.simplify(op(op(F))-second)==0
    assert sp.simplify(op(op(op(F)))-third)==0
    m=exact(31)/32;P0=exact(16);L=exact(63)/40
    assert below(exact(10)/P0**2,1-m*m)
    CR2=exact(1615)/(4*m*m)+5*exact(95)**2/(16*m**4*P0**2)
    assert below(CR2,450)
    Cdelta=L*450*iv.exp(exact(10)*L/P0);assert below(Cdelta,1950)
    app_e=(exact(35651)+exact(3)/5*237+exact(18)/5*exact(12)/5)/(4*m*m)
    assert below(app_e,10000)
    pair_error=exact(2)*exact("1.51")*3000+exact(3000)**2/P0**3
    assert below(pair_error,11258)
    weighted_error=pair_error*exact(81)/64;assert below(weighted_error,14249)
    assert below(weighted_error+app_e,25000)
    # Third-order pressure IBP coefficients, all norms include endpoint jumps of g'''.
    f0=exact("1.03");f1=exact(93);f2=exact(13688);f3=exact(3805091)
    # |O'|/O<=1/5, |O''|/O<=18/5, |O'''|/O<=77
    pressure_app=(f3+6*f2/5+(4*exact(18)/5+15*exact(1)/25)*f1+
                  (77+10*exact(1)/5*exact(18)/5+15*exact(1)/125)*f0)/(8*m**3)
    assert below(pressure_app+weighted_error,600000)
    P=exact(17)
    low=exact(69)**2*(P**5/5+P**4/2+P**3/3)
    def variance_coefficient(pair):
        # Thermal excess is separately bounded by 7; both fields and all degeneracies retained.
        return (low+16*exact(pair)**2/(9*(P-1)))/(9*iv.pi**4)+7
    energy_var=variance_coefficient(25000);pressure_var=variance_coefficient(600000)
    assert below(energy_var,1600**2) and below(pressure_var,8000**2)
    r0=BETA/MU*iv.sqrt(LOCAL_MSE_UPPER)
    re=1600*LAMBDA2;rp=8000*LAMBDA2
    be=box(mean["density_mean_residual_normalized_by_3_lambda2_over_2"])
    bp=box(mean["pressure_mean_residual_normalized_by_3_lambda2_over_2"])
    total_e=iv.sqrt(r0*r0+re*re+be*be)
    total_p=iv.sqrt(r0*r0+rp*rp+bp*bp)
    joint=iv.sqrt(2*r0*r0+re*re+rp*rp+be*be+bp*bp)
    assert below(total_e,"7e-6") and below(total_p,"7e-6") and below(joint,"1e-5")
    source_variance=box(CASE["variance_S0"])
    geometry_a6_relative_sd_lower=iv.sqrt(source_variance-LOCAL_MSE_UPPER)/(2*MU)
    assert above(geometry_a6_relative_sd_lower,"0.15")
    return {
      "proper_dimensionless_window":[0.0,0.1],
      "g":"Beta(3,3) on [T/4,3T/4] convolved with even smooth bump radius T/8",
      "g_derivative_L1_caps":[75,9600,2400000],
      "g_third_weak_derivative_includes_endpoint_jumps":True,
      "normalizer":"Gbar=(3/2)*lambda^-4*kappa^-3*(integral g*b^6+zeta)>0",
      "energy_pair_UV_cap":"25000/p^2",
      "pressure_pair_UV_cap":"600000/p^2",
      "pair_IR_cap":"69*p",
      "high_energy_RMS_upper":outward(re),
      "high_pressure_RMS_upper":outward(rp),
      "source_conditional_RMS_upper":outward(r0),
      "complete_energy_constraint_RMS_upper":outward(total_e),
      "complete_pressure_equation_RMS_upper":outward(total_p),
      "joint_two_equation_RMS_upper":outward(joint),
      "original_nonselective_source_law_preserved":True,
      "conditional_zero_high_centered_cross_covariance":0,
      "cross_covariance_zero_requires_explicit_reference_product_preparation":True,
      "density_pressure_cross_covariance_assumed_zero":False,
      "initial_a_to_six_relative_standard_deviation_lower":outward(geometry_a6_relative_sd_lower),
      "classical_record_geometry_spread_eliminated":False,
      "instantaneous_or_all_local_tensor_RMS_certified":False,
      "original_local_instrument_plus_total_gravity_history_constructed":False,
      "nearby_exact_SCE_solution_proved":False,
      "proof":"FLUCTUATIONS.md"}
if __name__=="__main__":finish("fluctuations.py",result(),["FLUCTUATIONS.md","ultraviolet.json","records.json"])
