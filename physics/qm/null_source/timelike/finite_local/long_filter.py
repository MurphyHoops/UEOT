"""Exact compact temporal filtering of the whole static spectrum and calibration error."""
import sympy as sp
from common import *
def result():
    x=sp.symbols("x",nonnegative=True)
    j1lower=1-x/2+x*x/12-x**3/144
    assert sp.expand(sp.diff(j1lower,x)+(x*x-8*x+24)/48)==0
    assert j1lower.subs(x,sp.Rational(5,2))>0
    j0upper=1-x+x*x/4-x**3/36+x**4/576
    assert sp.expand(sp.diff(j0upper,x)+j1lower)==0
    assert j0upper.subs(x,sp.Rational(9,4))<0
    assert above(iv.pi**2/4,exact(9)/4) and below(iv.pi**2/4,exact(5)/2)
    # Alternating Bessel tail; terms decrease strictly beyond m=1.
    partial=exact(0)
    for j in range(25):
        partial+=(-1)**j*(iv.pi/2)**(2*j+1)/(math.factorial(j)*math.factorial(j+1))
    next_term=(iv.pi/2)**51/(math.factorial(25)*math.factorial(26))
    J1=iv.mpf([(partial-next_term).a,partial.b])
    D=2*J1;assert above(D,"0.56") and below(D,"0.57")
    # Every nonzero shell is a symbolic zero, not a numerical frequency fit.
    k=sp.symbols("k",integer=True,positive=True)
    assert sp.sin(sp.pi*k)==0
    # Derivative bound valid throughout a +/-10% timing dilation.
    derivative_cap=2/exact("0.9")**3+6/(iv.pi*exact("0.9")**4*iv.sqrt(3))
    assert below(derivative_cap,exact(9)/2)
    timing=exact("0.001");phase=exact("0.001")
    wleak=27*iv.pi**2*(1+2*NTHERMAL)*X*timing**2/(4*iv.sqrt(3)*VOLUME)
    r=wleak/(4*X)
    Dtrace=iv.sqrt(1-1/((1+r)**2+phase**2))
    assert below(Dtrace,"0.0061")
    long_mse=4*X*MU/C+4*X**2/C**2
    c=VP*X/(VP+X)
    mmse_with_flags=4*c*(C*MU-c)/C**2
    qfi=4*c*(C*MU-c)/X**2
    assert above(qfi)
    support=2*iv.pi+exact("0.1")
    transient_upper=D**2/(4*VM_FIELD*A**3*VOLUME)
    zero_peak_lower=A/(4*X*support**2)
    source_peak_lower=X**2/(2*C*X*support**2)
    integrated_zero_lower=X/(4*X*support)
    residual_peak_lower=1/(12*iv.pi**2*X*support**2)
    return {
      "filter_FT":"-2*sin(pi*sqrt(1+omega^2))/(pi*omega^2*sqrt(1+omega^2))",
      "removable_value_at_zero":1,
      "all_nonzero_shells_removed_exactly":True,
      "base_filter_nonnegative_even_normalized":True,
      "base_filter_half_support":"pi",
      "actual_smooth_filter":"base convolved with fixed even probability C-infinity bump radius 1/20",
      "filter_total_variation_upper":outward(D),
      "minimum_temporal_support_infimum":"2*pi for this whole-spectrum filtering contract",
      "C_infinity_filter_attains_infimum_claimed":False,
      "proper_duration_actual_filter":outward(A*support),
      "causal_complement_of_long_worldtube_empty":True,
      "final_field_observable":"-P/(sqrt(2*pi^2)*A^2)",
      "out_high_state_exactly_unchanged_at_zero_timing_error":True,
      "out_field_injected_energy_at_zero_timing_error":0,
      "target_source_preserved_at_every_intermediate_time":False,
      "input_referred_pointer_noise":outward(X),
      "complete_record_source_MSE_upper":outward(long_mse),
      "classical_p_flag_posterior_source_MMSE":outward(mmse_with_flags),
      "classical_p_and_record_flag_zero_clock_QFI":outward(qfi),
      "coherently_retained_pointer_information_covered_by_clock_bound":False,
      "timing_relative_tolerance":outward(timing),
      "phase_tolerance_delta_R_over_4vm":outward(phase),
      "timing_high_noise_leak_upper":outward(wleak),
      "fixed_actual_input_complete_joint_trace_distance_upper":outward(Dtrace),
      "trace_distance_is_unknown_input_diamond_bound":False,
      "all_times_two_target_fields_injected_energy_upper":outward(transient_upper),
      "target_zero_energy_peak_lower":outward(zero_peak_lower),
      "target_zero_energy_proper_time_integral_lower":outward(integrated_zero_lower),
      "intermediate_matter_source_peak_increment_lower":outward(source_peak_lower),
      "static_original_geometry_mean_density_residual_peak_lower":outward(residual_peak_lower),
      "full_device_total_source_closed":False,
      "proof":"LONG_FILTER.md"}
if __name__=="__main__":finish("long_filter.py",result(),["LONG_FILTER.md"])
