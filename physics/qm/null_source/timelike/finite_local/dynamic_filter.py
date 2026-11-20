"""Same incoming Jost state, finite long filter, calibrated dynamic error."""
import json
from common import *
def result():
    hp=TIMELIKE/"nonlinear_history/history.json"
    rp=TIMELIKE/"dynamic_inverse/fast_root.json"
    h=json.loads(hp.read_text());r=json.loads(rp.read_text())
    assert h["exact_nonlinear_mean_history_exists"] and h["total_geometry_E4_radius"]=="1e-25"
    rho=exact(h["total_geometry_E4_radius"]);smin=box(r["old_positive_root_reused"])
    assert above(smin,"1.99")
    d=rho;J=rho+rho*rho/(2*smin)
    assert below(J,2*rho)
    D=exact("0.57");L=2*iv.pi+exact("0.1");Y02=1/(2*iv.pi**2)
    high=(1+2*NTHERMAL)*D**2/(2*X*iv.sqrt(3)*VOLUME)*(iv.exp(d+J/iv.sqrt(3))-1)**2
    gain=iv.exp(2*d)-1
    Rhigh=D**2/(2*X*iv.sqrt(3)*VOLUME)*(iv.exp(2*d+J/iv.sqrt(3))-1)
    Rzero=D**2*Y02*L/(2*X)*(iv.exp(2*d)-1)
    outputs={}
    for name,w in [("strong_reference",X),("weak_binary",C/2500)]:
        vm=BETA_FIELD2*w
        D0=1+(gain**2*VP+high/BETA_FIELD2)/(4*w)
        exponent=gain**2*(C*MU-2*VP)/(4*w*D0)
        dg=iv.sqrt(1-iv.exp(-exponent)/D0**2)
        phase=(Rhigh+Rzero)/(4*vm)
        outputs[name]={"pointer_noise":outward(w),"gain_and_high_joint_D_upper":outward(dg),
                       "static_phase_calibration_residual_D_upper":outward(phase),
                       "complete_fixed_input_joint_D_upper":outward(dg+phase)}
    assert below(box(outputs["strong_reference"]["complete_fixed_input_joint_D_upper"]),"1e-18")
    assert below(box(outputs["weak_binary"]["complete_fixed_input_joint_D_upper"]),"1e-22")
    return {
      "incoming_state":"same positive-frequency exact Jost state of the frozen nonlinear history",
      "geometry_E4_radius":outward(rho),"integrated_potential_upper":outward(J),
      "no_new_mode_or_geometry_integration":True,
      "exact_actual_beta_calibration_assumed":False,
      "only_static_Magnus_phase_compensation_used":True,
      "phase_difference_high_upper":outward(Rhigh),"phase_difference_zero_upper":outward(Rzero),
      "out_high_field_variance_leak_upper":outward(high),
      "fixed_input_bounds":outputs,
      "full_pulse_supported_before_certified_history_endpoint":True,
      "same_out_Cauchy_time_comparison":True,
      "dynamic_trace_distance_is_stress_moment_bound":False,
      "pulse_intermediate_total_Einstein_source_closed":False,
      "proof":"DYNAMIC_FILTER.md"}
if __name__=="__main__":finish("dynamic_filter.py",result(),["DYNAMIC_FILTER.md","long_filter.json",str(TIMELIKE/"nonlinear_history/history.json"),str(TIMELIKE/"dynamic_inverse/fast_root.json")])
