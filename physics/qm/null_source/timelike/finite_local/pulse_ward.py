"""The same retarded displacement exposes the pulse work and Bianchi obligation."""
import json,sympy as sp
from common import *
def result():
    t,x=sp.symbols("t x",real=True);u=sp.Function("u")(t,x)
    ut=sp.diff(u,t);ux=sp.diff(u,x)
    T00=(ut*ut+ux*ux)/2;T01=ut*ux;T11=T00
    boxu=-sp.diff(u,t,2)+sp.diff(u,x,2)
    assert sp.simplify(-sp.diff(T00,t)+sp.diff(T01,x)-boxu*ut)==0
    assert sp.simplify(-sp.diff(T01,t)+sp.diff(T11,x)-boxu*ux)==0
    local=json.loads((HERE/"local_tensor.json").read_text())
    lower=box(local["actual_target_out_injected_energy_strict_lower"])
    assert above(lower,"8.31e-14")
    w=C/2500;vm=BETA_FIELD2*w
    pulse_energy=TIME_TV**2/(4*vm*A**3*VOLUME)
    source_increment=8*X**2/(iv.pi**2*C*w)
    zero_transient=4*A/(iv.pi**2*w)
    assert below(pulse_energy,"1.88e-11")
    assert below(source_increment,"2.4e-19")
    assert below(zero_transient,"1.35e-13")
    return {
      "same_actual_short_pointer_channel":True,
      "retarded_displacement":"u_ret=G_ret f; Box u_ret=f",
      "nonselective_target_mean_change_during_pulse":"2*s*T[u_ret]",
      "target_Ward_defect_during_pulse":"2*s*f*grad(u_ret)",
      "target_Ward_defect_identically_zero":False,
      "whole_pulse_two_target_fields_added_energy_upper":outward(pulse_energy),
      "whole_pulse_source_mean_increment_upper":outward(source_increment),
      "whole_pulse_source_variance_increment":"2*mu*delta_mu+delta_mu^2",
      "same_full_Cauchy_covariance":"Gamma_eta=Gamma_free_eta+s*r_eta*r_eta_transpose",
      "Cauchy_normal_derivatives_and_zero_high_cross_terms_retained":True,
      "source_multitime_covariance":"VarS0+4*mu*k_eta_eta_prime/C+4*k_eta_eta_prime^2/C^2",
      "same_pointer_momenta_used_at_all_pulse_times":True,
      "nonselective_spectral_history_is_jointly_readable_with_final_flag":False,
      "whole_pulse_zero_energy_transient_upper":outward(zero_transient),
      "static_target_work":"Delta E=-2*s*integral sqrt(-g)*f*partial_proper_time(u_ret)",
      "strict_nonzero_target_work_lower":outward(lower),
      "free_out_mean_and_noise_conserved":True,
      "free_out_conservation_closes_intermediate_total_source":False,
      "interaction_pointer_controller_must_cancel_Ward_defect":True,
      "whole_device_work_determined_by_target_POVM":False,
      "proof":"PULSE_WARD.md"}
if __name__=="__main__":finish("pulse_ward.py",result(),["PULSE_WARD.md","local_tensor.json"])
