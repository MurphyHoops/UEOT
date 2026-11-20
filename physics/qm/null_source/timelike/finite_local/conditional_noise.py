"""Exact actual two-flag local stress noise via a Rice moment generator."""
import sympy as sp
from common import *
def result():
    n1,n2,t,z=sp.symbols("n1 n2 t z",real=True)
    delta=sp.symbols("delta",positive=True)
    dt=delta/(1-2*delta*z)
    left=-(n1*n1+n2*n2)/(2*delta)+t*n1+z*(n1*n1+n2*n2)
    right=-((n1-dt*t)**2+n2*n2)/(2*dt)+dt*t*t/2
    assert sp.simplify(left-right)==0
    Z=sp.exp(dt*t*t/2)/(1-2*delta*z)
    zero={t:0,z:0}
    for expr,expected in [(sp.diff(Z,t),0),(sp.diff(Z,z),2*delta),
                          (sp.diff(Z,t,2),delta),(sp.diff(Z,t,z),0),
                          (sp.diff(Z,z,2),8*delta**2)]:
        assert sp.simplify(expr.subs(zero)-expected)==0
    S,E,mn=sp.symbols("S E mn",real=True)
    W=S+sp.I*E/2;Wop=S-sp.I*E/2
    assert sp.expand(2*(W**2-Wop**2)+4*mn*(W-Wop)-4*sp.I*E*(S+mn))==0
    return {
      "state":"same actual source CQ prior and complete smooth binary instrument",
      "conditional_connected_Wightman":"W_c=W_0+s*u*uprime-c*cprime/V",
      "Gaussian_blocks_only_used_before_actual_CQ_and_record_mixing":True,
      "invariant_moment_vector":["abs(p)^2","p.dot(r)","abs(r)^2"],
      "moment_generator":"Z_b=(1-2*delta*z)^-1*exp(delta_z*t^2/2)*P_b((sqrt(R)+delta_z*t)^2;delta_z)",
      "delta_z":"delta/(1-2*delta*z)",
      "needed_derivatives":["t","z","tt","tz","zz"],
      "source_cross_species_classical_noise_included":True,
      "zero_high_quantum_correlations_included":True,
      "all_flag_local_stress_noise_kernels_explicit_as_finite_integrals":True,
      "same_branch_KG_transport_applies_to_all_kernel_entries":True,
      "arbitrary_Hadamard_state_claimed_finite_fourth_moments":False,
      "new_Rice_numerical_integrations":0,
      "same_state_nonlocal_stress_commutator_input_explicit":True,
      "retarded_contact_seagull_and_local_counterterm_variations_calculated":False,
      "full_device_total_noise_or_metric_response_solved":False,
      "proof":"CONDITIONAL_NOISE.md"}
if __name__=="__main__":finish("conditional_noise.py",result(),["CONDITIONAL_NOISE.md","conditional_tensor.json","conditional.json","actual_history.json"])
