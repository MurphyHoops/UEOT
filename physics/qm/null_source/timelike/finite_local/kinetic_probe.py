"""Exact finite-coupling kinetic field-probe algebra and resource lower bounds."""
import sympy as sp
from common import *
def result():
    g,ch,Abox,Bgrad=sp.symbols("g chi A B",real=True)
    cp=1+g*ch;cm=1-g*ch
    Q=sp.Matrix([[1,1],[1,-1]])/sp.sqrt(2)
    principal=sp.Matrix([[1,g*ch],[g*ch,1]])
    assert sp.simplify(Q.T*principal*Q-sp.diag(cp,cm))==sp.zeros(2)
    vp=g*Abox/(2*cp)-g*g*Bgrad/(4*cp**2)
    vm=-g*Abox/(2*cm)-g*g*Bgrad/(4*cm**2)
    assert sp.simplify(vp.subs(g,-g)-vm)==0
    # Exact homogeneous zero-sector Legendre transform, independent of spatial claim.
    a,p,q,k=sp.symbols("a p q k",positive=True)
    K=sp.Matrix([[1,k],[k,1]])
    energy=(sp.Matrix([p,q]).T*K.inv()*sp.Matrix([p,q]))[0]/(2*a**3)
    assert sp.simplify(energy-(p*p+q*q-2*k*p*q)/(2*a**3*(1-k*k)))==0
    W,nu,B=sp.symbols("W nu B",positive=True)
    assert sp.factor(1/W+1/nu-4/(W+nu))==(W-nu)**2/(W*nu*(W+nu))
    return {
      "new_apparatus_action_is_Core_derived":False,
      "interaction":"-g_c*chi*grad(phi).grad(psi)",
      "finite_coupling_hyperbolic_condition":"abs(g_c*chi)<1",
      "diagonal_kinetic_coefficients":["1+g_c*chi","1-g_c*chi"],
      "rescaled_potential":"Box(sqrt(1 +/- g_c*chi))/sqrt(1 +/- g_c*chi)",
      "source_shift_Noether_charge_exactly_conserved_in_and_out":True,
      "free_matter_momentum_conserved_during_interaction":False,
      "out_target_smearing_integral":0,
      "nonzero_finite_coupling_source_gain_exists":True,
      "numerical_finite_coupling_gain_calibration_supplied":False,
      "same_given_Gaussian_pointer_instrument_identified_exactly_at_finite_coupling":False,
      "in_out_implementer_in_specified_compact_Hadamard_folium":True,
      "all_normal_states_claimed_Hadamard":False,
      "one_probe_positive_zero_energy_before_reader_lower":"1/(8*A^3*beta^2*w)",
      "one_probe_positive_zero_energy_after_specified_Gaussian_reader_lower":"1/(2*A^3*beta^2*w)",
      "two_probe_after_reader_lower":"1/(A^3*beta^2*w)",
      "same_POVM_determines_device_stress":False,
      "same_target_instrument_determines_device_stress":False,
      "full_device_source_closed":False,
      "proof":"KINETIC_PROBE.md"}
if __name__=="__main__":finish("kinetic_probe.py",result(),["KINETIC_PROBE.md"])
