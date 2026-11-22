"""Finite field-probe existence in stress moments; no numerical coupling claim."""
import json,sympy as sp
from common import *
def result():
    a,b,dq,dp=sp.symbols("a b dq dp",real=True,nonzero=True)
    J=sp.diag(sp.Matrix([[0,1],[-1,0]]),sp.Matrix([[0,1],[-1,0]]))
    h=sp.Matrix([1,0,0,0]);j=sp.Matrix([0,1,0,0]);d=sp.Matrix([0,0,dq,dp])
    scale=sp.diag(a,1/a,1,1)
    off=sp.eye(4)+(d/a)*(J*j).T-j*(d/a).T*J
    shear=sp.eye(4)+(b/a)*j*(J*j).T
    T=shear*off*scale
    assert sp.simplify(T.T*J*T-J)==sp.zeros(4)
    assert sp.simplify(T*h-(a*h+b*j+d))==sp.zeros(4,1)
    assert sp.simplify(T*j-j/a)==sp.zeros(4,1)
    gc,u,b3,vm=sp.symbols("gc u b3 vm",real=True,nonzero=True)
    amplified=(gc*u+gc**3*b3)**2/(4*gc**2*vm)-u*u/(4*vm)
    assert sp.expand(amplified-gc**2*(2*u*b3+gc**2*b3*b3)/(4*vm))==0
    assert sp.Rational(19,48)<sp.Rational(1,2)
    assert sp.Rational(7,32)>sp.Rational(3,16)
    reference=json.loads((HERE/"actual_history.json").read_text())
    R0=box(reference["actual_joint_two_projected_equation_RMS_upper"])
    goal=exact("8e-6");slack=goal*goal-R0*R0
    assert above(slack,"7.7e-12")
    radius=19*iv.pi/48
    alpha_min=(radius-iv.sin(2*radius)/2)/iv.pi
    vm_weak=BETA_FIELD2*C/2500
    resource=alpha_min**2/(4*A**3*vm_weak)
    assert above(alpha_min,"0.2989") and above(resource,"1.46e-13")
    return {
      "first_Born_target_test_is_exact_original_short_f":True,
      "adapted_probe_mode_uses_exact_k_gc_not_only_h":True,
      "finite_rank_mode_transport_symbolically_symplectic":True,
      "full_joint_CCR_fixes_amplified_backaction_direction":True,
      "joint_parameter_Hadamard_smoothing_used":True,
      "target_free_out_kernel_difference":"O(gc^2) in every compact C^r seminorm",
      "actual_softflag_second_and_fourth_smeared_field_moments_converge":True,
      "future_two_geometries_held_fixed_during_implementation_limit":True,
      "finite_nonzero_coupling_exists_for_target_projected_RMS_below":outward(goal),
      "reference_squared_RMS_margin":outward(slack),
      "numerical_coupling_or_convergence_constant_supplied":False,
      "probe_zero_charge_signal_lower":outward(alpha_min),
      "two_probe_positive_zero_energy_coefficient_lower":outward(resource),
      "two_probe_positive_zero_energy_lower":"coefficient/gc^2",
      "uniform_finite_probe_energy_as_gc_tends_zero":False,
      "terminal_smooth_probe_reader_assumed":True,
      "all_probe_reader_controller_stress_included_in_target_RMS":False,
      "physical_total_source_implementation_complete":False,
      "proof":"IMPLEMENTATION_BRIDGE.md"}
if __name__=="__main__":finish("implementation_bridge.py",result(),["IMPLEMENTATION_BRIDGE.md","actual_history.json","kinetic_probe.json","conditional.json","smooth_binary.json"])
