"""The present radial apparatus cannot reveal preparation differences erased by the same O(2) twirl."""
import sympy as sp
from common import *
def result():
    theta=sp.symbols("theta",real=True)
    R=sp.Matrix([[sp.cos(theta),-sp.sin(theta)],[sp.sin(theta),sp.cos(theta)]])
    assert sp.simplify(R.T*R-sp.eye(2))==sp.zeros(2)
    x1,x2,y1,y2=sp.symbols("x1 x2 y1 y2",real=True)
    x=sp.Matrix([x1,x2]);y=sp.Matrix([y1,y2])
    assert sp.simplify((R*x).dot(R*y)-x.dot(y))==0
    pure=sp.diag(1,0);mixed=sp.eye(2)/2
    twirl=(R*pure*R.T).applyfunc(lambda a:sp.integrate(a,(theta,0,2*sp.pi))/(2*sp.pi))
    assert twirl==mixed
    assert sp.trace(pure*pure)==1 and sp.trace(mixed*mixed)==sp.Rational(1,2)
    return {
      "premise":"the two original preparations have the same complete O(2) twirl",
      "apparatus":"identical two-species probe states, covariant coupling, radial two-flag reader, scalar controller",
      "per_flag_total_target_stress_means_equal":True,
      "per_flag_full_target_stress_noise_equal":True,
      "per_flag_nonlocal_stress_commutator_inputs_equal":True,
      "complete_invariant_record_laws_equal_under_linear_CP_contract":True,
      "finite_kinetic_adapted_probe_family_breaks_species_symmetry":False,
      "scalar_controller_alone_breaks_this_equivalence":False,
      "current_protocol_detects_original_angular_noise_reduction_as_intrinsic_gravity":False,
      "mere_covariance_of_arbitrary_nonlinear_selector_is_sufficient":False,
      "new_species_reference_or_changed_invariant_source_law_is_free":False,
      "physical_unification_or_empirical_discrimination_completed":False,
      "proof":"SYMMETRY_EXIT.md"}
if __name__=="__main__":finish("symmetry_exit.py",result(),["SYMMETRY_EXIT.md","conditional_noise.json","implementation_bridge.json","records.json"])
