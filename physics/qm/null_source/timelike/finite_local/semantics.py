"""Exact counterexamples distinguish normal strong constraints and affine mean feedback."""
import sympy as sp
from common import finish
def result():
    x,a,c,v,n=sp.symbols("x a c v n",positive=True)
    density=630*x**4*(1-x)**4
    assert sp.integrate(density,(x,0,1))==1
    assert sp.integrate(x*density,(x,0,1))==sp.Rational(1,2)
    assert sp.integrate((x-sp.Rational(1,2))**2*density,(x,0,1))==sp.Rational(1,44)
    g=x*x*(1-x)**2
    qvar=2*630/c*sp.integrate((x+a)*sp.diff(g,x)**2,(x,0,1))
    assert sp.simplify(qvar-24*(a+sp.Rational(1,2))/c)==0
    # An exact normal sequence: no kernel is not a positive variance floor.
    vv=1/(4*n*n)
    variance=sp.expand(4*vv-4*vv*vv)
    assert sp.simplify(variance-(1/n**2-1/(4*n**4)))==0
    for nn in [1,2,3,10,100]:
        assert 0<variance.subs(n,nn)<1/sp.Integer(nn)**2
    # Two different pure-state decompositions of one density matrix.
    e1=sp.Matrix([1,0]);e2=sp.Matrix([0,1])
    ep=(e1+e2)/sp.sqrt(2);em=(e1-e2)/sp.sqrt(2)
    rho=(e1*e1.T+e2*e2.T)/2
    assert rho==(ep*ep.T+em*em.T)/2
    Z=sp.diag(1,-1)
    f=lambda e:(e.T*Z*e)[0]**2
    assert (f(e1)+f(e2))/2==1 and (f(ep)+f(em))/2==0
    G,m,s2=sp.symbols("G m s2",real=True)
    assert sp.expand((s2-m*m)+(G-m)**2-(G*G-2*G*m+s2))==0
    return {
      "normal_strong_constraint_kernel":"zero for alpha*S0 tensor I + I tensor Hhigh - c, alpha != 0",
      "independent_tensor_factor_required":True,
      "strong_commutation_alone_suffices":False,
      "mean_SCE_disproved":False,
      "positive_uniform_variance_floor_follows_from_no_kernel":False,
      "normal_approximation_variance":"1/n^2 - 1/(4n^4)",
      "normal_approximation_VarQ":"n^2 in dimensionless momentum variables",
      "normal_radial_witness_source_supports":[[1,2],[3,4]],
      "radial_witness_variance":"1/44",
      "radial_witness_each_VarQ":"24*(a+1/2)/C",
      "Gaussian_source_outcome_density_positive_for_every_real_record":True,
      "universal_record_controller_max_mean_error_strict_lower":"1/2",
      "fixed_prior_feedback_can_be_affine":True,
      "posterior_recomputed_for_unknown_input_is_same_channel":False,
      "O2_invariant_nonlinear_selector_affine_counterexample":[1,0],
      "Dirac_rigging_map_or_quantum_geometry_excluded":False,
      "proof":"SEMANTICS.md",
      "symbolic_checks_are_full_functional_analysis_proof":False}
if __name__=="__main__":finish("semantics.py",result(),["SEMANTICS.md"])
