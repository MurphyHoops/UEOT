"""Classify autonomous selectors and audit the full incoming-clock covariance."""
from common import *
import sympy as sp
def result():
    q=SIGMA/SLOW;N=468087;alpha=q-N
    assert above(alpha,".119") and below(alpha,".342")
    e,t,c,s,f,k,P,x,eta=sp.symbols("epsilon t c s sigma k P x eta",real=True)
    H=sp.Function("H")
    F=sp.exp(-f*t)*H(sp.exp(s*t)*e)
    shifted=F.subs({e:sp.exp(s*c)*e,t:t-c},simultaneous=True)
    assert sp.simplify(shifted-sp.exp(f*c)*F)==0
    example=k*sp.exp((2*s-f)*t)*e**2
    assert sp.simplify(example.subs({e:sp.exp(s*c)*e,t:t-c},simultaneous=True)-sp.exp(f*c)*example)==0
    assert example.subs(e,0)==0 and sp.diff(example,e).subs(e,0)==0
    assert sp.simplify(sp.diff(example,e,2)-2*k*sp.exp((2*s-f)*t))==0
    # B is translated with the geometry; the missing canonical shear is exact.
    assert sp.simplify(P*((eta+c-t)-(eta-t))/x-P*c/x)==0
    assert sp.simplify((eta+c-t)-(eta-(t-c)))==0
    # The full invariants differ from a geometry-only autonomous selector.
    assert sp.simplify(sp.exp(s*(t-c))*sp.exp(s*c)*e-sp.exp(s*t)*e)==0
    return {
      "ratio_sigma_over_s":outward(q),"N":N,"Holder_exponent":outward(alpha),
      "autonomous_graph":"delta=C_sign*abs(epsilon)^(sigma/s)",
      "nonzero_autonomous_graph_regular":"C^(N,alpha), not C^(N+1)",
      "C_N_jets_select_pure_slow":False,
      "autonomy_plus_C_N_plus_1_selects_pure_slow":True,
      "full_clock_covariance":"F(exp(s*c)*epsilon,t-c)=exp(sigma*c)*F(epsilon,t)",
      "general_full_covariant_graph":"F=exp(-sigma*t)*H(exp(s*t)*epsilon)",
      "analytic_slow_tangent_counterexample":"k*exp((2*s-sigma)*t)*epsilon^2",
      "full_covariance_and_analyticity_select_fast_amplitude":False,
      "fixed_QP_and_eta_ref_are_unchanged_by_geometry_only_translation":False,
      "canonical_shear":"Q -> Q+P*c/A^2; P -> P",
      "unique_physical_selection_constructed":False,"proof":"SELECTION.md"}
if __name__=="__main__":finish("selector.py",result(),["SELECTION.md"])
