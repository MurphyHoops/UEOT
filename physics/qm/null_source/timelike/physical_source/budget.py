"""Exact reservoir budget, record equivalence, and unavoidable common noise."""
import sympy as sp
from common import finish
def result():
    d=sp.sqrt(3)/2
    b=sp.symbols("b",real=True)
    x=[1-d,sp.Integer(1),1+d]
    po=[sp.Rational(1,2)-b/d,b/d,sp.Rational(1,2)]
    pn=[0,1-b/d,b/d]
    def mean(prob,f):return sp.simplify(sum(p*f(r) for r,p in zip(x,prob)))
    for prob in [po,pn]:
        assert sp.simplify(sum(prob)-1)==0
        assert mean(prob,lambda r:r)==1+b
    vo=sp.simplify(mean(po,lambda r:r*r)-(1+b)**2)
    vn=sp.simplify(mean(pn,lambda r:r*r)-(1+b)**2)
    assert sp.simplify(vo-(d*d-d*b-b*b))==0
    assert sp.simplify(vn-(d*b-b*b))==0
    assert sp.simplify(vo-vn-d*(d-2*b))==0
    # Total variation here uses signs valid exactly for 0<=b<=d/2.
    tv=sp.simplify((po[0]+pn[1]-po[1]+po[2]-pn[2])/2)
    assert sp.simplify(tv-(1-2*b/d))==0
    witness_old=sp.simplify(po[0]+po[2])
    witness_new=sp.simplify(pn[2])
    assert sp.simplify(witness_old-witness_new-tv)==0
    # Common-law frontier for d/2<=b<=d, and constant R for b>=d.
    rc=[1+2*b-d,1+d]
    assert sp.simplify(sum(rc)/2-(1+b))==0
    vc=sp.simplify(sum((r-(1+b))**2 for r in rc)/2)
    assert sp.simplify(vc-(d-b)**2)==0
    assert sp.simplify(vc.subs(b,d/2)-sp.Rational(3,16))==0
    for sigma in [-1,1]:
        old=[(sigma-sp.sqrt(3))/2,(sigma+sp.sqrt(3))/2]
        new=[-sp.Integer(1),sp.Integer(1)]
        weights=[(2-sigma)/4,(2+sigma)/4]
        # Use exact rational weights, preserving the first field marginal.
        weights=[sp.Rational(2-sigma,4),sp.Rational(2+sigma,4)]
        assert sp.simplify(sum(old)/2-sp.Rational(sigma,2))==0
        assert sp.simplify(sum(y*y for y in old)/2-1)==0
        assert sum(p*y for p,y in zip(weights,new))==sp.Rational(sigma,2)
        assert sum(p*y*y for p,y in zip(weights,new))==1
    # The Gaussian references are isotropic under this species rotation.
    y,z=sp.symbols("y z",real=True)
    rot=sp.Matrix([[y,-z],[z,y]])
    assert sp.simplify(rot.T*rot-(y*y+z*z)*sp.eye(2))==sp.zeros(2)
    eps=sp.symbols("eps",nonnegative=True)
    return {"minimum_equal_law_average_budget":"sqrt(3)/4",
        "old_fixed_radius_budget_retained":"sqrt(3)/2",
        "latent_radial_TV_sharp":"max(0,1-2*b/d), d=sqrt(3)/2",
        "low_budget_radial_probabilities":{"support":[str(t) for t in x],
            "old":[str(t) for t in po],"new":[str(t) for t in pn]},
        "equal_law_minimum_radial_variance":"max(d-b,0)^2 for b>=d/2",
        "minimum_budget_common_radial_variance":"3/16",
        "minimum_budget_common_radial_CV":"sqrt(3)/(4+sqrt(3))",
        "CV_epsilon_minimum_budget":"max(d/2,(d-eps)/(1+eps))",
        "full_noise_difference_coefficient":str(sp.expand(d*(d-2*b))),
        "full_noise_kernel":"2*N0+(1+b)*N1+Var(R)*(C tensor C)",
        "retarded_commutator_kernel":"2*chi0+(1+b)*chi1",
        "full_bounded_O2_invariant_record_laws_equal_at_common_radial_law":True,
        "includes_reference_reservoir_and_cross_noise":True,
        "all_record_effects_species_invariant_required":True,
        "global_energy_spectrum_also_makes_radial_law_equality_necessary":True,
        "quantum_energy_TV_not_asserted_equal_to_latent_TV":True,
        "abstract_state_preparation_not_a_local_engineering_implementation":True}
if __name__=="__main__":finish("budget.py",result())
