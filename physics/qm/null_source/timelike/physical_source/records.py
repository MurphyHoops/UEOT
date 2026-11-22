"""Exact complete energy law, finite-noise records, and budget/noise tradeoff."""
import sympy as sp
from common import *
def result():
    ss,nu,r=sp.symbols("s nu r",positive=True)
    lap=(1+2*ss/nu)**(-1)*sp.exp(-ss*r/(1+2*ss/nu))
    mean=sp.simplify(-sp.diff(lap,ss).subs(ss,0))
    variance=sp.simplify(sp.diff(lap,ss,2).subs(ss,0)-mean**2)
    assert sp.simplify(mean-r-2/nu)==0
    assert sp.simplify(variance-4*r/nu-4/nu**2)==0
    a,m,rr,ll=sp.symbols("A M vr L",positive=True)
    vv=sp.expand((m/(2*a**6))**2*(rr+4*ll/nu+4/nu**2)).subs(nu,4*sp.pi**2*m/a**2)
    expected=m*m*rr/(4*a**12)+m*ll/(4*sp.pi**2*a**10)+1/(16*sp.pi**4*a**8)
    assert sp.simplify(vv-expected)==0
    assert sp.simplify(2*(a*a/2)/(2*a**3)-1/(2*a))==0
    cases={}
    for name,b in [("zero",iv.mpf(0)),("half_minimum",D/4),
                   ("minimum_equal_law",D/2),("zero_radial_noise",D)]:
        x=root_box(b);nv=4*iv.pi**2*M/x
        correction=4/D*iv.sqrt(2*(1+b)/(iv.pi*nv))+4/(D*nv)
        quantum_variance=4*(1+b)/nv+4/nv**2
        row={"b":outward(b),"nu":outward(nv),
             "energy_variance_quantum_part":outward(quantum_variance),
             "generic_energy_TV_correction_upper":outward(correction)[1]}
        if name in ["zero","half_minimum"]:
            raw=1-2*b/D-correction
            row["energy_TV_lower"]=max(0,outward(raw)[0])
        if name=="minimum_equal_law":
            cv=(D/2)/(1+D/2)
            row["common_radial_variance"]=[3/16,3/16]
            row["common_radial_CV"]=outward(cv)
            row["common_energy_variance"]=outward(iv.mpf(3)/16+quantum_variance)
        if name=="zero_radial_noise":
            row["common_radial_variance"]=[0,0]
            row["common_energy_variance"]=outward(quantum_variance)
        assert above(quantum_variance)
        cases[name]=row
    threshold=(D-iv.mpf(1)/100)/(1+iv.mpf(1)/100)
    assert above(threshold,D/2)
    return {"complete_energy_constant":"Ec=2*V*rhoq+V*U-1/(2*A)",
        "energy_scale":"Es=pi^2*M2/A^3","nu":"4*pi^2*M2/A^2",
        "conditional_energy_law":"nu*S|R = noncentral_chi_square(df=2, noncentrality=nu*R)",
        "conditional_Laplace":"(1+2*s/nu)^(-1)*exp(-s*R/(1+2*s/nu))",
        "complete_energy_variance":"VarR+4*(1+b)/nu+4/nu^2",
        "energy_law_equality_iff_radial_law_equality":True,
        "proof_uses_Laplace_uniqueness_not_moment_determinacy":True,
        "generic_energy_TV_lower":"[1-2*b/d-4/d*sqrt(2*(1+b)/(pi*nu))-4/(d*nu)]_+",
        "explicit_low_budget_energy_TV_exact":"(1-2*b/d)*D_nu",
        "D_nu_bound":"1-4/d*sqrt(2/(pi*nu))-4/(d*nu) <= D_nu <= 1",
        "explicit_completion_quantum_TV_globally_minimal_claimed":False,
        "cases":cases,"one_percent_common_radial_CV_budget":outward(threshold),
        "preparation_channel":"sum_j w_j W_j rho W_j^dagger",
        "bounded_energy_effect":"f(S)=min(1,abs(S-1)/d)",
        "CP_instrument":["sqrt(f(S))*rho*sqrt(f(S))","sqrt(1-f(S))*rho*sqrt(1-f(S))"],
        "local_detector_or_gravity_channel_constructed":False,
        "nonzero_mode_local_stress_noise_deleted":False}
if __name__=="__main__":finish("records.py",result())
