"""Independent Ward/component, classical-constraint and scope review."""
import json
import sympy as sp
from common import *
def result():
    # Exact finite-z AE conservation, not inferred from a truncated Taylor jet.
    hj=sp.symbols("h0:5",real=True);ell=sp.symbols("ell",real=True)
    hh,hp,hpp,hppp=hj[:4]
    def Dt(e):
        return sp.expand(sum(sp.diff(e,hj[j])*hj[j+1] for j in range(4))+sp.diff(e,ell)*2*hh)
    v=hp+hh*hh
    a3=hpp+3*hh*hp+hh**3
    a4=hppp+4*hh*hpp+3*hp**2+6*hh*hh*hp+hh**4
    q=-1-v;f=Dt(q);q2=Dt(f)
    e1=(hh*hh-1)/2
    e3=(q*q-2*(hh*hh-1)*q+2*hh*f)/8
    p1=q/3+hh*hh/2+sp.Rational(1,6)
    p3=-q*q/8-q2/12-(3*hh*hh+1)*q/12+hh*f/4
    assert sp.simplify(Dt(e1)-hh*(e1-3*p1))==0
    assert sp.simplify(Dt(e3)-hh*(e3-3*p3))==0
    h1=-36*a3*hh+72*v*hh*hh+18*v*v+36*hh*hh-18
    t1=-36*a4+144*a3*hh-216*v*hh*hh+108*v*v+72*v-72*hh*hh
    h3=3*hh**4+6*hh*hh+3
    t3=12*v*hh*hh-12*hh**4+12*v-12*hh*hh
    ran=(-h1/6+h3)/2880-h1/1728+(h1*(2+ell)/32-sp.Rational(9,4)*(hh*hh*v+hh*hh))/36
    tan=(-t1/6+t3)/2880-t1/1728+(t1*(2+ell)/32-sp.Rational(9,8)*(
        4*a3*hh-10*v*hh*hh+3*v*v+4*v-6*hh*hh+1))/36
    assert sp.simplify(Dt(h1)-hh*t1)==0
    assert sp.simplify(Dt(h3)-hh*t3)==0
    assert sp.simplify(Dt(ran)-hh*tan)==0
    a,a1,a2,rho,p=sp.symbols("a a1 a2 rho p",nonzero=True)
    rhop=-3*a1*(rho+p)/a
    Cp=2*a1*a2+2*a*a1-sp.Rational(2,3)*(4*a**3*a1*rho+a**4*rhop)
    Bacc=a2+a-a**3*(rho-3*p)/3
    assert sp.simplify(Cp-2*a1*Bacc)==0
    E=a1*a1/a**2+1-2*a*a*rho/3
    S=a2/a-a1*a1/(2*a**2)+sp.Rational(1,2)+a*a*p
    assert sp.simplify(Bacc/a-S-E/2)==0
    ep=(E-2*Bacc/a)/a**2
    assert sp.simplify(ep+2*S/a**2)==0
    z,b,S1,S2,S3=sp.symbols("z beta S1 S2 S3",real=True)
    E2=S1;E3=(2*S2+(4*b-1)*S1)/3
    ej=E2*z*z+E3*z**3
    ward=sp.expand(sp.diff(ej,z)+(1+2*b*z)*ej-2*(1+2*b*z)*(S1*z+S2*z*z))
    assert ward.coeff(z,1)==sp.simplify(ward.coeff(z,2))==0
    E4=S3/2
    assert sp.expand(sp.diff(E4*z**4,z)-2*S3*z**3)==0
    # Independent classical first integral, not a substitute for quantum response.
    t=sp.symbols("t",positive=True)
    assert sp.factor((2*t+1)*(t-1)**2/(3*t*t)-(2*t/3+1/(3*t*t)-1))==0
    u=z-z*z/3;hh=2*z*sp.diff(u,z)
    constraint=hh*hh+1-sp.exp(-4*u)/3-2*sp.exp(2*u)/3
    assert sp.series(constraint,z,0,4).removeO().expand()==0
    # Changing incoming source energy cannot be absorbed by a decaying-past seed.
    dm,A0=sp.symbols("delta_M A",nonzero=True)
    assert sp.simplify(-sp.Rational(2,3)*A0**4*dm/(2*A0**6)+dm/(3*A0**2))==0
    assert sp.simplify(-A0**3*(dm/(2*A0**6)-3*dm/(2*A0**6))/3-dm/(3*A0**3))==0
    data={name:json.loads((HERE/(name+".json")).read_text()) for name in ["jet","bounds","window","records"]}
    assert all(v["status"]=="PASS" for v in data.values())
    w=data["window"]
    assert w["finite_positive_window_numerical_remainder_certified"]
    assert not w["exact_nonlinear_SCE_solution_constructed"]
    assert not w["random_source_constraint_or_gravity_instrument_constructed"]
    assert not w["exact_Jost_modes_assumed_delta_analytic"]
    assert w["x_times_orthonormal_density_defect_upper"]<3.080e-12
    assert w["x_times_orthonormal_pressure_defect_upper"]<4.104e-8
    return {
        "full_AE_local_and_subtraction_conservation_exact":True,
        "Ward_identity":"C'=2*a'*Bacc; E'+h*E=2*h*S",
        "actual_orthonormal_components":"Gnn-2rho=3E/a^2; Gii-2p=-2S/a^2",
        "constraint_second_coefficient":"E2=S1",
        "constraint_third_coefficient":"E3=(2*S2+(4*beta-1)*S1)/3",
        "constraint_fourth_when_first_two_spatial_coefficients_vanish":"E4=S3/2",
        "classical_stiff_plus_U_first_integral_checked":True,
        "classical_beta":"-1/3",
        "incoming_energy_shift_past_constraint":"delta C=-delta_M/(3*A^2)",
        "incoming_energy_shift_past_trace_residual":"delta Bacc=delta_M/(3*A^3)",
        "finite_positive_window_bound_present":True,
        "new_certificates_read":["jet","bounds","window","records"],
        "complete_quantum_gravity_or_unification_claimed":False,
        "seven_percent_static_bound_is_geometry_RMS":False,
        "seven_percent_static_bound_negates_mean_SCE":False,
        "root_native_agent_roles":["A: state/Ward/UV","B: KG/AE/response/UV","C: dynamic records/ensemble/clock"],
        "external_human_peer_review":False,
        "remaining_exit":"Exact nonlinear SCE correction/existence with error, joint fluctuating constraint law, and physical local device; dynamic O2 record obstruction applies under its stated contract."}
if __name__=="__main__":finish("review.py",result(),
    [p for n in ["jet","bounds","window","records"] for p in [n+".py",n+".json"]])
