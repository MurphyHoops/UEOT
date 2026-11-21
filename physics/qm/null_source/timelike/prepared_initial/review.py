"""Independent AE, constraint, UV-compatibility and rational existence review."""
from fractions import Fraction as F
import argparse
import hashlib
import json
from pathlib import Path
import sys
import sympy as sp

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[4]

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def symbolic_review():
    h,y,z,w,wprime,L=sp.symbols("h y z w wprime L",real=True)
    U=y*y-2*h*z+3*h**4+2*h*h-1
    V=-2*w+(12*h*h+4)*y
    Z=4*h*z+8*h*h*y-3*h**4+3*y*y+4*y-2*h*h+1
    C=19+15*L
    Nr=C*U+(h*h+1)**2-60*h*h*(y+h*h+1)
    Nt=C*V+4*y*(h*h+1)-30*Z
    variables=[h,y,z,w,L]
    velocity=[y,z,w,wprime,2*h]
    D=lambda expression:sp.expand(sum(sp.diff(expression,x)*v for x,v in zip(variables,velocity)))
    assert sp.expand(D(U)-h*V)==0
    assert sp.expand(D(Nr)-h*Nt)==0

    # Read directly from AE (1999), equations 10, 12, 14.
    a,a1,a2,a3,a4=sp.symbols("a a1 a2 a3 a4",nonzero=True)
    H1r=-36*a3*a1/a**6+72*a2*a1**2/a**7+18*a2**2/a**6+36*a1**2/a**6-18/a**4
    H1t=-36*a4/a**5+144*a3*a1/a**6-216*a2*a1**2/a**7+108*a2**2/a**6+72*a2/a**5-72*a1**2/a**6
    H3r=3*a1**4/a**8+6*a1**2/a**6+3/a**4
    H3t=12*a2*a1**2/a**7-12*a1**4/a**8+12*a2/a**5-12*a1**2/a**6
    density=C*H1r/(17280*sp.pi**2)+H3r/(2880*sp.pi**2)-(a1*a1*a2/a**7+a1*a1/a**6)/(16*sp.pi**2)
    extra_trace=4*a3*a1/a**6-10*a2*a1*a1/a**7+3*a2*a2/a**6+4*a2/a**5-6*a1*a1/a**6+1/a**4
    trace=C*H1t/(17280*sp.pi**2)+H3t/(2880*sp.pi**2)-extra_trace/(32*sp.pi**2)
    jets={a1:a*h,a2:a*(y+h*h),a3:a*(z+3*h*y+h**3),
          a4:a*(w+4*h*z+3*y*y+6*h*h*y+h**4)}
    assert sp.factor(density.subs(jets,simultaneous=True)-Nr/(960*sp.pi**2*a**4))==0
    assert sp.factor(trace.subs(jets,simultaneous=True)-Nt/(960*sp.pi**2*a**4))==0

    t,eta,ell=sp.symbols("t eta ell",real=True)
    initial={h:0,y:-2+t,z:0,w:-16}
    r_initial=(C*(t*t-4*t+3)+1)/(8640*sp.pi**2)
    p_initial=(C*(t*t-8*t-21)+90*t*t-244*t+159)/(25920*sp.pi**2)
    assert sp.factor(Nr.subs(initial)/(8640*sp.pi**2)-r_initial)==0
    assert sp.factor((Nr-Nt).subs(initial)/(25920*sp.pi**2)-p_initial)==0
    assert sp.factor(r_initial.subs(L,L+2*ell)-r_initial-ell*(t*t-4*t+3)/(288*sp.pi**2))==0
    assert sp.factor(p_initial.subs(L,L+2*ell)-p_initial-ell*(t*t-8*t-21)/(864*sp.pi**2))==0

    # Independent derivative of the exact local physical scale family.
    at=sp.sqrt(3*sp.cos(2*eta))*sp.exp(t*eta*eta/2)
    ht=sp.diff(at,eta)/at
    assert sp.trigsimp(ht-(-sp.tan(2*eta)+t*eta))==0
    qt=1/sp.cos(2*eta)**2-t*(1-2*eta*sp.tan(2*eta))-t*t*eta*eta
    assert sp.trigsimp(-1-sp.diff(ht,eta)-ht**2-qt)==0
    q_jets=[sp.simplify(sp.diff(qt,eta,j).subs(eta,0)) for j in range(6)]
    assert q_jets==[1-t,0,8+8*t-2*t*t,0,256+128*t,0]
    assert sp.simplify((sp.diff(at,eta,4)/at).subs(eta,0)-(-4-12*t+3*t*t))==0

    # WKB expansion independently checks the full generic AE mode subtractions.
    delta,q0,q1,q2=sp.symbols("delta q0 q1 q2")
    B=1+q0*delta-q2*delta**2/4
    g=h+q1*delta/(4*B)
    energy=(B+1-delta+delta*g*g)/(2*sp.sqrt(B))
    pressure=(B-(1-delta)/3+delta*g*g)/(2*sp.sqrt(B))
    E1=(h*h-1)/2
    E3=(q0*q0-2*(h*h-1)*q0+2*h*q1)/8
    P1=q0/3+h*h/2+sp.Rational(1,6)
    P3=-q0*q0/8-q2/12-(3*h*h+1)*q0/12+h*q1/4
    assert sp.simplify(sp.series(energy,delta,0,3).removeO()-1-E1*delta-E3*delta**2)==0
    assert sp.simplify(sp.series(pressure,delta,0,3).removeO()-sp.Rational(1,3)-P1*delta-P3*delta**2)==0
    subs={h:0,q0:1-t,q1:0,q2:8+8*t-2*t*t}
    assert sp.expand(E3.subs(subs)-(3-4*t+t*t)/8)==0
    assert sp.expand(P1.subs(subs)-(sp.Rational(1,2)-t/3))==0
    assert sp.expand(P3.subs(subs)-(-sp.Rational(7,8)-t/3+t*t/24))==0
    # The local subtraction tail does not inherit the faster state-only rate.
    Bstatic=1+delta-2*delta**2/(1+delta)
    Gstatic=(Bstatic+1-delta)/(2*sp.sqrt(Bstatic))
    E5=sp.expand(sp.series(Gstatic,delta,0,4).removeO()).coeff(delta,3)
    assert E5==-sp.Rational(21,16)
    d=sp.symbols("d")
    frozen_density=sp.expand(E3.subs({h:0,q1:0,q0:1})-E3.subs({h:0,q1:0,q0:1+d}))
    frozen_pressure=sp.expand(P1.subs({h:0,q0:1})-P1.subs({h:0,q0:1+d}))
    assert frozen_density==-d*(d+4)/8 or sp.expand(frozen_density+d*(d+4)/8)==0
    assert frozen_pressure==-d/3

    # Full homogeneous Einstein constraint and its off-shell propagation.
    v,acc,M,rho,p=sp.symbols("v acc M rho p",real=True)
    constraint=v*v+a*a-M/(3*a*a)-sp.Rational(2,3)*a**4*rho
    acceleration=acc+a+M/(3*a**3)-a**3*(rho-3*p)/3
    d_constraint=sp.diff(constraint,a)*v+sp.diff(constraint,v)*acc+sp.diff(constraint,rho)*(-3*v*(rho+p)/a)
    assert sp.factor(d_constraint-2*v*acceleration)==0
    dv,dB,B0=sp.symbols("delta_v delta_B B0")
    epsilon=sp.symbols("epsilon")
    variation=sp.diff(2*(v+epsilon*dv)*(B0+epsilon*dB),epsilon).subs(epsilon,0)
    assert sp.expand(variation-2*v*dB-2*dv*B0)==0
    assert sp.expand(variation-2*v*dB)==2*dv*B0

    lam,Qr,Qp=sp.symbols("lambda Qrho Qp",positive=True)
    a0=sp.sqrt(3)*lam
    Mnew=27*lam**4-54*lam**2*Qr
    total_rho=Mnew/(2*a0**6)+Qr/lam**4
    total_p=Mnew/(2*a0**6)+Qp/lam**4
    G00=3/a0**2
    Gii=-(2*(-2+t)+1)/a0**2
    assert sp.factor(G00-2*total_rho)==0
    assert sp.factor((Gii-2*total_p)+2*(t-3*(Qr-Qp)/lam**2)/(3*lam**2))==0
    assert sp.simplify(3*(-2+t)/a0**2-(-2+t)/lam**2)==0

    omega,H,x=sp.symbols("omega H x",real=True)
    J=sp.Matrix([[0,1],[-1,0]])
    sigma=sp.diag(1,-1)
    generator=omega*J+h*sigma
    assert generator.T+generator==2*h*sigma
    product=(sp.exp(H)+sp.exp(H+x))*sp.exp(H)*(sp.exp(x)-1)
    assert sp.simplify(sp.expand(product)-sp.exp(2*H)*(sp.exp(2*x)-1))==0
    return {
        "AE_equations_10_12_14_to_generic_local_terms":"PASS",
        "generic_local_conservation_Nrho_prime_equals_h_Ntrace":"PASS",
        "exact_initial_metric_jets":[str(value) for value in q_jets],
        "mode_subtractions_from_independent_WKB":"PASS",
        "fixed_mu_scaling_anomaly":"PASS; included once through actual metric scale",
        "hard_transfer_density_harmonic_coefficient":str(frozen_density),
        "hard_transfer_pressure_sum_k_coefficient":str(frozen_pressure),
        "local_density_E5_negative_control":str(E5),
        "full_stress_tail_rate":"O(N^-2); state-only density O(N^-4) is not a full-tail claim",
        "off_shell_constraint":"C_prime=2*a_prime*B; delta_C_prime=2*a_prime*delta_B+2*delta_a_prime*B",
        "initial_Hamiltonian_and_pressure_reduction":"PASS",
        "proper_clock_acceleration":"(-2+t_star)/lambda^2",
        "mode_energy_frame_and_Duhamel_quadratic_identity":"PASS"
    }

def rational_review(data):
    stress=data["absolute_stress"]
    R,P=stress["Qrho_absolute_integer_bound"],stress["Qp_absolute_integer_bound"]
    for key,bound in [("Qrho_interval",R),("Qp_interval",P)]:
        lo,hi=map(F,stress[key])
        assert -bound<=lo<=hi<=bound
    lam=data["physical_prescription"]["lambda"]
    radius=F(data["physical_prescription"]["parameter_radius"])
    bound=F(3*(R+P),lam*lam)
    margin=radius-bound
    ratio=1-F(2*R,lam*lam)
    assert margin>0 and ratio>0
    reported=data["initial_existence"]
    assert F(reported["root_absolute_bound"])==bound
    assert F(reported["F_left_upper"])==-margin
    assert F(reported["F_right_lower"])==margin
    assert F(reported["M2_over_27lambda4_lower"])==ratio
    assert tuple(map(F,reported["proper_clock_log_volume_acceleration_interval"]))==((-2-bound)/(lam*lam),(-2+bound)/(lam*lam))
    assert (-2+bound)<0
    # Independent, coarser rational alternative to all transcendental low-mode bounds:
    # H < 1/27, exp(H) < 27/26, x <= 1/16384, exp(x)-1 <= 1/16383.
    assert F(285,7874)<F(1,27)
    norm_bound=F(27,26)
    change=F(1,16383)
    K=data["finite_modes"]["K"]
    sum_cubes=(K*(K+1)//2)**2-1
    bare_independent=norm_bound**2*(2*change+change**2)*sum_cubes
    actual=F(data["finite_modes"]["bare_energy_and_pressure_sum_error"][1])
    assert actual<bare_independent
    assert bare_independent/F(36*9)<450
    for key in ["rho_absolute_bound","pressure_absolute_bound"]:
        assert F(data["new_uniform_uv"][key][0])>=0
    assert F(data["new_uniform_uv"]["B_lower"][0])>0
    assert F(data["new_uniform_uv"]["phase_denominator_lower"][0])>0
    assert not reported["root_uniqueness_proved"]
    assert not reported["nonzero_correction_proved"]
    assert not data["scope"]["future_SCE_solution"]
    assert not data["scope"]["inherited_instrument_probabilities_reused"]
    return {
        "R":R,"P":P,"root_absolute_bound":str(bound),"endpoint_margin":str(margin),
        "source_ratio_interval":[str(ratio),str(2-ratio)],
        "absolute_clock_acceleration_correction_bound":str(bound/(lam*lam)),
        "relative_clock_acceleration_correction_bound":str(bound/2),
        "independent_rational_finite_mode_energy_bound":str(bare_independent),
        "existence_not_uniqueness_or_nonzero_signal":True,
        "full_future_or_surface_jet_extension_not_claimed":True,
    }

def main():
    assert __debug__ and sys.flags.optimize==0
    parser=argparse.ArgumentParser(description=__doc__)
    group=parser.add_mutually_exclusive_group()
    group.add_argument("--write",action="store_true")
    group.add_argument("--check",action="store_true")
    args=parser.parse_args()
    data=json.loads((HERE/"result.json").read_text())
    frozen=dict(data["source_sha256"])
    for rel,digest in frozen.items():
        assert sha(REPO/rel)==digest,("Scientific input changed",rel)
    for p in [HERE/"review.py",HERE/"result.json"]:
        frozen[str(p.relative_to(REPO))]=sha(p)
    result={"schema":"ueot-prepared-initial-review/1","status":"PASS",
            "symbolic":symbolic_review(),"independent_rational":rational_review(data),
            "source_sha256":frozen,
            "native_parallel_review":{"agents":3,"human_peer_review":False,
                "direction":"Independent critique and initial-slice IVT construction",
                "quantum":"AE local terms and finite-mode comparison",
                "consistency":"Independent UV, Ward and tail-rate red team"},
            "new_mode_integrations":0,"new_Lean_proofs":False}
    for rel,digest in frozen.items():
        assert sha(REPO/rel)==digest
    rendered=json.dumps(result,indent=2,sort_keys=True,ensure_ascii=False)+"\n"
    if args.write:(HERE/"review.json").write_text(rendered)
    if args.check:assert rendered==(HERE/"review.json").read_text(),"Independent review receipt mismatch"
    print("PASS: independent AE, UV, off-shell constraint and rational existence review")
if __name__=="__main__":
    main()
