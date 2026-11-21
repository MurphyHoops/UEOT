#!/usr/bin/env python3
"""Independent narrow audits of C's propagation and B's W2/tail algebra."""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import sys
import sympy as sp

HERE=Path(__file__).resolve().parent
sys.dont_write_bytecode=True
sys.path.insert(0,str(HERE.parent/"propagation"))
import background as bg
import finite_modes as fm
I,iv,mp=bg.I,bg.iv,bg.mp


def static_step_audit():
    # Exact constant-background oscillator, not another numerical ODE solver.
    lo=Q(-1,4); hi=lo+Q(1,1024); degree=12; last=64
    variation,growth,remainder=fm.local_certificate(lo,hi,degree,last)
    a,c,b=bg.coefficients(lo,lo,degree,hi-lo)
    ae=bg.derivative_box(hi,hi,1)
    cell=dict(lo=lo,hi=hi,variation=variation,growth=growth,
        remainder=remainder,c=c.c,b=b.c,a_end=ae.c[0],
        h_end=ae.c[1]/ae.c[0])
    results=[]
    for k in (2,17,64):
        omega=iv.sqrt(k*k-1); ast=iv.sqrt(3)
        u_exact0=iv.mpc(1/(ast*iv.sqrt(2*omega)),0)
        p_exact0=iv.mpc(0,-ast*iv.sqrt(omega/2))
        u,du=fm.recenter(u_exact0);p,dp=fm.recenter(p_exact0)
        initial=fm.bound(iv.sqrt(omega*ast*ast*du*du+dp*dp/(omega*ast*ast)))
        uc,pc,error=fm.step(u,p,initial,cell,k,degree)
        cosine=iv.cos(omega*I(hi-lo));sine=iv.sin(omega*I(hi-lo))
        ux=u_exact0*cosine+p_exact0*sine/(omega*ast*ast)
        px=p_exact0*cosine-omega*ast*ast*u_exact0*sine
        discrepancy=fm.norm(ux-uc,px-pc,ast,omega)
        assert bg.upper(discrepancy)<=bg.lower(error)
        altered=dict(cell,remainder=I(0))
        un,pn,false_error=fm.step(u,p,initial,altered,k,degree)
        assert bg.lower(discrepancy)>bg.upper(false_error)
        results.append({
            "k":k,
            "exact_analytic_energy_discrepancy":fm.decimal_box(discrepancy),
            "certified_energy_error":fm.decimal_box(error),
            "false_bound_without_Taylor_remainder":fm.decimal_box(false_error),
            "omitted_remainder_negative_control_rejected":True})
    try:
        bg.cap_step_bound(Q(1,64),33)
    except AssertionError:
        cap_guard=True
    else:
        cap_guard=False
    assert cap_guard
    return {"constant_scale_factor":True,"modes":results,
            "cap_monotonicity_condition_guard":cap_guard}


def w2_algebra():
    z=sp.symbols("delta",positive=True)
    q=sp.symbols("q0:6")
    def dt(f):
        return sum(sp.diff(f,q[j])*q[j+1] for j in range(5))
    A=1+z*q[0]
    T=-q[2]/(4*A)+5*z*q[1]**2/(16*A**2)
    T1=-q[3]/(4*A)+7*z*q[1]*q[2]/(8*A**2)-5*z**2*q[1]**3/(8*A**3)
    T2=(-q[4]/(4*A)+9*z*q[1]*q[3]/(8*A**2)
        +7*z*q[2]**2/(8*A**2)-29*z**2*q[1]**2*q[2]/(8*A**3)
        +15*z**3*q[1]**4/(8*A**4))
    assert sp.cancel(dt(T)-T1)==0
    assert sp.cancel(dt(T1)-T2)==0
    B=A+z*z*T
    # Independently form w''+(k^2+q)w from W2^2=k^2*B.
    residual=-z*T-dt(dt(B))/(4*B)+5*dt(B)**2/(16*B**2)
    normalized=(-T2/(4*B)+z*q[2]*T/(4*A*B)
        +5*z*(2*q[1]*T1+z*T1*T1)/(16*B*B)
        -5*z*z*q[1]*q[1]*T*(2*A+z*z*T)/(16*A*A*B*B))
    assert sp.cancel(residual-z*z*normalized)==0
    # c/(2 phi') = k^-6 Rn/(4B+2 delta^3 Rn).
    k,rn,b=sp.symbols("k Rn B",positive=True)
    omega=k*sp.sqrt(b); defect=rn/k**4; mixing=defect/(2*omega)
    identity=sp.cancel(mixing/(2*(omega+mixing))
                        -k**-6*rn/(4*b+2*k**-6*rn))
    assert identity==0
    # Sum-bound exponents include k^2 S3 degeneracy and e_W2=k*G.
    ranks={}
    for rank in (5,6):
        ranks[str(rank)]={
            "diagonal_integral_power":2*rank-4,
            "energy_cross_constant_integral_power":rank-3,
            "energy_cross_inverse_k_integral_power":rank-2,
            "pressure_cross_integral_power":rank-4,
        }
    return {"T1_is_time_derivative":True,"T2_is_time_derivative":True,
        "defect_R_equals_delta_squared_Rn":True,
        "phase_integration_by_parts_identity":True,
        "degeneracy_aware_integral_powers":ranks}


def finite_gap_lower():
    k=sp.symbols("k",positive=True)
    static=k**2*sp.sqrt(k*k-1)-k**3+k/2+1/(8*k)
    physical_subtraction=k**2*(sp.sqrt(k*k-1)-k+sp.Rational(1,2)/k
                               -sp.Rational(3,8)/k**3)
    assert sp.simplify(physical_subtraction-static+1/(2*k))==0
    # r_static = -sum_{j>=3} b_j/k^(2j-3),
    # b_3=1/16 and b_(j+1)/b_j=(j-1/2)/(j+1)<1.
    j=sp.symbols("j",integer=True,positive=True)
    ratio=(j-sp.Rational(1,2))/(j+1)
    assert sp.simplify(1-ratio)==sp.Rational(3,2)/(j+1)
    # Exact Wronskian + AM-GM gives e>=sqrt(k^2-1), independently of state.
    return {
        "eta_zero_gap_identity":True,
        "static_binomial_first_tail_coefficient":"1/16",
        "binomial_successive_ratio":str(ratio),
        "finite_unresolved_sum_lower":
            "-1/(32*K^2*(1-1/(K+1)^2)) - log(J/K)/2",
        "scope":"K<k<=J; full k^2 degeneracy; J>K>=2",
        "infinite_tail_still_required":True,
    }


def initial_density_lower_audit():
    """Independent eta0 assembly and analytic specialized far-tail bound.

    Uses C's rational mode balls and B's certified preparation integrals.
    Does not call B's assemble, cut_stress, local_tail, or analytic functions.
    """
    evo=HERE.parent
    finite=json.loads((evo/"propagation/result.json").read_text())
    extra=json.loads((evo/"propagation/extra_eta0_256.json").read_text())
    archive=json.loads((evo/"stress/tail_K256_M1024.json").read_text())
    target=next(x for x in archive["targets"] if x["eta"]=="0")
    assert archive["K"]==target["K"]==256 and target["ibp_phase_positive"]
    def read(x):return bg.box(Q(x[0]),Q(x[1]))
    D=I(bg.upper(read(target["integration_D5"])))
    V=I(bg.upper(read(target["integration_Hvariation"])))
    N=I(bg.upper(read(target["integration_N11"])))
    J=3072
    dmax=Q(1,(J+1)**2)
    d=bg.Jet([bg.box(0,dmax),1,0,0])
    a=1+d
    b=a-2*d*d/a
    # At eta0: q=1,q'=0,q''=8,q'''=0,q''''=256,h=0.
    rn=(16-2*d)/(a*a*b)
    g=(b+1-d)/(2*b.sqrt())
    local=I(bg.absmax(g.c[3]))/(2*J*J)
    hj=rn/(4*b+2*d*d*d*rn)
    hmax=I(bg.absmax(hj.c[0]))
    r_inverse=(2+2*I(dmax)/I(bg.lower(a.c[0])))/iv.sqrt(I(bg.lower(b.c[0])))
    rapidity=D/(J+1)**5
    cosh=(iv.exp(rapidity)+iv.exp(-rapidity))/2
    sinh=(iv.exp(rapidity)-iv.exp(-rapidity))/2
    cosh2=(iv.exp(2*rapidity)+iv.exp(-2*rapidity))/2
    ab5=D*cosh2
    beta6=cosh*(hmax+V)+sinh*N/(J+1)**5
    ab6=cosh*beta6
    far5=ab5*r_inverse/(3*J**3)+local
    far6=ab6*r_inverse/(4*J**4)+local
    pref=1/(36*iv.pi**2)
    far_upper=I(min(bg.upper(far5),bg.upper(far6)))*pref
    far_lower=-I(bg.upper(far_upper))
    L=iv.log(I(Q(3,4)))+2*iv.euler
    analytic=(58+45*L)/(8640*iv.pi**2)
    results=[]
    modes=list(finite["targets"]["0"]["modes"])
    for K in (64,256):
        if K==256:modes+=extra["targets"]["0"]["modes"]
        assert [r["k"] for r in modes]==list(range(2,K+1))
        # Exactly one k1 subtraction, raw Gaussian energy=1/2.
        raw=I(Q(-3,8))
        for r in modes:
            k=r["k"]
            raw+=k*k*read(r["e"])-k**3+I(k)/2-I(Q(3,8*k))
        cut=raw*pref+analytic
        middle=-I(bg.upper(pref*(iv.log(I(J)/K)/2
            +I(1)/(32*K*K*(1-I(1)/(K+1)**2)))))
        full=I(bg.lower(cut+middle+far_lower))
        assert bg.lower(full)>mp.mpf(".5")
        results.append({"finite_K":K,"splice_J":J,
            "rho_cutoff":fm.decimal_box(cut),
            "middle_lower":fm.decimal_box(middle),
            "infinite_UV_lower":fm.decimal_box(far_lower),
            "full_rho_lower":fm.decimal_box(full),
            "exceeds_half":True})
    return {"method":"independent_eta0_closed_form_W2_and_finite_sum",
        "scope":"mu1_and_no_extra_finite_curvature_term",
        "rows":results,"geometry_acceleration_not_imposed_as_initial_data":True}


def run():
    frozen={str(p.relative_to(HERE.parent)):hashlib.sha256(p.read_bytes()).hexdigest()
        for p in [HERE.parent/"propagation/background.py",
                  HERE.parent/"propagation/finite_modes.py",
                  HERE.parent/"stress/tail.py",
                  HERE.parent/"propagation/result.json",
                  HERE.parent/"propagation/extra_eta0_256.json",
                  HERE.parent/"stress/tail_K256_M1024.json"]}
    result={"status":"INDEPENDENT_NARROW_ALGEBRA_AND_ANALYTIC_STEP_REVIEW",
        "source_sha256":frozen,
        "C_static_analytic_step":static_step_audit(),
        "B_W2_and_IBP":w2_algebra(),
        "B_finite_unresolved_gap":finite_gap_lower(),
        "initial_density_lower_independent_audit":initial_density_lower_audit(),
        "not_claimed":["full finite-mode replay","full UV numerical replay",
                       "physical coupling selected","finite hbar remainder"]}
    assert frozen=={name:hashlib.sha256((HERE.parent/name).read_bytes()).hexdigest()
                    for name in frozen}
    return result


def main():
    if not __debug__:raise RuntimeError("Review requires assertions; do not use -O")
    parser=argparse.ArgumentParser()
    parser.add_argument("--write",action="store_true")
    parser.add_argument("--check",action="store_true")
    args=parser.parse_args()
    result=run()
    path=HERE/"review_bc.json"
    if args.write:path.write_text(json.dumps(result,indent=2)+"\n")
    if args.check:assert result==json.loads(path.read_text())
    print(json.dumps({"status":result["status"],"check_passed":args.check,
        "static_negative_controls_rejected":3,
        "W2_residual_and_phase_identity":True,"receipt":str(path)},indent=2))


if __name__=="__main__":main()
