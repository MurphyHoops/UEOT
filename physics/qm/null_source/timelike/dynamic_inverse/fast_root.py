"""Directed full infinite-response fast-root, derivative and residue enclosures."""
from common import *
K=256
def H_enclosure(d,method="em"):
    assert above(d,0)
    finite=sum((d/(k*(k*k+d)) for k in range(2,K+1)),iv.mpf(0))
    if method=="monotone":
        lo=finite+iv.log(1+d/(K+1)**2)/2
        hi=finite+iv.log(1+d/K**2)/2
    else:
        t=iv.mpf(K)
        f=d/(t*(t*t+d))
        fp=-1/(t*t)+(t*t-d)/(t*t+d)**2
        fppp=-6/t**4+6*(t**4-6*t*t*d+d*d)/(t*t+d)**4
        upper=iv.log(1+d/t**2)/2-f/2-fp/12
        assert below(fppp,0)
        lo=finite+upper+fppp/720
        hi=finite+upper
    return interval(lo.a,hi.b)
def evaluate(kappa,method="em"):
    # kappa=s/sqrt(x) is a correlated argument, not an independently chosen s.
    y=kappa*kappa*X;d=y/4-1;H=H_enclosure(d,method)
    R=interval((H/(8*d)).a,(H/(6*d)).b)
    Dnum=-1+y/2-y*y/12-y*(d+iv.mpf(1)/2)*H/3+y*R/3
    Z=Dnum+CA(X)*y*y/360-(CA(X)-29)*y/180-iv.mpf(1)/24
    Dy=y-4+2/X*(iv.mpf(8)/3*B(X)-D0+Z/(4*iv.pi**2))+4*JN/(3*X)*(y+24)/(y+12)
    if method=="monotone":return Dy/y
    # Exact cancellation of correlated log(x) and C*y, not a new AE prescription.
    t=iv.mpf(K)
    f=d/(t*(t*t+d))
    fp=-1/(t*t)+(t*t-d)/(t*t+d)**2
    fppp=-6/t**4+6*(t**4-6*t*t*d+d*d)/(t*t+d)**4
    finite_harmonic=sum((iv.mpf(1)/k for k in range(2,K+1)),iv.mpf(0))
    finite_correction=sum((k/(k*k+d) for k in range(2,K+1)),iv.mpf(0))
    L=-iv.mpf(11)/30+iv.euler-finite_harmonic+finite_correction+iv.log(K)
    L-=iv.log(kappa*kappa+4*(K*K-1)/X)/2
    L+=f/2+fp/12+interval(0,(-fppp/720).b)
    C=1/(2*iv.pi**2*X)
    c0=-4+(iv.mpf(16)/3*B(X)-2*D0)/X-25*C/24+4*JN/(3*X)*(y+24)/(y+12)
    stable=1+kappa*kappa*L/(24*iv.pi**2)+C*(iv.mpf(89)/180-L/6+R/3)+c0/y
    # Both forms enclose the same exact expression; their intervals must overlap.
    assert not (stable.b<(Dy/y).a or stable.a>(Dy/y).b)
    return stable
def root_derivative(kappa):
    y=kappa*kappa*X;d=y/4-1;H=H_enclosure(d)
    R=interval((H/(8*d)).a,(H/(6*d)).b)
    gmax=9/(16*iv.sqrt(3)*d**iv.mpf("1.5"))
    Hp=interval((1/(2*(d+iv.mpf(9)/4))-gmax).a,
                (1/(2*(d+iv.mpf(9)/4))+gmax).b)
    J=interval(0,(H/(6*d*d)).b)
    C=1/(2*iv.pi**2*X)
    p=1+C*(iv.mpf(1)/2-(CA(X)-29)/180)
    c0=-4+(iv.mpf(16)/3*B(X)-2*D0)/X-25*C/24+4*JN/(3*X)*(y+24)/(y+12)
    c0p=-16*JN/(X*(y+12)**2)
    # Exact root equation eliminates the cancellation-prone quadratic coefficient.
    deriv=-p-2*c0/y+c0p-C*(H/6+R/3+y*(y-2)*Hp/48+y*J/12)
    return deriv
def result():
    signs=[]
    for name in ["11.45","11.47"]:
        k=iv.mpf(name)
        em=evaluate(k);mono=evaluate(k,"monotone")
        if name=="11.45":assert above(em) and above(mono)
        else:assert below(em,0) and below(mono,0)
        signs.append({"kappa":name,"D_over_y_EM":outward(em),"D_over_y_monotone":outward(mono)})
    lo=iv.mpf("11.45");hi=iv.mpf("11.47")
    iterations=0
    for _ in range(32):
        mid=(lo+hi)/2;v=evaluate(mid)
        if above(v):lo=mid
        elif below(v,0):hi=mid
        else:
            low_probe=(3*lo+hi)/4;high_probe=(lo+3*hi)/4
            vl=evaluate(low_probe);vh=evaluate(high_probe)
            changed=False
            if above(vl):lo=low_probe;changed=True
            if below(vh,0):hi=high_probe;changed=True
            if not changed:break
        iterations+=1
    kappa=interval(lo.a,hi.b)
    assert above(evaluate(lo)) and below(evaluate(hi),0)
    deriv=root_derivative(kappa)
    assert above(deriv,"-1.28") and below(deriv,"-1.27")
    ds_over_A=2*kappa*deriv
    assert above(ds_over_A,-30) and below(ds_over_A,-29)
    residue_times_A=1/ds_over_A
    assert above(residue_times_A,-iv.mpf(1)/29) and below(residue_times_A,-iv.mpf(1)/30)
    sf=kappa*iv.sqrt(X)
    assert above(sf,2*SLOW.b)
    # Root-independent analytic quadrature width, before input interval dependency.
    em_width=iv.mpf(1)/(120*K**4)
    assert below(em_width,"2e-12")
    return {
      "full_fixed_AE_and_thermal_response":True,
      "coarse_root_signs":signs,
      "fast_kappa_sigma_over_A":outward(kappa),
      "fast_conformal_growth_rate":outward(sf),
      "fast_proper_growth_rate_model_units":outward(kappa),
      "root_y_derivative":outward(deriv),
      "root_s_derivative_divided_by_A":outward(ds_over_A),
      "fast_pole_residue_times_A":outward(residue_times_A),
      "fast_to_slow_rate_ratio":outward(sf/SLOW),
      "fast_greater_than_twice_slow":True,
      "finite_terms_per_H_sum":K-1,
      "bisection_sign_updates":iterations,
      "EM_tail_width_at_fixed_d_upper":outward(em_width)[1],
      "EM_tail_proof":"Positive Laplace weight and exact coth partial fractions; SPECTRUM.md",
      "EM_lower":"I_K-f(K)/2-f'(K)/12+f'''(K)/720",
      "EM_upper":"I_K-f(K)/2-f'(K)/12",
      "R_bounds":"H/(8d)<R<H/(6d)",
      "Hprime_bounds":"1/(2*(d+9/4)) +/- 9/(16*sqrt(3)*d^(3/2))",
      "J_bounds":"0<=-R_d'<=H/(6d^2)",
      "correlated_logx_and_Cy_cancellation_exact":True,
      "rate_is_SI_seconds_inverse":False,
      "old_positive_root_reused":outward(SLOW),
      "nonlinear_exact_solution_constructed":False
    }
if __name__=="__main__":finish("fast_root.py",result())
