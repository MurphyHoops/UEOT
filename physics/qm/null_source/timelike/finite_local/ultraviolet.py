"""All-record full AE density/pressure bounds for the new Hadamard reference family."""
import json,sympy as sp
from common import *
def result():
    profile=json.loads((HERE/"profile.json").read_text())
    assert [q["strict_cap"] for q in profile["potential_jet_bounds"]]==[10,95,1615,32568,811690]
    # Verify the complete fourth-order WKB defect, not only a leading asymptotic term.
    p,a,b,a1,b1,a2,b2,V=sp.symbols("p a b a1 b1 a2 b2 V",nonzero=True)
    om=p+a/p+b/p**3;Q=om/p
    om1=a1/p+b1/p**3;om2=a2/p+b2/p**3
    # a=-V/2; b=(V''-V^2)/8=-(a''+2a^2)/4.
    defect=p*p+2*a-om*om-om2/(2*om)+3*om1**2/(4*om**2)
    explicit=p**(-4)*(-2*a*b-b*b/p**2-b2/(2*Q)+a2*(a+b/p**2)/(2*Q)+
                      sp.Rational(3,4)*(a1+b1/p**2)**2/Q**2)
    assert sp.factor((defect-explicit).subs(b,-(a2+2*a*a)/4))==0
    # Exact AE local tensor conversions and the nonlog coefficient.
    h,k,V,V1,V2,ell=sp.symbols("h k V V1 V2 ell",real=True)
    H1=-36*h*V1+36*h*h*V+18*V*V+36*k*h*h-18*k*k
    T1=-36*V2+72*h*V1-72*h*h*V+72*V*V+72*k*V-72*k*h*h
    J3=3*h**4+6*k*h*h+3*k*k
    L3=12*V*h*h-12*h**4+12*k*V-12*k*h*h
    Ae=h*h/2;Ce=V*V/8+h*h*V/4-h*V1/4
    Ap=Ae-V/3;Cp=-V*V/8+h*h*V/4-h*V1/4+V2/12
    E3=Ce+k*Ae/2-k*k/8;P3=Cp+k*Ap/2-k*k/24
    assert sp.expand(H1-144*E3)==0
    assert sp.expand((H1-T1)/3-144*P3)==0
    rho_an=-H1/4320+J3/720-H1/432+H1*(2+ell)/288-(h*h*V+k*h*h)/4
    rho_target=E3*(sp.Rational(19,30)+ell/2)+J3/720-(h*h*V+k*h*h)/4
    assert sp.expand(rho_an-rho_target)==0
    tau_an=-T1/4320+L3/720-T1/432+T1*(2+ell)/288-(
        4*h*V1-6*h*h*V+3*V*V+4*k*V-6*k*h*h+k*k)/8
    pressure_target=P3*(sp.Rational(19,30)+ell/2)+(J3-L3)/2160+(
        4*h*V1-8*h*h*V+3*V*V+4*k*V-8*k*h*h+k*k)/24
    assert sp.expand((rho_an-tau_an)/3-pressure_target)==0
    # Certified actual-mode remainder from the independently derived constants.
    V0,V1,V2,V3,V4=map(exact,[10,95,1615,32568,811690])
    H=exact(4)/3;L=exact(63)/40;P0=exact(16);cut=exact(17)
    aa=V0/2;aa1=V1/2;aa2=V2/2
    bb=(V2+V0**2)/8;bb1=(V3+2*V0*V1)/8
    bb2=(V4+2*V1**2+2*V0*V2)/8
    assert below(aa/P0**2+bb/P0**4,exact(1)/2)
    CR=2*aa*bb+bb**2/P0**2+bb2+aa2*(aa+bb/P0**2)+3*(aa1+bb1/P0**2)**2
    Cdelta=L*CR*iv.exp(V0*L/P0)
    D0=aa+bb/P0**2;D1=aa1+bb1/P0**2
    Yc=exact(3)/2+D1/P0**3+H/P0
    CA=iv.sqrt(Yc**2+1);CD=Cdelta*iv.sqrt((1+H/P0)**2+1)
    Cs=2*CA*CD+CD**2/P0**5
    Ce5=aa**2*D0+2*aa*bb+bb**2/P0**2+H**2*(aa*D0+bb)+H*(5*aa1*D0+2*bb1)+D1**2
    Cp5=Ce5+exact(2)/3*(2*aa*bb+bb**2/P0**2+2*D0**3)
    AE=H**2/2;AP=AE+V0/3
    CE=V0**2/8+H**2*V0/4+H*V1/4
    CP=V0**2/8+H**2*V0/4+H*V1/4+V2/12
    conv_e=1+AE+4*CE;conv_p=exact(1)/3+AP+4*CP
    tail4=exact(16)/(9*(cut-1))
    tail5=(exact(4)/3)**(exact(5)/2)/(2*(cut-1)**2)
    uv_e=Cs*tail4+Ce5*tail5+conv_e/(2*(cut-1)**2)
    uv_p=Cs*tail4+Cp5*tail5+conv_p/(2*(cut-1)**2)
    E1max=AE+exact(1)/2;P1max=AP+exact(1)/6
    E3max=CE+AE/2+exact(1)/8;P3max=CP+AP/2+exact(1)/24
    ellbox=iv.log(XC*iv.mpf([1,(exact(9)/8).b])**2/4)+2*iv.euler
    Jbox=iv.mpf([iv.log(cut).a,(1+iv.log(cut)).b])
    logfactor=abs(exact(19)/30+ellbox/2-Jbox)
    j3max=3*H**4+6*H**2+3
    l3max=12*V0*H**2+12*H**4+12*V0+12*H**2
    locale=E3max*logfactor+j3max/720+(H**2*V0+H**2)/4
    localp=P3max*logfactor+(j3max+l3max)/2160+(
        4*H*V1+8*H**2*V0+3*V0**2+4*V0+8*H**2+1)/24
    sum1=cut*(cut+1)/2;sum3=sum1**2
    ir=34*cut**2*(cut+1)**2/(8*iv.pi**2)
    thermal=4*NTHERMAL*34*iv.sqrt(3)/iv.pi**2
    rho_coefficient=ir+(sum3+E1max*sum1+uv_e+locale)/(2*iv.pi**2)+thermal
    p_coefficient=ir+(sum3/3+P1max*sum1+uv_p+localp)/(2*iv.pi**2)+thermal
    density_norm=exact(2)/3*LAMBDA2*rho_coefficient
    pressure_norm=exact(2)/3*LAMBDA2*p_coefficient
    assert below(density_norm,"0.0000042") and below(pressure_norm,"0.0000042")
    return {
      "state":"new auxiliary-static-past in-vacuum plus original k2 thermal occupation in that in-basis",
      "same_original_measured_high_Cauchy_state":False,
      "uniform_over_all_records_and_kappa_in_0_1":True,
      "positive_proper_tau_window":[0.0,0.1],
      "same_AE_mu_1_no_new_finite_counterterms":True,
      "full_log_kappa_cancellation":"H_K+0.5 log kappa lies in (log P,1+log P]",
      "fourth_order_WKB_defect_identity":True,
      "WKB_is_actual_state_definition":False,
      "WKB_used_only_to_bound_exact_modes":True,
      "P0":16,"P":17,"mode_defect_constant":outward(CR),
      "mode_solution_error_constant":outward(Cdelta),
      "exact_energy_pressure_difference_constant":outward(Cs),
      "energy_UV_bracket_upper":outward(uv_e),"pressure_UV_bracket_upper":outward(uv_p),
      "IR_physical_coefficient_upper":outward(ir),
      "AE_log_factor_absolute_enclosure":outward(logfactor),
      "thermal_physical_coefficient_upper":outward(thermal),
      "absolute_density_over_lambda_fourth_upper":outward(rho_coefficient),
      "absolute_pressure_over_lambda_fourth_upper":outward(p_coefficient),
      "density_mean_residual_normalized_by_3_lambda2_over_2":outward(density_norm),
      "pressure_mean_residual_normalized_by_3_lambda2_over_2":outward(pressure_norm),
      "nearby_exact_semiclassical_solution_proved":False,
      "proof":"ULTRAVIOLET.md"}
if __name__=="__main__":finish("ultraviolet.py",result(),["ULTRAVIOLET.md","profile.json"])
