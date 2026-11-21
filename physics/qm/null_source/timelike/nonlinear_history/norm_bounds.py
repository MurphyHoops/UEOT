"""Same-radius nonlinear RSET bounds, including every fixed AE and matter term."""
from common import *
def result():
    t=exact("0.1");H=t;M=t+t*t
    C5=(exact(4)/3)**2*iv.sqrt(exact(4)/3)/2
    Ulog=exact(7)/6*8/(3*iv.sqrt(3))
    assert below(Ulog,"1.8") and below(C5,"1.027")
    high_p=C5*(2*M**3/3+H*M*M/4)/(1-M/3)
    high_e=C5*(M**3+H*M*M/4)/(1-M/3)
    assert below(high_p,"0.00132") and below(high_e,"0.00175")
    # Finite Taylor remainders at d=1/k^2 <=1/4.
    # sqrt(1-d): third derivative /6; (1-d)^-1/2: second /2;
    # (1-d)^-3/2: first derivative.
    d=exact(1)/4
    coeff0=(exact(3)/8)*(1-d)**(-exact(5)/2)/6
    coeff1=(exact(3)/4)*(1-d)**(-exact(5)/2)/2
    coeff3=(exact(3)/2)*(1-d)**(-exact(5)/2)
    assert below(coeff0,1) and below(coeff1,1) and below(coeff3,4)
    Ap=H*H/2+M/3;Ae=H*H/2
    Cp=M*M/8+H*H*M/4+H*M/4+M/12
    Ce=M*M/8+H*H*M/4+H*M/4
    conversion_p=exact(1)/6+Ap/2+2*Cp
    conversion_e=exact(1)/2+Ae/2+2*Ce
    sum_p=M+M*M+H*M+high_p+conversion_p
    sum_e=M*M+H*M+high_e+conversion_e
    assert below(sum_p,1) and below(sum_e,1)

    a2=M;a3=t*(1+t)**2;a4=t*(1+t)**3
    H1=36*a3*H+72*a2*H*H+18*a2*a2+36*H*H+18
    T1=36*a4+144*a3*H+216*a2*H*H+108*a2*a2+72*a2+72*H*H
    H3=3*H**4+6*H*H+3
    T3=12*a2*H*H+12*H**4+12*a2+12*H*H
    ell0=iv.log(X/4)+2*iv.euler
    assert above(ell0) and below(ell0,26)
    ell_plus_2=2+ell0+2*t
    assert below(ell_plus_2,30)
    ra=(H1/6+H3)/2880+H1/1728+(H1*ell_plus_2/32+exact(9)/4*(H*H*a2+H*H))/36
    ta=(T1/6+T3)/2880+T1/1728+(T1*ell_plus_2/32+
       exact(9)/8*(4*a3*H+10*a2*H*H+3*a2*a2+4*a2+6*H*H+1))/36
    pa=(ra+ta)/3
    assert below(ra,1) and below(ta,1) and below(pa,exact(2)/3)
    P1=Ap+exact(1)/6;P3=Cp+Ap/2+exact(1)/24
    E1=Ae+exact(1)/2;E3=Ce+Ae/2+exact(1)/8
    pressure_bracket=exact(1)/3+P1+P3+sum_p+4*pa
    density_bracket=1+E1+E3+sum_e+4*ra
    assert below(pressure_bracket,5) and below(density_bracket,7)

    # Exact k=2 product sum; every geometry derivative follows from E4.
    omega=iv.sqrt(3)
    W=1+M/(2*omega**2*(1-M/omega**2))
    D2W=2*M/(1-M/omega**2)
    p2=(D2W/2+H*W+2*omega**2*W/3)/(2*omega)
    e2=(D2W/2+H*W+2*omega**2*W)/(2*omega)
    assert below(p2,1)
    xrhoz=X*RHOZ;xu=X*U0
    assert above(X,"6e9") and below(OCCUPATION,"0.02")
    assert below(xrhoz,"0.6") and below(xu,"1.01")
    classical=t+(H*H+1)/2+exact("0.6")*iv.exp(4*t)+exact("1.01")*iv.exp(2*t)
    vacuum=iv.exp(2*t)*pressure_bracket/(2*iv.pi**2*X)
    thermal=4*OCCUPATION*iv.exp(2*t)*p2/(iv.pi**2*X)
    full=classical+vacuum+thermal
    assert below(vacuum,"1e-9") and below(thermal,"1e-9") and below(full,4)
    return {
      "geometry_domain":"E4: sum (1+lambda)^4*log(e+lambda)*abs(u_nm)*Rz^n*Rw^m",
      "geometry_ball_radius":"0.1",
      "V_E2_upper":"0.11","h_E1_upper":"0.1",
      "same_coefficient_radius_no_loss":True,
      "density_and_pressure_holomorphic_on_ball":True,
      "weighted_kernel_log_constant_upper":outward(Ulog)[1],
      "sum_k_squared_over_omega_fifth_upper":outward(C5)[1],
      "pressure_high_Born_tail_upper":outward(high_p)[1],
      "density_high_Born_tail_upper":outward(high_e)[1],
      "omega_to_k_Taylor_coefficients":[outward(v) for v in [coeff0,coeff1,coeff3]],
      "K0_enclosure":["-1/2",0],"K1_enclosure":[0,"1/2"],"K3_enclosure":[0,2],
      "renormalized_pressure_mode_sum_upper":outward(sum_p)[1],
      "renormalized_density_mode_sum_upper":outward(sum_e)[1],
      "all_AE_local_tensor_bounds":[outward(v)[1] for v in [H1,T1,H3,T3]],
      "fixed_AE_density_trace_pressure_bounds":[outward(v)[1] for v in [ra,ta,pa]],
      "full_vacuum_pressure_bracket_upper":outward(pressure_bracket)[1],
      "full_vacuum_density_bracket_upper":outward(density_bracket)[1],
      "thermal_k2_pressure_upper":outward(p2)[1],
      "thermal_k2_density_upper":outward(e2)[1],
      "x_times_actual_zero_density":outward(xrhoz),
      "x_times_fixed_U0":outward(xu),
      "spatial_classical_ball_bound":outward(classical),
      "spatial_vacuum_ball_bound":outward(vacuum),
      "spatial_thermal_ball_bound":outward(thermal),
      "full_spatial_equation_ball_bound":outward(full),
      "chosen_holomorphic_majorant":4,
      "all_fixed_contacts_zero_thermal_retained":True,
      "seven_derivatives_or_exact_inverse_k_analyticity_assumed":False,
      "proof":"KERNELS.md"}
if __name__=="__main__":finish("norm_bounds.py",result(),["kernels.py","kernels.json"])
