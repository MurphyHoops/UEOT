"""Taylor-Picard outward enclosure of the closed-FRW bounce and curved clock trajectory without ODEs."""
from common import iv,require,above,below,outward,finish
from model import geodesic_cap_spectrum,frw_bounce_enclosure,eval_frw

spec=geodesic_cap_spectrum(inv_r0=20,Kmax=16,nsub=64)
kh2=spec["khat"][1]

enc=frw_bounce_enclosure(alpha_G=iv.mpf(1)/10,lam_L=iv.mpf(550001)/1000000,N=220,T_end=iv.pi+3)
require(below(enc["R_u"],iv.mpf("2e-30")) and below(enc["R_up"],iv.mpf("2e-29")),"ultrahigh-precision Taylor-Picard enclosure")
# Check positivity of all even Taylor coefficients c[2k]
require(all(enc["coeffs"][2*k].a>0 for k in range(1,111)),"all even Taylor coefficients strictly positive")

ev_m1=eval_frw(enc,iv.mpf(-1))
ev_p2=eval_frw(enc,iv.mpf(1)/5)
ev_pi=eval_frw(enc,iv.pi)
ev_end=eval_frw(enc,iv.pi+3)

# Verify Friedmann equation residual (u')^2 - 4*Q(u) contains 0 at tau = -1, pi, pi+3
for label,ev in [("tau=-1",ev_m1),("tau=pi",ev_pi),("tau=pi+3",ev_end)]:
    u=ev["u"];up=ev["up"]
    f_res=up**2-4*(enc["lam_L"]*u**3-u**2+enc["beta_r"]*u+enc["alpha_G"])
    require(iv.mpf(0) in f_res and below(abs(f_res),iv.mpf("1e-27")),"Friedmann enclosure "+label)

# Verify curved positive-square threshold u(tau) <= u(pi+3) < 3/2 and strict non-staticity
require(above(ev_pi["ap"],iv.mpf("9.8e-5")) and above(ev_end["ap"],iv.mpf("0.012")) and above(ev_end["a"]-1,iv.mpf("0.0077")),"strictly non-static closed FRW")
require(below(ev_end["u"],iv.mpf("1.016")) and below(ev_end["u"],iv.mpf(3)/2),"curved positive-square bound u < 3/2")

# Background radiation budget after subtracting 6-channel Parseval frame
lam0=iv.mpf("2e-32")
delta_beta_frame=4*enc["alpha_G"]*lam0/(kh2**2)
beta_bg=enc["beta_r"]-delta_beta_frame
require(below(delta_beta_frame,iv.mpf("9e-33")) and above(beta_bg,iv.mpf("0.349998")),"positive background radiation")

# Exact analytic enclosure of theta(tau) = int_0^tau ds / u(s) via geometric series on w(s) = u(s) - 1 < 0.015
def enclose_clock_theta(tau_val):
    s_sign=iv.mpf(-1) if tau_val.b<0 else iv.mpf(1)
    T_abs=abs(tau_val)
    # Use w_max = eval_frw(enc, T_abs)["u"] - 1; compute exact polynomial powers of w_20(s) + remainder!
    # Even simpler and exact: truncate w to degree 40 (tail <= sum_{n=42}^100 c_n T^n + R_u)
    c=enc["coeffs"]
    w_trunc=[c[n] for n in range(41)];w_trunc[0]=iv.mpf(0)
    rem_w=sum(c[n]*(T_abs**n) for n in range(42,221))+enc["R_u"]
    w_hi=eval_frw(enc,T_abs)["u"]-1
    # Polynomial convolution powers p_m(s) = w_trunc(s)^m for m=0..10
    p_pow=[iv.mpf(1)]
    total=T_abs  # m=0 integral
    for m in range(1,11):
        nxt=[iv.mpf(0)]*(len(p_pow)+40)
        for i,vi in enumerate(p_pow):
            if vi==0:continue
            for j,vj in enumerate(w_trunc):
                if vj==0:continue
                nxt[i+j]+=vi*vj
        p_pow=nxt
        term_int=sum(cf*(T_abs**(deg+1))/(deg+1) for deg,cf in enumerate(p_pow) if cf!=0)
        total+=((-1)**m)*term_int
    # Error from replacing w by w_trunc in 1/(1+w) - 1/(1+w_trunc) <= rem_w * T_abs, plus geometric tail w_hi^11 * T_abs
    err=T_abs*(rem_w+(w_hi**11))
    return s_sign*(total+iv.mpf([-err.b,err.b]))

theta_m1=enclose_clock_theta(iv.mpf(-1))
theta_02=enclose_clock_theta(iv.mpf(1)/5)
theta_pi=enclose_clock_theta(iv.pi)
theta_end=enclose_clock_theta(iv.pi+3)

clock_lag_pi=iv.pi-theta_pi
clock_lag_end=(iv.pi+3)-theta_end
pulse_lag_02=(iv.mpf(1)/5)-theta_02
require(above(clock_lag_pi,iv.mpf("7e-5")) and above(clock_lag_end,iv.mpf("0.0094")),"curved clock differs strictly from coordinate time")
require(above(pulse_lag_02,0) and below(pulse_lag_02,iv.mpf("6e-9")),"tiny analytic clock shift on [-1/5, 1/5]")
# At encoding slice tau = pi and readout window tau >= pi+1, theta(pi) > 3.141 > 0.2 so F_{j,FRW}(theta(pi)) = 0 identically
require(above(theta_pi,iv.mpf("3.14")) and below(theta_02,iv.mpf("0.2")),"pulse support strictly separated from encoding and readout")

finish("dynamical_frw_clock_program.py",{
  "Taylor_polynomial_degree":220,
  "Picard_sup_error_R_u_upper":outward(enc["R_u"]),
  "Picard_derivative_error_R_up_upper":outward(enc["R_up"]),
  "a_at_minus_1":outward(ev_m1["a"]),
  "a_at_one_fifth":outward(ev_p2["a"]),
  "a_at_pi":outward(ev_pi["a"]),
  "a_prime_at_pi":outward(ev_pi["ap"]),
  "a_at_pi_plus_3":outward(ev_end["a"]),
  "u_max_on_window":outward(ev_end["u"]),
  "curved_square_bound_3_over_2_satisfied_everywhere":True,
  "parseval_frame_beta_contribution":outward(delta_beta_frame),
  "remaining_background_radiation_beta":outward(beta_bg),
  "curved_clock_theta_at_minus_1":outward(theta_m1),
  "curved_clock_theta_at_one_fifth":outward(theta_02),
  "curved_clock_theta_at_pi":outward(theta_pi),
  "curved_clock_theta_at_pi_plus_3":outward(theta_end),
  "curved_clock_lag_at_pi":outward(clock_lag_pi),
  "curved_clock_lag_at_pi_plus_3":outward(clock_lag_end),
  "geometry_ODE_integrations":0
},inputs=["physics/qm/null_source/timelike/finite_stress/lapse_boundary/renormalized_continuum/CRUNCH_VS_SUBCRITICAL_GRAVITY.md",
          "physics/qm/null_source/timelike/finite_stress/lapse_boundary/renormalized_continuum/PARSEVAL_ISOTROPIC_FRAME.md"])
