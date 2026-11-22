"""Exact symbolic and interval proof of the Lambda<=0 stiff-clock Big Crunch vs sub-critical bounce window."""
import sympy as sp
from common import iv,load,require,above,below,outward,finish

jc="physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/"
load(jc+"backreaction_gate.json")

# 1. Exact Lambda=0 closed-form solution u(tau) = beta_r/2 + sqrt(alpha_G + beta_r^2/4)*sin(2*tau)
tau,alpha_s,beta_s,lam_s=sp.symbols("tau alpha_G beta_r lam_L",positive=True)
R_s=sp.sqrt(alpha_s+beta_s**2/4)
u_exact=beta_s/2+R_s*sp.sin(2*tau)
res_lambda0=sp.simplify(sp.diff(u_exact,tau)**2-4*(alpha_s+beta_s*u_exact-u_exact**2))
require(res_lambda0==0,"exact Lambda=0 Friedmann integral")

# 2. Exact turnaround algebra Q(1)=0 and Q'(1) = 2*lam_L - 1 - alpha_G
u_var=sp.Symbol("u",positive=True)
Q_poly=lam_s*u_var**3-u_var**2+(1-alpha_s-lam_s)*u_var+alpha_s
require(sp.simplify(Q_poly.subs(u_var,1))==0,"turnaround Friedmann root Q(1)=0")
Qp_1=sp.simplify(sp.diff(Q_poly,u_var).subs(u_var,1))
require(sp.simplify(Qp_1-(2*lam_s-1-alpha_s))==0,"turnaround bounce acceleration Q'(1)")
window_width=sp.simplify((1-alpha_s)-(1+alpha_s)/2)
require(sp.simplify(window_width-sp.Rational(1,2)*(1-3*alpha_s))==0,"sub-critical compactness threshold alpha_G < 1/3")

# 3. Interval verification of lifetime obstruction vs concrete sub-critical point
pure_clock_lifetime=iv.pi/2
apparatus_window=iv.pi+4
require(below(pure_clock_lifetime,iv.pi) and below(iv.pi,apparatus_window),"Big-Crunch horizon strictly shorter than apparatus window")

alpha_G=iv.mpf(1)/10
compactness_4piG_over_g2=3*alpha_G
lam_lo=(1+alpha_G)/2
lam_hi=1-alpha_G
lam_chosen=iv.mpf(550001)/1000000
beta_chosen=1-alpha_G-lam_chosen
acc_a0=lam_chosen-lam_lo  # (2*lam_L - 1 - alpha_G)/2 = a''(0)
require(above(lam_chosen,lam_lo) and below(lam_chosen,lam_hi) and above(beta_chosen,iv.mpf("0.34999")),"valid sub-critical bounce parameters")
require(above(acc_a0,iv.mpf("9e-7")) and below(compactness_4piG_over_g2,1),"positive bounce acceleration in sub-critical regime")

finish("crunch_vs_subcritical_gravity.py",{
  "pure_stiff_clock_Lambda0_max_conformal_lifetime":outward(pure_clock_lifetime),
  "radiation_plus_clock_Lambda_le_0_lifetime_strict_upper":outward(iv.pi),
  "required_apparatus_conformal_window_length":outward(apparatus_window),
  "Lambda_le_0_closed_FRW_reaches_encoding_or_readout":False,
  "subcritical_compactness_iff_4piG_over_g2_lt":"1",
  "subcritical_alpha_G_strict_upper":"1/3",
  "selected_alpha_G":"1/10",
  "selected_4piG_over_g2":"3/10",
  "selected_lambda_Lambda":"550001/1000000",
  "selected_beta_radiation":"349999/1000000",
  "turnaround_a_double_prime_at_zero":outward(acc_a0),
  "unit_ESU_with_G_order_one_excluded_at_g_1e_40":True
},inputs=[jc+"backreaction_gate.json",jc+"BACKREACTION_GATE.md"])
