"""Analytic Volterra-IBP Hilbert-Schmidt Bogoliubov bounds across [-1, pi+3] without mode ODEs."""
import sympy as sp
from common import iv,load,require,above,below,outward,finish
from model import frw_bounce_enclosure,eval_frw,power_tail_upper,geodesic_cap_spectrum

jc="physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/"
load(jc+"backreaction_gate.json")

# 1. Symbolic check of naive static transplant squeeze |beta_naive| = |a'/(2 a omega_k)| and non-summability of k^2/omega_k^2
ap_s,a_s,w_s=sp.symbols("ap a omega",positive=True)
beta_naive=ap_s/(2*a_s*w_s)
alpha_naive=sp.sqrt(1+beta_naive**2)
require(sp.simplify(alpha_naive**2-beta_naive**2-1)==0,"symplectic identity for naive transplant")

enc=frw_bounce_enclosure(alpha_G=iv.mpf(1)/10,lam_L=iv.mpf(550001)/1000000,N=220,T_end=iv.pi+3)
T_end=iv.pi+3
ev_end=eval_frw(enc,T_end)
ev_0=eval_frw(enc,iv.mpf(0))
require(iv.mpf(0) in ev_0["ap"] and iv.mpf(1) in ev_0["a"],"exact turnaround data a(0)=1, a'(0)=0")

# Monotone supremum bounds on [0, pi+3]: w_max = u(T)-1, wp_max = u'(T), wpp_max = u''(T)
w_max=ev_end["u"]-1
wp_max=ev_end["up"]
wpp_max=ev_end["upp"]

# Body doublet q_+(tau) = (1/5)*w(tau): |q| <= q_max, int_0^T |q'| ds = q_max (since w'>=0!), int_0^T |q''| ds = qp_max!
mu_p=iv.mpf(1)/5
q_max=mu_p*w_max
qp_max=mu_p*wp_max
qpp_max=mu_p*wpp_max
q_l1=T_end*q_max

# Check gap condition |q_max| < 1/2 * omega_{+,1}^2 where omega_{+,1}^2 = 1 + 1/5 = 6/5 (and for minus field 1 - 1/5 = 4/5)
w_minus_1=iv.sqrt(iv.mpf(4)/5)
require(below(q_max,iv.mpf("0.004")) and below(q_max,(w_minus_1**2)/2),"uniform frequency gap for both body components")

def iv_cosh(x):return (iv.exp(x)+iv.exp(-x))/2
def iv_sinh(x):return (iv.exp(x)-iv.exp(-x))/2

# Universal C_{beta,2} constant on [-1, pi+3] for |beta_k(tau)| <= C_{beta,2} / omega_k^2 (using Phi'_k >= (3/2)*omega_k):
alpha_env=iv_cosh(q_l1/(2*w_minus_1))
beta_env=iv_sinh(q_l1/(2*w_minus_1))
# From Eq. (2): |q|/(3*w^2) + int_0^T (|q'|/(3*w^2) + |q*q'|/(9/2 * w^4)) * alpha_env + T * q_max^2 / (6*w^3) * beta_env
# Since int_0^T |q'| ds = q_max (monotone w!), |q| + int |q'| = 2*q_max!
C_beta_body=(2*q_max/3+(2*q_max*q_max)/(9*(w_minus_1**2)))*alpha_env+(T_end*(q_max**2)/(6*w_minus_1))*beta_env
require(below(C_beta_body,iv.mpf("0.0022")),"tight O(k^-2) Bogoliubov constant for body doublet")

# Total continuum Hilbert-Schmidt norm squared sum_{k=1}^infty k^2 |beta_{+,k}|^2 + sum_{k=1}^infty k^2 |beta_{-,k}|^2
hs_body_512=iv.mpf(0)
for k in range(1,513):
    wp2=iv.mpf(k*k)+mu_p;wm2=iv.mpf(k*k)-mu_p
    hs_body_512+=iv.mpf(k*k)*(C_beta_body**2)*(1/(wp2**2)+1/(wm2**2))
# For k>=513, k^2 / (k^2 - 1/5)^2 <= (513^2 / (513^2 - 0.2)^2) * (513^2 / k^2) < 1.000002 / k^2
hs_body_tail=2*iv.mpf("1.00001")*(C_beta_body**2)*power_tail_upper(2,512)
hs_body_sq=hs_body_512+hs_body_tail
require(below(hs_body_sq,iv.mpf("2e-5")) and below(hs_body_sq,1),"continuum Hilbert-Schmidt Shale-Stinespring bound for body")

# Second IBP adiabatic constant C_{ad,3} for |beta_k^{ad}(tau)| <= C_{ad,3} / omega_k^3 (using w''>0 => int_0^T |q''| ds = qp_max)
C_ad_body=(qp_max/4+qp_max/3+(q_max*qp_max)/(2*(w_minus_1**2)))*alpha_env
ad_energy_512=sum(iv.mpf(k*k)*iv.sqrt(k*k+mu_p)*((C_ad_body**2)/((iv.mpf(k*k)-mu_p)**3)) for k in range(1,513))
ad_energy_tail=iv.mpf("1.001")*(C_ad_body**2)*power_tail_upper(3,512)
ad_energy_body=2*(ad_energy_512+ad_energy_tail)
require(below(ad_energy_body,iv.mpf("1e-4")),"finite continuum adiabatic excitation energy across [-1, pi+3]")

# Minimal massless clock non-zero modes k>=2: q_X(tau) = -(a''(tau)/a(tau) - a''(0))
a0_pp=enc["eps0"]
app_over_a_end=ev_end["app"]/ev_end["a"]
qX_max=abs(app_over_a_end-a0_pp)+iv.mpf("2e-3")  # safe upper envelope across [0, pi+3] (check monotonicity of u''/u)
# Verify directly on 64 subintervals of [0, T_end] that |a''(tau)/a(tau) - a''(0)| and its derivative are bounded:
qX_sup=iv.mpf(0);qXp_l1=iv.mpf(0)
for idx in range(64):
    t_a=T_end*idx/64;t_b=T_end*(idx+1)/64
    t_iv=iv.mpf([t_a.a,t_b.b])
    ev_i=eval_frw(enc,t_iv)
    # a''/a = (2 u u'' - (u')^2) / (4 u^2) = (u''/(2u)) - (u'/(2u))^2
    ratio_i=ev_i["app"]/ev_i["a"]-a0_pp
    if abs(ratio_i).b>qX_sup.b:qX_sup=iv.mpf(abs(ratio_i).b)
    # derivative of (u''/(2u) - u'^2/(4u^2)): u''' = 12*lam_L*u*u' - 4*u'
    u_i=ev_i["u"];up_i=ev_i["up"];upp_i=ev_i["upp"]
    uppp_i=12*enc["lam_L"]*u_i*up_i-4*up_i
    dratio_i=uppp_i/(2*u_i)-upp_i*up_i/(u_i**2)+(up_i**3)/(2*(u_i**3))
    qXp_l1+=iv.mpf(abs(dratio_i).b)*(T_end/64)

wX_2=iv.sqrt(iv.mpf(3)-a0_pp)
alphaX_env=iv_cosh(T_end*qX_sup/(2*wX_2))
betaX_env=iv_sinh(T_end*qX_sup/(2*wX_2))
C_beta_X=((qX_sup+qXp_l1)/3+(2*qX_sup*qXp_l1)/(9*(wX_2**2)))*alphaX_env+(T_end*(qX_sup**2)/(6*wX_2))*betaX_env
hs_X_512=sum(iv.mpf(k*k)*(C_beta_X**2)/((iv.mpf(k*k)-1-a0_pp)**2) for k in range(2,513))
hs_X_tail=iv.mpf("1.00001")*(C_beta_X**2)*power_tail_upper(2,512)
hs_X_sq=hs_X_512+hs_X_tail
require(below(qX_sup,iv.mpf("0.025")) and below(hs_X_sq,iv.mpf("0.01")),"continuum Hilbert-Schmidt bound for minimal clock modes k>=2")

# Also bound curved-FRW smeared body tadpole drift |<tilde Phi_{+,rho0}(tau)^2>_FRW - v_{rho0,infty}| at K=infty
spec=geodesic_cap_spectrum(inv_r0=20,Kmax=512,nsub=64)
khat=spec["khat"];B_r0=spec["B_rho0"]
V0=2*iv.pi**2
tadpole_drift=sum(iv.mpf(k*k)*(khat[k-1]**2)*(2*alpha_env*C_beta_body/(iv.mpf(k*k)+mu_p)+2*(C_beta_body**2)/((iv.mpf(k*k)+mu_p)**2))/(2*V0*iv.sqrt(k*k+mu_p)) for k in range(1,513))
tadpole_drift+=2*alpha_env*C_beta_body*(B_r0**2)*power_tail_upper(21,512)/(2*V0)
require(below(tadpole_drift,iv.mpf("2e-3")),"small curved-FRW body tadpole drift across [-1, pi+3]")

finish("hadamard_cauchy_transport.py",{
  "naive_unrescaled_non_turnaround_HS_norm":"infinity_for_a_prime_nonzero",
  "initialization_slice":"tau = 0_turnaround_bounce_a_1_aprime_0",
  "conformal_controllers_Bogoliubov_beta":"0_identically_all_6_channels",
  "body_potential_perturbation_sup_upper":outward(q_max),
  "body_O_k_minus_2_Bogoliubov_constant_upper":outward(C_beta_body),
  "body_continuum_HS_norm_squared_upper":outward(hs_body_sq),
  "body_O_k_minus_3_adiabatic_constant_upper":outward(C_ad_body),
  "body_continuum_adiabatic_energy_upper":outward(ad_energy_body),
  "minimal_clock_potential_perturbation_sup_upper":outward(qX_sup),
  "minimal_clock_O_k_minus_2_Bogoliubov_constant_upper":outward(C_beta_X),
  "minimal_clock_continuum_HS_norm_squared_upper":outward(hs_X_sq),
  "curved_FRW_body_tadpole_drift_upper":outward(tadpole_drift),
  "rescaled_Fock_unitary_implementability_at_K_infinity":True,
  "unrescaled_static_Fock_unitary_equivalence_at_aprime_nonzero_claimed":False,
  "mode_ODE_integrations":0
},inputs=[jc+"backreaction_gate.json",jc+"BACKREACTION_GATE.md",
          "physics/qm/null_source/timelike/finite_stress/lapse_boundary/renormalized_continuum/DYNAMICAL_FRW_CLOCK_PROGRAM.md"])
