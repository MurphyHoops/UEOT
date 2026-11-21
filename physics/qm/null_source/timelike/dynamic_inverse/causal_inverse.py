"""Positive-real factor, causal inverse identities and short-window interval gains."""
import sympy as sp
from common import *
def result():
    y,b,r1,r2,W=sp.symbols("y b r1 r2 W",positive=True)
    weight=W/((b+r1)*(b+r2))
    assert sp.factor(weight/(b+y)-weight/b+weight*y/(b*(b+y)))==0
    gamma,tau=sp.symbols("gamma tau",real=True)
    s=gamma+sp.I*tau
    real=sp.simplify(sp.re(s/(s*s+b)))
    target=gamma*(gamma*gamma+tau*tau+b)/((gamma*gamma-tau*tau+b)**2+4*gamma*gamma*tau*tau)
    assert sp.simplify(real-target)==0
    # The exact integrals used in the Bromwich bounds.
    t=sp.symbols("t",real=True);g=sp.symbols("g",positive=True)
    assert sp.integrate((g*g+t*t)**sp.Rational(-3,2),(t,-sp.oo,sp.oo))==2/g**2
    assert sp.integrate(1/(g*g+t*t),(t,-sp.oo,sp.oo))==sp.pi/g
    fast=json.loads((HERE/"fast_root.json").read_text())
    kap=box(fast["fast_kappa_sigma_over_A"])
    rslow=SLOW*SLOW;rfast=kap*kap*X
    c=-characteristic_zero()/(rslow*rfast)
    gam=24*iv.sqrt(X)
    delta1=1-rslow/(576*X)
    delta2=1-kap*kap/576
    assert above(c) and above(delta1) and above(delta2)
    G0=1/(iv.pi*c*gam**3*delta1*delta2)
    G1=1/(2*c*gam**2*delta1*delta2)
    gain0=(iv.exp(1)-1)*G0/gam
    gain1=(iv.exp(1)-1)*G1/gam
    T=1/gam
    assert below(gain0,"1e-12") and below(gain1,"1e-5")
    assert above(kap*iv.sqrt(X)-3*SLOW,0)
    return {
      "renormalized_factor_identity":"-F(y)=c+sum mu_k*y/(y+b_k), c=-D(0)/(r1*r2)>0, mu_k=W_k/[b_k*(b_k+r1)*(b_k+r2)]>0",
      "positive_real_identity_exact":True,
      "positive_real_lower":"Re[-F(s^2)/s]>=c*Re(s)/abs(s)^2, Re(s)>0",
      "symbol_inverse_bound":"abs(1/P(s))<=1/[c*gamma*delta1*delta2*abs(s)^3], Re(s)=gamma>sigma_F",
      "delta_definition":"delta_j=1-r_j/gamma^2",
      "causal_G_regular_class":"C1, G(t)=0 for t<=0, G'(0)=0; G is an exponentially growable causal distribution inverse",
      "G_bound":"exp(gamma*t)/(pi*c*gamma^3*delta1*delta2)",
      "Gprime_bound":"exp(gamma*t)/(2*c*gamma^2*delta1*delta2)",
      "smooth_physical_test_domain":"f in C_c^infinity((0,infinity)); w=G*f is C-infinity with all zero-past jets and original incoming modes transported",
      "residual_test_forcing_is_added_physical_device":False,
      "both_positive_poles_retained":True,
      "stable_low_growth_inverse_exists":False,
      "past_slow_residual_convolution_automatically_converges":False,
      "chosen_gamma_over_A":24,
      "short_conformal_window":outward(T),
      "static_background_proper_duration":"1/24 model time units",
      "perturbed_exact_proper_duration":"Between exp(-norm(u))/24 and exp(norm(u))/24; not exactly 1/24",
      "c":outward(c),"delta_slow":outward(delta1),"delta_fast":outward(delta2),
      "G_prefactor":outward(G0),"Gprime_prefactor":outward(G1),
      "short_window_sup_w_per_sup_f":outward(gain0),
      "short_window_sup_wprime_per_sup_f":outward(gain1),
      "general_finite_T_gain":"G_prefactor*(exp(gamma*T)-1)/gamma",
      "derivative_bounds_for_smooth_f":"w^(m)=G*f^(m), with the same sup gain; not a bound for G'' itself",
      "seed_eta_0_1_nonlinear_error_certified":False,
      "complete_nonlinear_SCE_IVP_solved":False,
      "proof":"INVERSE.md"
    }
if __name__=="__main__":finish("causal_inverse.py",result(),["fast_root.py","fast_root.json"])
