"""Continuum (K=infinity) conformal-improved total Jacobian, Wick comparison, and H_{0,3}(X) form majorant."""
import sympy as sp
from common import iv,load,require,above,below,outward,finish
from model import geodesic_cap_spectrum,power_tail_upper

jc="physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/"
load(jc+"total_columns.json");load(jc+"quantified_preparation.json")

spec=geodesic_cap_spectrum(inv_r0=20,Kmax=512,nsub=64)
khat=spec["khat"];B_r0=spec["B_rho0"]
kh2=khat[1];inv_kh2=1/kh2
V0=2*iv.pi**2

# Exact symbolic check of the conformally improved finite-sensor retarded exchange identity Eqs. (2)-(3)
t=sp.Symbol("t",real=True)
k2,veff,u=sp.symbols("k2 veff u",positive=True)
c=sp.cos(2*t);cp=sp.diff(c,t)
F=sp.Function("F")(t);Fp=sp.diff(F,t)
z0=sp.Function("z0")(t);zX=sp.Function("zX")(t)
R_app=sp.diff(zX,t)+(cp*sp.diff(z0,t)+2*c*z0)*u/k2
J_app=zX+(sp.Rational(2,3)*c*sp.diff(z0,t)-sp.Rational(1,3)*cp*z0)*u/k2
lhs=sp.expand(sp.diff(R_app,t)+3*J_app)
subs_eq={sp.diff(z0,t,2):-z0-veff*F/2,sp.diff(zX,t,2):-3*zX-k2*veff*c*Fp*u/2}
lhs_eval=sp.simplify(lhs.subs(subs_eq))
rhs_expected=sp.simplify(-veff*(k2*c*Fp+cp*F/k2)*u/2)
require(sp.simplify(lhs_eval-rhs_expected)==0,"exact conformally improved finite-sensor retarded exchange balance")

# Continuum smeared body tadpole scale V0 * v_{rho0,infty} / 8
tail_19=(B_r0**2)*power_tail_upper(19,512)/(2*V0)
v_512=sum(iv.mpf(k*k)*(khat[k-1]**2)/iv.sqrt(k*k+iv.mpf(1)/5) for k in range(1,513))/(2*V0)
v_inf=iv.mpf([v_512.a,(v_512+tail_19).b])
scale_inf=V0*v_inf/8
require(above(scale_inf,iv.mpf("250.7")) and below(scale_inf,iv.mpf("250.8")),"continuum tadpole scale")

# Outward interval bounds for conformally improved 2x2 controller matrix Eq. (4) at T = pi
a=iv.sqrt(3);S=iv.sin(a*iv.pi);C=iv.cos(a*iv.pi);d=iv.cos(iv.mpf(2)/5);m=iv.mpf(14)/1875
ul=kh2*(1-(iv.mpf(3)/2+4/d)*m)
ru=inv_kh2*(1+2*m/d)
vl=kh2*(7-(iv.mpf(21)/2+12/d)*m)
vu=kh2*(3+4/d**2)
qu=inv_kh2*(1+(2/d+4/d**2)*m)
pos_term=3*ul-2*C*ru
neg_term=6*C*ul-4*ru
require(above(pos_term) and below(neg_term,0),"conformally improved determinant signs")
detlo=pos_term*vl+neg_term*qu
require(above(detlo,iv.mpf("10.0")),"conformally improved controller determinant lower bound > 10")
fro2=(abs(S)*a*kh2)**2+(C*vu+2*qu)**2+((2*ru-3*C*ul)**2)+(3*abs(S)*vu/a)**2
frob=iv.sqrt(fro2)
require(below(frob,iv.mpf("13.5")),"conformally improved controller Frobenius upper")

inv_ctrl=frob/(detlo*scale_inf)
require(below(inv_ctrl,iv.mpf("0.0054")) and below(6*inv_ctrl,1),"continuum controller inverse bound")
tot_inv_unsub=inv_ctrl/(1-6*inv_ctrl)
require(below(tot_inv_unsub,iv.mpf("0.0056")),"continuum unsubtracted total Jacobian inverse bound")

# Vacuum-subtracted (v_eff = 0) comparison: lower-bound shift and matter-only continuum inverse
g=iv.mpf(1)/10**40;M0=iv.mpf(16);M1=iv.mpf(343)
wick_shift=iv.mpf(1)/2*(g**2)*V0*(v_inf**2)*(M0*M0+M1*M1)
require(below(wick_shift,iv.mpf("2e-69")),"finite-sensor Wick subtraction preserves uniform lower bound")
require(all(khat[k-1].a>0 and khat[k].a>0 for k in range(1,278)),"strictly positive pair weights on 1<=k<=277")
first_pair_factor=khat[0]*khat[1]
require(above(first_pair_factor,iv.mpf("0.99982")),"first-pair cap weight khat(1)*khat(2)")
osc_278_511=sum(abs(khat[k-1]*khat[k])*iv.mpf(5930)/(iv.mpf(k)**4) for k in range(278,512))
osc_512_inf=(B_r0**2)*iv.mpf(5930)*power_tail_upper(24,511)
matter_osc_tail=osc_278_511+osc_512_inf
require(below(matter_osc_tail,iv.mpf("1e-9")),"negligible high-k matter oscillating tail")
a_lo=first_pair_factor*(iv.mpf(9)/10000)-matter_osc_tail
app_lo=9*first_pair_factor*(iv.mpf(9)/10000)-matter_osc_tail
det_matter_lo=a_lo*app_lo
matter_only_inv_upper=6/det_matter_lo
require(above(det_matter_lo,iv.mpf("7.28e-6")) and below(matter_only_inv_upper,iv.mpf("1e6")),"vacuum-subtracted matter-only continuum inverse bound")

# Minimal-clock H_{0,3}(X) Sobolev commutator variance sum_{k=2}^infty k^2/(2 V0 sqrt(k^2-1)) * (k^6 |khat(k)|)^2
h03_512=sum(iv.mpf(k*k)*(iv.mpf(k)**12)*(khat[k-1]**2)/iv.sqrt(k*k-1) for k in range(2,513))
h03_tail=iv.mpf("1.00001")*(B_r0**2)*power_tail_upper(7,512)
h03_comm_var=iv.mpf([h03_512.a,(h03_512+h03_tail).b])/(2*V0)
sobolev_cs_const=iv.pi/iv.sqrt(6)
require(below(h03_comm_var,iv.mpf("1e30")) and below(sobolev_cs_const,iv.mpf("1.29")),"finite continuum H_{0,3}(X) commutator variance")

# Contraction of the continuum limiting/parametrix total response map F_{total,lim}^{rho0,infty} on ||u|| <= 1e-16
r0=iv.mpf("1e-16");x=58*r0;C0=iv.mpf("1e8")
app_rem=2*C0*x*x
limiting_L=tot_inv_unsub*(iv.mpf("4.096e-9")+app_rem)
target=iv.mpf("5e-23")
require(below(limiting_L,iv.mpf("3e-11")) and below(tot_inv_unsub*target+limiting_L*r0,r0.a),"continuum limiting total-map contraction")

finish("continuum_tadpole_columns.py",{
  "cap_radius_rad":"1/20",
  "controller_coupling":"conformally_coupled_massless_xi_1_over_6_with_improvement_tensor",
  "continuum_tadpole_scale_V0_v_over_8":outward(scale_inf),
  "sensor_nonlocality_dipole_gap_khat2_minus_inv_khat2":outward(kh2-inv_kh2),
  "smeared_controller_determinant_lower":outward(detlo),
  "smeared_controller_Frobenius_upper":outward(frob),
  "continuum_controller_inverse_norm_upper":outward(inv_ctrl),
  "continuum_unsubtracted_total_inverse_norm_upper":outward(tot_inv_unsub),
  "wick_subtracted_lower_bound_shift_at_g_1e_40_upper":outward(wick_shift),
  "positive_pair_weight_cutoff_k":277,
  "first_pair_cap_weight_khat1_khat2":outward(first_pair_factor),
  "matter_high_mode_oscillating_tail_upper":outward(matter_osc_tail),
  "continuum_wick_subtracted_matter_det2_lower":outward(det_matter_lo),
  "continuum_wick_subtracted_matter_inverse_norm_upper":outward(matter_only_inv_upper),
  "max_resonant_counterterm_values_per_dipole_block":2,
  "sobolev_H03_X_Cauchy_Schwarz_constant":outward(sobolev_cs_const),
  "continuum_H03_X_commutator_variance_upper":outward(h03_comm_var),
  "continuum_limiting_map_contraction_factor_upper":outward(limiting_L),
  "sharp_slice_inverse_scope":"continuum_limiting_and_parametrix_total_map_on_Q_H03_X",
  "nonperturbative_Friedrichs_H03_X_domain_invariance_claimed":False,
  "target_ball_radius":"5e-23",
  "control_ball_radius":"1e-16",
  "both_unsubtracted_and_wick_subtracted_schemes_invertible_at_infinity":True,
  "pointlike_rho0_to_zero_scheme_independence_claimed":False
},inputs=[jc+"total_columns.json",jc+"quantified_preparation.json",
          "physics/qm/null_source/timelike/finite_stress/lapse_boundary/renormalized_continuum/CONTINUUM_CLOCK_COMPOSITE.md"])
