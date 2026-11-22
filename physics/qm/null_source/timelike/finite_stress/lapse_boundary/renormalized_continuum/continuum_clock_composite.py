"""Uniform K<=infinity Friedrichs lower bound, continuum variances, Duhamel error and graph/Ward tails."""
import sympy as sp
from common import iv,box,load,require,above,below,outward,finish
from model import geodesic_cap_spectrum,power_tail_upper

jc="physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/"
prep=load(jc+"prepared_record.json")
load(jc+"clock_actuator.json");load(jc+"clock_uv.json");load(jc+"wick_clock_graph.json")

y,f,g_s,a_s,phi=sp.symbols("y f g a phi",real=True)
lhs=sp.Rational(3,8)*y**2+g_s*a_s*y*f*phi**2/2+g_s**2*f**2*phi**4/4
rhs=sp.Rational(3,8)*(y+sp.Rational(2,3)*g_s*a_s*f*phi**2)**2+g_s**2*(1-sp.Rational(2,3)*a_s**2)*f**2*phi**4/4
require(sp.expand(lhs-rhs)==0,"curved positive-square identity")

spec=geodesic_cap_spectrum(inv_r0=20,Kmax=512,nsub=64)
khat=spec["khat"];B_r0=spec["B_rho0"]
V=2*iv.pi**2;T=iv.mpf(8);a0=iv.mpf(4)
eta=iv.mpf(1)/10**13;g=iv.mpf(1)/10**40;ur=iv.mpf(1)/10**16
M0=iv.mpf(16);M1=iv.mpf(343);L0=iv.mpf(357)

# Continuum shift C_shift = 3/4 * sum_{k=1}^infty k^3 khat(k)^2 (tail exponent 20 - 3 = 17)
shift_512=iv.mpf(3)/4*sum((iv.mpf(k)**3)*(khat[k-1]**2) for k in range(1,513))
shift_tail=iv.mpf(3)/4*(B_r0**2)*power_tail_upper(17,512)
C_shift=iv.mpf([shift_512.a,(shift_512+shift_tail).b])
require(below(C_shift,iv.mpf("2.5e7")),"uniform K-independent vacuum shift")

# Continuum variances for X, Y, and body tadpole v_{rho0,infty} (tail exponent 20 - 1 = 19)
tail_19=(B_r0**2)*power_tail_upper(19,512)/(2*V)
vx_512=(a0+T*T/(4*a0))/V+sum(iv.mpf(k*k)*(khat[k-1]**2)/iv.sqrt(k*k-1) for k in range(2,513))/(2*V)
vy_512=sum(iv.mpf(k)*(khat[k-1]**2) for k in range(1,513))/(2*V)
vp_512=sum(iv.mpf(k*k)*(khat[k-1]**2)/iv.sqrt(k*k+iv.mpf(1)/5) for k in range(1,513))/(2*V)
# Note for k>=513, k/sqrt(k^2-1) <= 513/sqrt(513^2-1) < 1.000002
vx_inf=iv.mpf([vx_512.a,(vx_512+iv.mpf("1.00001")*tail_19).b])
vy_inf=iv.mpf([vy_512.a,(vy_512+tail_19).b])
vp_inf=iv.mpf([vp_512.a,(vp_512+tail_19).b])
require(below(vx_inf,110) and below(vy_inf,110) and below(vp_inf,110),"finite continuum smeared variances")

amp=iv.exp(2*29*ur/iv.sqrt(iv.mpf(6)/5))
vp_env=amp*vp_inf+iv.mpf("1e-18")
C1_inf=iv.sqrt(3)*V*T*vp_env/2*(iv.sqrt(vy_inf)*(M0+M1)+iv.sqrt(vx_inf)*ur*(L0+iv.mpf(10000)))
C2_inf=iv.sqrt(105)*V*T*(vp_env**2)/4*(M0*M0+M1*M1)
delta_inf=g*C1_inf+g*g*C2_inf
require(below(C1_inf,iv.mpf("1.1e8")) and below(C2_inf,iv.mpf("1e12")) and below(delta_inf,iv.mpf("1.2e-32")),"continuum Duhamel error")

# Continuum (K=infty) mathematical record gap: on [pi, pi+3] the reference body transfer under free H_r is state-independent
# (and even under cap-smearing K_{rho0} >= 0 with unit integral, Fubini + pointwise -G_{ps}(3, gamma) >= r/(8*pi) on [0.4, 2.6] preserves mu_lo)
mu_inf=box(prep["receiver_mean_unit_strength_lower"])
den=iv.sqrt(2*(iv.mpf("0.01")+eta**2*iv.mpf(9)/16))
arg=eta**2*mu_inf/den
gap_inf=2*arg/iv.sqrt(iv.pi)*iv.exp(-arg*arg)
actual_inf=gap_inf-2*delta_inf
require(above(actual_inf,iv.mpf("2.70e-30")),"continuum binary record gap")

# Graph tail above K=256 and cutoff commutator residual above K=256
v_tail_256=sum(iv.mpf(k*k)*(khat[k-1]**2)/iv.sqrt(k*k+iv.mpf(1)/5) for k in range(257,513))/(2*V)+tail_19
v_tail_512=tail_19
ward_comm_512=2*B_r0/(iv.mpf(512)**10)
require(below(v_tail_256,iv.mpf("0.01")) and below(v_tail_512,iv.mpf("2e-5")) and below(ward_comm_512,iv.mpf("4e-4")),"rapid UV tail decay")

Ecl=V*(1/(khat[0]**2)+(ur**2)/(khat[1]**2))/(2*g*g)
quartic_inf=3*g*g*V*(M0*M0+M1*M1)*(vp_inf**2)/4
E_ren_init=Ecl+1/(8*a0)+quartic_inf
require(below(E_ren_init,iv.mpf("1.02e81")),"finite renormalized continuum initial mean energy without K^4 zero-point")

finish("continuum_clock_composite.py",{
  "K":"infinity_with_512_explicit_plus_analytic_tail",
  "cap_radius_rad":"1/20",
  "g":"1e-40",
  "eta":"1e-13",
  "bare_zero_point_sum_removed_by_normal_ordering":True,
  "uniform_Friedrichs_lower_bound_shift":outward(C_shift),
  "curved_square_stability_max_a_squared":"3/2",
  "continuum_smeared_variances":{
    "X_rho0_infty":outward(vx_inf),
    "Y_rho0_infty":outward(vy_inf),
    "body_tadpole_v_rho0_infty":outward(vp_inf)
  },
  "continuum_Duhamel_linear_constant_upper":outward(C1_inf),
  "continuum_Duhamel_quadratic_constant_upper":outward(C2_inf),
  "continuum_joint_vector_error_upper":outward(delta_inf),
  "continuum_reference_binary_gap_lower":outward(gap_inf),
  "continuum_actual_binary_gap_lower":outward(actual_inf),
  "renormalized_initial_energy_mean_upper":outward(E_ren_init),
  "body_tadpole_tail_above_K256_upper":outward(v_tail_256),
  "body_tadpole_tail_above_K512_upper":outward(v_tail_512),
  "cutoff_commutator_residual_at_K512_upper":outward(ward_comm_512),
  "selfadjoint_realization_at_infinity":"Friedrichs_extension_of_uniformly_semibounded_form",
  "essential_selfadjointness_at_infinity_claimed":False,
  "pointlike_rho0_to_zero_limit_claimed":False
},inputs=[jc+"prepared_record.json",jc+"clock_actuator.json",jc+"clock_uv.json",jc+"wick_clock_graph.json",
          "physics/qm/null_source/timelike/finite_stress/lapse_boundary/renormalized_continuum/GEODESIC_CAP_KERNEL.md"])
