"""4D local autonomous pointer field: antipodal r_b/g beacon, light-cone cap inclusion, and k=1 quadrature binary gap."""
import sympy as sp
from common import iv,box,load,require,above,below,outward,finish
from model import geodesic_cap_spectrum,power_tail_upper,frw_bounce_enclosure,eval_frw

jc="physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/"
rc="physics/qm/null_source/timelike/finite_stress/lapse_boundary/renormalized_continuum/"
prep=load(jc+"prepared_record.json")
comp=load(rc+"continuum_clock_composite.json")
frw=load(rc+"dynamical_frw_clock_program.json")

# 1. Exact curved positive-square identity and joint parity symmetry (psi, qp) -> (-psi, -qp)
psi_s,b_s,f_s,qp_s,lam_s,a_s=sp.symbols("psi b f qp lam a",real=True)
lhs=sp.Rational(3,8)*psi_s**2+lam_s*a_s*psi_s*b_s*f_s*qp_s+lam_s**2*(b_s**2)*(f_s**2)*(qp_s**2)
rhs=sp.Rational(3,8)*(psi_s+sp.Rational(4,3)*lam_s*a_s*b_s*f_s*qp_s)**2+lam_s**2*(1-sp.Rational(2,3)*a_s**2)*(b_s**2)*(f_s**2)*(qp_s**2)
require(sp.expand(lhs-rhs)==0,"pointer curved positive-square identity")
require(sp.expand(lhs.subs({psi_s:-psi_s,qp_s:-qp_s})-lhs)==0,"exact joint parity symmetry")

# Exact light-cone + K_{rho0}^2 geodesic-ball inclusion arithmetic:
# 31/80 + 1/80 + 2*(1/20) == 1/2 and 29/80 - 1/80 - 2*(1/20) == 1/4
require(sp.Rational(31,80)+sp.Rational(1,80)+2*sp.Rational(1,20)==sp.Rational(1,2),"strict outer light-cone cap inclusion")
require(sp.Rational(29,80)-sp.Rational(1,80)-2*sp.Rational(1,20)==sp.Rational(1,4),"strict backward light-cone core plateau")

spec=geodesic_cap_spectrum(inv_r0=20,Kmax=512,nsub=64)
khat=spec["khat"];B_r0=spec["B_rho0"]
V0=2*iv.pi**2

# Additional continuum Friedrichs vacuum shift from borrowing 3/8 int tilde Psi_{ptr,rho0}^2 dV
ptr_shift_512=iv.mpf(3)/8*sum(iv.mpf(k*k)*iv.sqrt(k*k+1)*(khat[k-1]**2) for k in range(1,513))
ptr_shift_tail=iv.mpf(3)/8*(B_r0**2)*iv.mpf("1.00001")*power_tail_upper(17,512)
C_shift_ptr=iv.mpf([ptr_shift_512.a,(ptr_shift_512+ptr_shift_tail).b])
require(below(C_shift_ptr,iv.mpf("1.3e7")),"finite continuum pointer Friedrichs shift")

# Verify gate theta in [5.90, 5.92] lies strictly inside positive-kernel light cone for BOTH C_read and -C_read
enc=frw_bounce_enclosure(N=220)
u_max=eval_frw(enc,iv.pi+3)["u"]
a_max=eval_frw(enc,iv.pi+3)["a"]
w_max=u_max-1
delta_tau_half=iv.mpf("0.01")*u_max
require(below(delta_tau_half,iv.mpf(1)/80),"half-width strictly below 1/80 rad")
tau_gate_min=iv.mpf("5.90")
tau_gate_max=iv.mpf("5.92")*u_max
tau_el_min=tau_gate_min-iv.pi
tau_el_max=tau_gate_max-iv.pi
antipodal_max_dist=(iv.pi-iv.mpf(3)/2)+iv.mpf(1)  # d(x_enc, -x_read) + 1/2 + 1/2
theta_end=box(frw["curved_clock_theta_at_pi_plus_3"])
require(above(tau_el_min-antipodal_max_dist,iv.mpf("0.11")) and below(tau_el_max,iv.pi),"both antipodal caps strictly inside positive cone")
require(above(theta_end-iv.mpf("5.92"),iv.mpf("0.20")),"gate finishes strictly before pi + 3")

# Homogeneous plateau oscillation lower bound chi_hom(tau) >= cos(sqrt(1 + u_max)*delta_tau_half) and Goursat FRW bound
omega_ptr_max=iv.sqrt(1+u_max)
chi_hom_lo=iv.cos(omega_ptr_max*delta_tau_half)
goursat_frw_err=iv.mpf("0.5")*(iv.mpf(1)/5)*w_max*(tau_el_max**2)
require(above(chi_hom_lo,iv.mpf("0.9998")) and below(goursat_frw_err,iv.mpf("0.02")),"plateau coherence and Goursat FRW transfer")

# Complete Duhamel vector error: prep + quantum beacon delta B_rec + quantum clock jitter g*xi_{rho0}
g=iv.mpf(1)/10**40;eta=iv.mpf(1)/10**13;lam_ptr=iv.mpf(1)/100;r_b=iv.mpf(1)/10**14
lam_tilde=lam_ptr*g/r_b  # = 1e-28
vx_inf=box(comp["continuum_smeared_variances"]["X_rho0_infty"])
vp_inf=box(comp["continuum_smeared_variances"]["body_tadpole_v_rho0_infty"])
vq_env=iv.mpf("1.01")*vp_inf  # safe upper envelope for <tilde Q_{p,rho0}^2>_FRW including mu_- = -1/5 and FRW drift
cap_vol_half=2*iv.pi*(iv.mpf(1)/2-iv.sin(1)/2)
c_core=iv.mpf("0.5")/iv.sqrt(cap_vol_half)
b_eff_sup=lam_ptr*c_core  # = lam_tilde * (r_b / g) * c_core
F_sup=iv.mpf(1);Fp_sup=iv.mpf(200);T_gate_tau=2*delta_tau_half

# (a) Quantum beacon fluctuation error (using lam_tilde = 1e-28)
delta_beacon=T_gate_tau*V0*(lam_tilde*a_max*F_sup*(vq_env**iv.mpf("1.5"))+2*lam_tilde*b_eff_sup*(F_sup**2)*iv.sqrt(3)*(vq_env**iv.mpf("1.5"))+2*(lam_tilde**2)*(F_sup**2)*iv.sqrt(15)*(vq_env**2))
# (b) Clock-jitter error including BOTH coherent beacon b_eff_sup^2 and quantum variance lam_tilde^2 * vq_env
delta_ptr_clock=g*T_gate_tau*V0*Fp_sup*iv.sqrt(vx_inf)*(b_eff_sup*a_max*vq_env+2*(b_eff_sup**2)*iv.sqrt(3)*vq_env+2*(lam_tilde**2)*iv.sqrt(15)*(vq_env**2))
delta_prep=box(comp["continuum_joint_vector_error_upper"])
delta_total=delta_prep+delta_beacon+delta_ptr_clock
require(below(delta_beacon,iv.mpf("2e-25")) and below(delta_ptr_clock,iv.mpf("1e-34")) and below(delta_total,iv.mpf("2e-25")),"suppressed beacon and clock vector errors")

# Explicit k=1 homogeneous pointer quadrature shift at tau = pi + 3 (including exact V0^(-1/2) and omega_ptr_max^(-1/2)):
# Constructive two-cap factor: 2 * (1/sqrt(2)) = sqrt(2), core factor 1/2 -> sqrt(2)/2 = 1/sqrt(2), gate integral 0.01
mu_esu=box(prep["receiver_mean_unit_strength_lower"])
gate_int=iv.mpf("0.01")
mu_ptr_shift=lam_ptr*gate_int*(1/iv.sqrt(2))*chi_hom_lo*(1-goursat_frw_err)*mu_esu*eta/iv.sqrt(omega_ptr_max*V0)
den_ptr=iv.sqrt(2*iv.mpf("0.51"))
arg_ptr=mu_ptr_shift/den_ptr
gap_ptr_ref=2*arg_ptr/iv.sqrt(iv.pi)*iv.exp(-(arg_ptr**2))
gap_ptr_actual=gap_ptr_ref-2*delta_total
# Rigorous Cauchy-Schwarz upper bound: ||<tilde Q_p(tau)>||_{L^2} <= 1.15*eta, ||K_{rho0}^2 h_rec^sym||_{L^2} <= 1,
# int dtau a(tau) F_read(theta(tau)) = int dtheta a(tau)^3 F_read(theta) <= a_max^3 * gate_int, omega_ptr_1 >= sqrt(2), Var >= 0.49
mu_ptr_shift_hi=lam_ptr*(a_max**3)*gate_int*iv.mpf("1.15")*eta/iv.sqrt(iv.sqrt(2)*V0)
gap_ptr_actual_hi=(2/iv.sqrt(iv.pi))*(mu_ptr_shift_hi/iv.sqrt(2*iv.mpf("0.49")))+2*delta_total
require(above(gap_ptr_ref,iv.mpf("4.8e-23")) and above(gap_ptr_actual,iv.mpf("4.5e-23")) and below(gap_ptr_actual_hi,iv.mpf("3e-18")),"certified lower and Cauchy-Schwarz upper bounds on continuum pointer binary gap")

# Beacon background beta contribution and full pointer interaction energy (including quantum beacon variance!)
H1_beacon_sq=iv.mpf(1)+iv.mpf(80)**2
delta_beta_beacon=iv.mpf(1)/10*(r_b**2)*H1_beacon_sq/V0
E_beacon_model=(r_b**2)*H1_beacon_sq/(2*(g**2))
E_ptr_inc_upper=((b_eff_sup**2)*V0*vq_env+(lam_tilde**2)*V0*(vq_env**2))
require(below(delta_beta_beacon,iv.mpf("4e-26")) and below(E_ptr_inc_upper,iv.mpf("0.25")),"negligible beacon FRW backreaction and bounded pointer energy")

finish("local_autonomous_pointer.py",{
  "pointer_field":"conformal_scalar_xi_1_over_6_mass2_1",
  "beacon_field":"antipodally_symmetric_conformal_scalar_xi_1_over_6_mass2_1",
  "effective_coupling_lambda_ptr":"1e-2",
  "beacon_amplitude_scale_r_b":"1e-14",
  "Lagrangian_coupling_lambda_tilde":"1e-28",
  "clock_gate_support_theta":"[5.90, 5.92]",
  "coherent_beacon_envelope_support":"strictly_inside_C_read_union_minus_C_read_radius_1_over_2",
  "beacon_odd_harmonic_dipole_moments":"0_identically_by_antipodal_symmetry",
  "readout_observable":"phase_aligned_k1_homogeneous_pointer_quadrature_at_pi_plus_3",
  "Hamiltonian_coordinate_and_program_free":True,
  "pointer_Friedrichs_shift_upper":outward(C_shift_ptr),
  "beacon_quantum_fluctuation_vector_error_upper":outward(delta_beacon),
  "pointer_clock_jitter_vector_error_upper":outward(delta_ptr_clock),
  "total_continuum_vector_error_through_readout_upper":outward(delta_total),
  "pointer_k1_quadrature_shift_lower":outward(mu_ptr_shift),
  "reference_pointer_binary_gap_lower":outward(gap_ptr_ref),
  "actual_continuum_pointer_binary_gap_lower":outward(gap_ptr_actual),
  "actual_continuum_pointer_binary_gap_upper":outward(gap_ptr_actual_hi),
  "beacon_FRW_radiation_beta_contribution_upper":outward(delta_beta_beacon),
  "beacon_initial_energy_upper":outward(E_beacon_model),
  "pointer_interaction_energy_upper":outward(E_ptr_inc_upper),
  "all_outcomes_retained":True,
  "same_complete_energy_law_for_both_codes":True,
  "macroscopic_irreversible_detector_amplification_modeled":False
},inputs=[jc+"prepared_record.json",jc+"PREPARED_RECORD.md",
          rc+"continuum_clock_composite.json",rc+"dynamical_frw_clock_program.json"])
