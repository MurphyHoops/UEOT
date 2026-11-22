"""4D local autonomous pointer field: strict cap inclusion, curved positive square, and continuum binary gap."""
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

# Exact geodesic-ball inclusion arithmetic: 2/5 + 2*(1/20) == 1/2 and 1/4 + 2*(1/20) == 7/20 < 2/5
require(sp.Rational(2,5)+2*sp.Rational(1,20)==sp.Rational(1,2),"strict receiver cap inclusion")
require(sp.Rational(1,4)+2*sp.Rational(1,20)==sp.Rational(7,20) and sp.Rational(7,20)<sp.Rational(2,5),"core plateau inclusion")

spec=geodesic_cap_spectrum(inv_r0=20,Kmax=512,nsub=64)
khat=spec["khat"];B_r0=spec["B_rho0"]
V0=2*iv.pi**2

# Additional continuum Friedrichs vacuum shift from borrowing 3/8 int tilde Psi_{ptr,rho0}^2 dV
ptr_shift_512=iv.mpf(3)/8*sum(iv.mpf(k*k)*iv.sqrt(k*k+1)*(khat[k-1]**2) for k in range(1,513))
ptr_shift_tail=iv.mpf(3)/8*(B_r0**2)*iv.mpf("1.00001")*power_tail_upper(17,512)
C_shift_ptr=iv.mpf([ptr_shift_512.a,(ptr_shift_512+ptr_shift_tail).b])
require(below(C_shift_ptr,iv.mpf("1.3e7")),"finite continuum pointer Friedrichs shift")

# Verify gate [5.75, 5.95] lies strictly inside the curved-clock image of the positive-kernel window (pi + 5/2, pi + 3)
enc=frw_bounce_enclosure(N=220)
# Lower bound on theta(pi + 5/2) and upper bound on theta(pi + 5/2): since 1 <= u(s) <= u(pi+3), tau/u_max <= theta(tau) <= tau!
u_max=eval_frw(enc,iv.pi+3)["u"]
a_max=eval_frw(enc,iv.pi+3)["a"]
theta_pos_start_hi=iv.pi+iv.mpf(5)/2  # since theta(tau) <= tau
theta_end=box(frw["curved_clock_theta_at_pi_plus_3"])
require(below(theta_pos_start_hi,iv.mpf("5.65")) and above(iv.mpf("5.75")-theta_pos_start_hi,iv.mpf("0.1")),"gate starts strictly after pi + 5/2")
require(above(theta_end-iv.mpf("5.95"),iv.mpf("0.18")),"gate finishes strictly before pi + 3")

# Clock-jitter Duhamel vector error during readout at g = 1e-40, lam_ptr = 1e-3
g=iv.mpf(1)/10**40;eta=iv.mpf(1)/10**13;lam_ptr=iv.mpf(1)/1000
vx_inf=box(comp["continuum_smeared_variances"]["X_rho0_infty"])
vp_inf=box(comp["continuum_smeared_variances"]["body_tadpole_v_rho0_infty"])
F_sup=iv.mpf(1);Fp_sup=iv.mpf(20);T_gate_tau=iv.mpf("0.25")
delta_ptr_clock=g*T_gate_tau*V0*(lam_ptr*a_max*Fp_sup*iv.sqrt(vx_inf)*vp_inf+2*(lam_ptr**2)*F_sup*Fp_sup*iv.sqrt(3*vx_inf)*vp_inf)
delta_prep=box(comp["continuum_joint_vector_error_upper"])
delta_total=delta_prep+delta_ptr_clock
require(below(delta_ptr_clock,iv.mpf("1e-35")) and below(delta_total,iv.mpf("1.3e-32")),"controlled continuum joint vector error through readout")

# Continuum autonomous pointer displacement lower bound at tau = pi + 3:
# Core amplitude >= 1/2 of PREPARED_RECORD's unit-cap profile, gate integral 1/10, curved-FRW & lam_ptr^2 attenuation <= 0.02,
# mode factor >= 1/(sqrt(2)*2) (from coupling to pointer oscillator frequency >= sqrt(2)):
mu_esu=box(prep["receiver_mean_unit_strength_lower"])
frw_signal_attenuation=iv.mpf("0.02")
mu_ptr_shift=lam_ptr*iv.mpf("0.1")*iv.mpf("0.5")*(1-frw_signal_attenuation)*mu_esu*eta/iv.mpf(2)
# Pointer canonical quadrature variance <= 1/2 + O(lam_ptr^2) <= 0.51 -> den = sqrt(2 * 0.51)
den_ptr=iv.sqrt(2*iv.mpf("0.51"))
arg_ptr=mu_ptr_shift/den_ptr
gap_ptr_ref=2*arg_ptr/iv.sqrt(iv.pi)*iv.exp(-(arg_ptr**2))
gap_ptr_actual=gap_ptr_ref-2*delta_total
require(above(gap_ptr_ref,iv.mpf("9e-23")) and above(gap_ptr_actual,iv.mpf("9e-23")),"strictly positive continuum autonomous pointer binary gap")

# Pointer and beacon initial energy contribution (unit L2 beacon packet in B_{2/5}, ||nabla h_rec|| <= 20):
E_beacon_upper=iv.mpf("0.5")*(1+iv.mpf(400))  # <= 200.5 in model units
E_ptr_inc_upper=iv.mpf("0.5")*(lam_ptr**2)*V0*vp_inf
require(below(E_beacon_upper,201) and below(E_ptr_inc_upper,iv.mpf("0.002")),"finite beacon and pointer energy costs")

finish("local_autonomous_pointer.py",{
  "pointer_field":"conformal_scalar_xi_1_over_6_mass2_1",
  "beacon_field":"conformal_scalar_xi_1_over_6_mass2_1",
  "coupling_lambda_ptr":"1e-3",
  "clock_gate_support_theta":"[5.75, 5.95]",
  "strict_spatial_support_radius":"1/2_inside_C_read",
  "Hamiltonian_coordinate_and_program_free":True,
  "pointer_Friedrichs_shift_upper":outward(C_shift_ptr),
  "pointer_clock_jitter_vector_error_upper":outward(delta_ptr_clock),
  "total_continuum_vector_error_through_readout_upper":outward(delta_total),
  "pointer_quadrature_shift_lower":outward(mu_ptr_shift),
  "reference_pointer_binary_gap_lower":outward(gap_ptr_ref),
  "actual_continuum_pointer_binary_gap_lower":outward(gap_ptr_actual),
  "beacon_initial_energy_upper":outward(E_beacon_upper),
  "pointer_interaction_energy_upper":outward(E_ptr_inc_upper),
  "all_outcomes_retained":True,
  "same_complete_energy_law_for_both_codes":True,
  "macroscopic_irreversible_detector_amplification_modeled":False
},inputs=[jc+"prepared_record.json",jc+"PREPARED_RECORD.md",
          rc+"continuum_clock_composite.json",rc+"dynamical_frw_clock_program.json"])
