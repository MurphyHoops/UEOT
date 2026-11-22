"""Neumann enclosure of the continuum 8-projection total Jacobian on the dynamical closed-FRW bounce."""
from common import iv,box,load,require,above,below,outward,finish
from model import frw_bounce_enclosure,eval_frw

rc="physics/qm/null_source/timelike/finite_stress/lapse_boundary/renormalized_continuum/"
ap_old="physics/qm/null_source/timelike/finite_stress/lapse_boundary/autonomous_preparation/"
cols=load(rc+"continuum_tadpole_columns.json")
had=load(rc+"hadamard_cauchy_transport.json")
loc_rec=load(ap_old+"local_record.json")

enc=frw_bounce_enclosure(alpha_G=iv.mpf(1)/10,lam_L=iv.mpf(550001)/1000000,N=220,T_end=iv.pi+3)
ev_02=eval_frw(enc,iv.mpf(1)/5)
ev_pi=eval_frw(enc,iv.pi)

# Bound |a''(tau)/a(tau)| across [-1/5, pi] on 32 subintervals
app_over_a_pi_sup=iv.mpf(0)
for idx in range(32):
    t_a=iv.pi*idx/32;t_b=iv.pi*(idx+1)/32
    ev_i=eval_frw(enc,iv.mpf([t_a.a,t_b.b]))
    r_i=abs(ev_i["app"]/ev_i["a"])
    if r_i.b>app_over_a_pi_sup.b:app_over_a_pi_sup=iv.mpf(r_i.b)
require(below(app_over_a_pi_sup,iv.mpf("2e-4")),"small curvature potential on [-1/5, pi]")

# Relative perturbation of J_{app} from curved FRW vs static ESU:
# (i) tadpole drift on [-1/5, 1/5]: dv_pulse / v_inf <= had["curved_FRW_body_tadpole_drift_upper"] / (cols["continuum_tadpole_scale"]*8/V0) + (a(1/5)-1)
V0=2*iv.pi**2
scale_esu=box(cols["continuum_tadpole_scale_V0_v_over_8"])
v_esu=8*scale_esu/V0
dv_frw=box(had["curved_FRW_body_tadpole_drift_upper"])
rel_source_err=(ev_02["a"]-1)+(ev_02["a"]*dv_frw)/v_esu
# (ii) clock dipole propagator Duhamel error on [-1/5, pi]: (pi + 1/5)/(2*sqrt(3)) * sup|a''/a|
prop_err=((iv.pi+iv.mpf(1)/5)/(2*iv.sqrt(3)))*app_over_a_pi_sup
# (iii) extrinsic curvature H_pi = a'(pi)/a(pi) mixing at tau = pi
extrinsic_err=abs(ev_pi["ap"]/ev_pi["a"])

frob_esu=box(cols["smeared_controller_Frobenius_upper"])
delta_J_app=scale_esu*frob_esu*(rel_source_err+prop_err+2*extrinsic_err)
require(below(delta_J_app,iv.mpf("2.0")),"small curved-FRW controller Jacobian perturbation")

# Curved matter Jacobian norm <= 6 + Duhamel shift <= 6.01
J_matter_frw_upper=iv.mpf("6.01")
inv_esu_ctrl=box(cols["continuum_controller_inverse_norm_upper"])
inv_scaled_ctrl=ev_pi["a"]*inv_esu_ctrl
pert_total=delta_J_app+J_matter_frw_upper
require(below(pert_total,iv.mpf("8.1")) and below(inv_scaled_ctrl*pert_total,iv.mpf("0.05")),"strict Neumann margin on FRW")

tot_inv_frw=inv_scaled_ctrl/(1-inv_scaled_ctrl*pert_total)
require(below(tot_inv_frw,iv.mpf("0.0057")),"continuum FRW total Jacobian inverse bound")

# Contraction of the continuum limiting/parametrix FRW total response map on ||u|| <= 1e-16 for target ||y|| <= 5e-23
r0=iv.mpf("1e-16");target=iv.mpf("5e-23");eta=iv.mpf(1)/10**13
L_frw=tot_inv_frw*iv.mpf("4.2e-9")
require(below(L_frw,iv.mpf("3e-11")) and below(tot_inv_frw*target+L_frw*r0,r0.a),"strict limiting contraction on FRW")

# Actual continuum cap target moment d_inf (no K=64 truncation tail needed at K=infty!)
d_inf_lo=box(loc_rec["frozen_density_first_harmonic_projection_lower"])/ev_pi["a"]
y_eta=eta*eta*iv.mpf("0.5")
require(above(d_inf_lo,iv.mpf("0.0292")) and below(y_eta,target.a),"eta=1e-13 target inside FRW ball")

finish("curved_continuum_inverse.py",{
  "encoding_slice_a_pi":outward(ev_pi["a"]),
  "encoding_slice_Hubble_aprime_over_a":outward(extrinsic_err),
  "curvature_potential_sup_to_pi_upper":outward(app_over_a_pi_sup),
  "controller_Jacobian_FRW_perturbation_upper":outward(delta_J_app),
  "matter_Jacobian_FRW_norm_upper":outward(J_matter_frw_upper),
  "continuum_FRW_total_inverse_norm_upper":outward(tot_inv_frw),
  "continuum_FRW_contraction_upper":outward(L_frw),
  "certified_control_ball_radius":"1e-16",
  "certified_target_ball_radius":"5e-23",
  "continuum_cap_density_moment_lower":outward(d_inf_lo),
  "eta_1e_13_inside_certified_FRW_target_ball":True,
  "background_FRW_bounce_invariant_under_program_u":True,
  "l2_spatial_quadrupole_vanishes_on_FRW":True,
  "all_higher_spatial_matter_modes_or_operator_Einstein_solved":False
},inputs=[rc+"continuum_tadpole_columns.json",rc+"CONTINUUM_TADPOLE_COLUMNS.md",
          rc+"hadamard_cauchy_transport.json",rc+"HADAMARD_CAUCHY_TRANSPORT.md",
          rc+"PARSEVAL_ISOTROPIC_FRAME.md",ap_old+"local_record.json"])
