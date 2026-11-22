"""SI/Planck calibration dictionary, sample-complexity lower bound, and explicit open-gate inventory."""
from common import iv,box,load,require,above,below,outward,finish

rc="physics/qm/null_source/timelike/finite_stress/lapse_boundary/renormalized_continuum/"
ptr=load(rc+"local_autonomous_pointer.json")
crunch=load(rc+"crunch_vs_subcritical_gravity.json")

# CODATA-2022 reference constants (with conservative interval enclosure on G_SI)
c_si=iv.mpf("299792458")
hbar_si=iv.mpf("1.054571817e-34")
G_si=iv.mpf(["6.67428e-11","6.67432e-11"])

l_pl=iv.sqrt(hbar_si*G_si/(c_si**3))
require(above(l_pl,iv.mpf("1.6162e-35")) and below(l_pl,iv.mpf("1.6163e-35")),"Planck length in meters")

g=iv.mpf("1e-40")
alpha_G=iv.mpf(1)/10  # 4*pi*G_model / (3*g^2) = 1/10 => G_model = 3*g^2 / (40*pi)
G_model=(3*(g**2))/(40*iv.pi)
R_s3=l_pl/iv.sqrt(G_model)
L_sensor=R_s3/20
T_window_si=((iv.pi+4)*R_s3)/c_si

require(above(R_s3,iv.mpf("1.046e6")) and below(R_s3,iv.mpf("1.047e6")),"physical turnaround radius ~1046 km")
require(above(L_sensor,iv.mpf("5.23e4")) and below(L_sensor,iv.mpf("5.24e4")),"physical geodesic-cap sensor radius ~52.3 km")

rho_X_si=(hbar_si*c_si)/(2*(g**2)*(R_s3**4))
mass_density_si=rho_X_si/(c_si**2)
require(above(rho_X_si,iv.mpf("1.32e30")) and below(rho_X_si,iv.mpf("1.33e30")),"astrophysical closure energy density")

# Upper bound on autonomous pointer binary gap <= 2 * lam_ptr * eta < 2e-16 (actually ~1e-22) -> sample complexity floor
gap_lo=box(ptr["actual_continuum_pointer_binary_gap_lower"])
gap_conservative_hi=iv.mpf("1e-20")
require(above(gap_lo,iv.mpf("9e-23")) and below(gap_lo,gap_conservative_hi),"pointer binary gap scale")
N_trials_min=iv.log(10)/(2*(gap_conservative_hi**2))
require(above(N_trials_min,iv.mpf("1e40")),"prohibitive trial count for direct binary readout")

finish("calibration_and_open_gates.py",{
  "Planck_length_m":outward(l_pl),
  "dimensionless_G_model_at_g_1e_40":outward(G_model),
  "physical_turnaround_radius_R_S3_m":outward(R_s3),
  "physical_sensor_cap_radius_m":outward(L_sensor),
  "operating_window_physical_duration_s":outward(T_window_si),
  "turnaround_clock_energy_density_J_m3":outward(rho_X_si),
  "turnaround_clock_mass_density_kg_m3":outward(mass_density_si),
  "minimum_independent_trials_for_95pct_ID_lower":outward(N_trials_min),
  "tabletop_flat_space_accessibility":False,
  "remaining_open_gates":[
    "pointlike_rho0_to_zero_apparatus_renormalization",
    "higher_matter_harmonics_l_ge_2_of_quadratic_code_kick",
    "nonperturbative_operator_quantum_Einstein_equations",
    "derivation_of_field_content_and_couplings_from_Core_v3",
    "laboratory_gravimetric_calibration"
  ]
},inputs=[rc+"local_autonomous_pointer.json",rc+"LOCAL_AUTONOMOUS_POINTER.md",rc+"crunch_vs_subcritical_gravity.json"])
