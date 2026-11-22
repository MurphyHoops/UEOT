"""AR: exact radial and energy algebra, outward cap/readout bounds."""
from common import finish,require,iv,exact,outward,above,below,load,box
import sympy as s
r=exact(1)/5;eps=exact(1)/2;centers=exact(3)/2;T=iv.mpf(3)
Vcap=2*iv.pi*(eps-iv.sin(2*eps)/2)
Vhalf=2*iv.pi*(eps/2-iv.sin(eps)/2)
l1=iv.exp(-exact(1)/3)*Vhalf/iv.sqrt(Vcap)
mu=r*l1*l1/(8*iv.pi)
xlo=mu*iv.sqrt(exact(200)/229)
gap=2*xlo/iv.sqrt(iv.pi)*iv.exp(-xlo*xlo)
require(above(centers-2*eps) and below(centers+2*eps,T) and below(T,iv.pi),"Cap causal window")
require(above(mu,".000034") and above(gap,".000036"),"Local causal record contrast")
u=(3+iv.sqrt(3))/2
grad=2/eps*u**(exact(3)/2)*iv.sqrt(u-1)*iv.exp(1-u)
require(below(grad,exact(22)/5),"Bump gradient bound")
Pstar=exact(11)/20*iv.sqrt(1+(exact(22)/5)**2)
p="physics/qm/null_source/timelike/finite_stress/lapse_boundary/autonomous_preparation/"
aq=load(p+"external_ramp.json");ap=load(p+"stationary_comparator.json")
VE=box(aq["excitation_energy_variance_upper"])
EE=box(aq["excitation_energy_upper"])
er=box(ap["vacuum_energy_same_ESU_convention"])
Vout=VE+26*Pstar+25+exact(625)/2
Mout=er+EE+13
require(below(Vout,403),"Full retained-system variance budget")
dipole=iv.cos(eps)*iv.exp(-exact(2)/3)*Vhalf/(2*Vcap)
require(above(dipole,".029"),"Frozen-source first-harmonic obstruction")

Kcert=64;k0=exact(Kcert+1)
mu_tail=(exact(22)/5)**2/(k0*k0-1)*(exact(3)/(8*k0*k0)+iv.sqrt(5)/(16*k0**3))
require(below(mu_tail,".00000041"),"Actual signal cutoff tail")
muKlo=mu-mu_tail
xK=muKlo*iv.sqrt(exact(200)/229)
gapKlo=2*xK/iv.sqrt(iv.pi)*iv.exp(-xK*xK)
require(above(gapKlo,".000035"),"Positive complete K64 record")
z=s.symbols("z",positive=True)
uf=s.Function("u")(z);ph=uf/s.sin(z)
radial=s.sin(z)*(-s.diff(ph,z,2)-2*s.cot(z)*s.diff(ph,z)+ph)+s.diff(uf,z,2)
require(s.trigsimp(s.expand_trig(radial))==0,"S3 radial +1 shift")
Y=s.cos(z)
require(s.trigsimp(s.diff(Y,z,2)+2*s.cot(z)*s.diff(Y,z)+3*Y)==0,"First scalar harmonic")
require(s.diff(Y,z,2)+Y==0 and s.trigsimp(s.cot(z)*s.diff(Y,z)+Y)==0,"First-harmonic radial and angular Hessian")
# Homogeneous quadratic energy under local canonical momentum translations.
p0,xi,G2,H=s.symbols("p0 xi G2 H",real=True)
delta=xi*p0+xi**2*G2/2
require(s.diff(delta,xi).subs(xi,0)==p0 and s.diff(delta,xi,2)==G2,"Canonical kick coefficients")

# Noncommuting tensor operators: the Gaussian kick covariance identity.
AF,AG,BF,BG=s.symbols("AF AG BF BG",commutative=False)
CF,CG,v=s.symbols("CF CG v",real=True)
TF=AF+xi*BF+xi**2*CF;TG=AG+xi*BG+xi**2*CG
sym=s.expand((TF*TG+TG*TF)/2)
avg=s.expand(sym.coeff(xi,0)+v*sym.coeff(xi,2)+3*v**2*sym.coeff(xi,4))
deltaN=s.expand(avg-(AF*AG+AG*AF)/2-v*CF*AG-v*CG*AF-v**2*CF*CG)
require(s.expand(deltaN-v*(BF*BG+BG*BF)/2-2*v**2*CF*CG)==0,"Complete symmetric tensor covariance increment")
finish("local_record.py",{
"scope":"Actual AQ state, local two-field action, disjoint-cap encoding and local normal mathematical instrument",
"r":"1/5","ramp_model_time":100,"cap_radius":"1/2","center_distance":"3/2","read_model_time":3,
"SI_time_calibration":False,
"cap_volume":outward(Vcap),"half_cap_volume":outward(Vhalf),
"cap_test_L2_squared_upper":1,"cap_test_integral_lower":outward(l1),
"receiver_mean_magnitude_lower":outward(mu),
"receiver_reference_variance_upper":"9/16",
"complete_binary_threshold_contrast_lower":outward(gap),
"explicit_signal_cutoff":64,
"explicit_signal_cutoff_error_upper":outward(mu_tail),
"explicit_cutoff_complete_binary_contrast_lower":outward(gapKlo),
"exact_continuum_no_signal_window":"0<t<1/2",
"strictly_positive_local_quantum_record_window":"5/2<T<pi",
"finite_spectral_cutoff_exact_causality_claimed":False,
"bump_gradient_maximum":outward(grad),
"momentum_smear_variance_upper":outward(Pstar),
"local_encoding_mean_energy_increase_upper":"1/2",
"retained_reader_stress_jump":{"rho":"25*g^2/2","p":"25*g^2/6","momentum_density":0},
"nonselective_full_retained_state_strictly_changes":True,
"terminal_source_species_marginal_unchanged_by_probe_reader":True,
"nonselective_reader_mean_energy_increase_upper":"25/2",
"postrecord_retained_energy_mean_upper_expression":outward(Mout),
"postrecord_retained_energy_variance_upper":outward(Vout),
"actual_all_outcome_Stinespring_limit":True,
"cutoff_graph_scope":"common diagonal graph and varying-H_K recovery only",
"conditional_nonselective_binary_states_Hadamard":True,
"conditional_nonselective_final_energy_moments_finite":True,
"instrument_local_algebra_and_spacelike_commutant_identity":True,
"raw_and_binary_records_complete":True,
"postreadout_full_tensor_noise_increment":"v Re <B_F B_G> + 2 v^2 C_F C_G, positive semidefinite",
"tensor_noise_domain":"real smooth compact spacetime tests supported after readout",
"sharp_divergent_stress_variances_subtracted":False,
"signal_kernel":"causal Cauchy propagator; not positive-frequency covariance",
"full_same_state_gravitational_constraints_satisfied":False,
"frozen_density_first_harmonic_projection_lower":outward(dipole),
"full_coupled_constraint_adjoint_kernel_determined":False,
"static_pointwise_Einstein_rejection":"code-reference density f^2/2 is nonconstant on homogeneous ESU",
"codes_total_energy_and_even_stress_laws_identical":True,
"source_sign_record_is_geometry_charge_record":False,
"physical_local_autonomous_pointer_constructed":False,
"external_actuator_and_pointer_own_stress_included":False,
"old_general_local_probe_theorems_claimed_new":False
},[p+"NEXT_GATE.md",p+"EXTERNAL_RAMP.md",p+"external_ramp.json",p+"STATIONARY_COMPARATOR.md",p+"stationary_comparator.json"],
proof="LOCAL_RECORD.md")
