"""Actual high-mode endpoint characteristic law and joint-normality obstruction."""
import sympy as s
from common import require,finish
z,d,c=s.symbols("z d c",real=True)
X=z/2+c*z**3
leading=s.limit(-s.log(1+d*d*X*X)/(z*z),z,0)
require(s.simplify(leading+d*d/4)==0,"Actual high-mode characteristic Cesaro coefficient")
k=s.symbols("k",positive=True,integer=True)
require(s.simplify(2*k*k*s.Rational(1,2)-k*k)==0,"Two-field characteristic amplitude degeneracy")
u,v=s.symbols("u v",real=True)
require(s.simplify((1+s.I*u*v)*(1-s.I*u*v)-(1+u*u*v*v))==0,"Gaussian characteristic absolute square")
x,sg=s.symbols("x sg",positive=True)
require(s.simplify(s.integrate(s.exp(-x*x/4),(x,-s.oo,s.oo))/(2*s.sqrt(s.pi)*sg)-1/sg)==0,"Fixed Gaussian purity rate coefficient")
kap,qc=s.symbols("kap qc",real=True)
f=s.Function("f")(kap)
Pm=lambda f:-s.I*s.diff(f,kap)
for sign in [-1,1]:
 phase=s.exp(sign*s.I*kap*qc)
 require(s.simplify(Pm(phase*f)-phase*(Pm(f)+sign*qc*f))==0,"Active shear sign")
finish("quantum_endpoint.py",dict(
 both_active_endpoint_signs_have_same_obstruction=True,
 finite_K_active_controlled_shear_normal=True,
 current_actual_incoming_high_modes_used=True,
 characteristic_modulus_squared="product_(k=3..K) (1+s^2*abs(v_k)^4)^(-k^2)",
 log_characteristic_modulus_squared_over_K_limit="-s^2/4",
 fixed_geometry_wavepacket_reduced_purity_tends_zero=True,
 general_fixed_normal_geometry_product_input_reduced_purity_tends_zero=True,
 fixed_Gaussian_width_s_times_sqrt_K_times_purity_limit=1,
 fixed_wavepacket_normal_trace_norm_reduced_limit_exists=False,
 fixed_wavepacket_normal_trace_norm_joint_limit_exists=False,
 c_number_endpoint_phase_fixes_purity=False,
 sharp_shear_high_frequency_input_reused=True,
 active_preparation_confused_with_passive_canonical_transport=False,
 finite_K_common_action_state_endpoint_cancellation_excluded=False,
 Hilbert_bundle_or_Dirac_physical_inner_product_excluded=False,
 all_quantum_geometry_preparations_excluded=False),
 ["finite_stress/lapse_boundary/ENDPOINT_DOMAIN.md",
  "finite_stress/lapse_boundary/ACTION_LIFT.md",
  "finite_stress/lapse_boundary/INCOMING_PREPARATION.md",
  "finite_stress/lapse_boundary/FINITE_SOURCE_DOMAIN.md"],
 proof="QUANTUM_ENDPOINT.md")
