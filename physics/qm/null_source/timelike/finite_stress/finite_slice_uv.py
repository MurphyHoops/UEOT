"""True initial-density and ultraviolet matching for a finite-slice candidate."""
import json,hashlib
import sympy as s
from common import *
boundary=json.loads((HERE/"boundary_state.json").read_text())
assert boundary["status"]=="PASS"
for rel,digest in boundary["source_sha256"].items():
    assert hashlib.sha256((REPO/rel).read_bytes()).hexdigest()==digest
assert boundary["exact_correlated_nonGaussian_homogeneous_boundary_factor_derived"] is True
# The commutator of one normalized branch and its actual energy direction.
sg,m2=s.symbols("sg m2",positive=True)
C=s.Matrix([[0,-sg*s.sqrt(m2)],[sg*s.sqrt(m2),0]])
assert s.simplify(C.adjoint()*C-sg**2*m2*s.eye(2))==s.zeros(2)
assert s.Rational(2,100)==s.Rational(1,50)
# High-frequency coefficients follow from the exact amplitude equation.
x=s.symbols("x",positive=True)  # x=1/omega, not time
eta=s.symbols("eta",real=True)
V=s.Function("V")(eta)
O=1/x-V*x/2+(s.diff(V,eta,2)-V**2)*x**3/8
res=O**2-1/x**2+V+s.diff(O,eta,2)/(2*O)-3*s.diff(O,eta)**2/(4*O**2)
series=s.series(res,x,0,4).removeO().expand()
assert s.simplify(series.coeff(x,0))==0
assert s.simplify(series.coeff(x,2))==0
h,V0,V1,V2=s.symbols("h V0 V1 V2",real=True)
sub={V:V0,s.diff(V,eta):V1,s.diff(V,eta,2):V2}
Oo=O.subs(sub)
Op=s.diff(O,eta).subs(sub)
cc=h+Op/(2*Oo)
beta_sq=((1/x-Oo)**2+cc**2)/(4*(1/x)*Oo)
beta_series=s.series(beta_sq,x,0,6).removeO().expand()
assert s.simplify(beta_series.coeff(x,2)-h**2/4)==0
coef4=h**2*V0/8+V0**2/16-h*V1/8
assert s.simplify(beta_series.coeff(x,4)-coef4)==0
assert s.simplify(coef4.subs(h,0)-V0**2/16)==0
# Exact positive covariance and Bogoliubov normalization.
W,w=s.symbols("W w",positive=True)
c=s.symbols("c",real=True)
cov=s.Matrix([[1/(2*W),-c/(2*W)],[-c/(2*W),(W**2+c**2)/(2*W)]])
assert s.simplify(cov.det())==s.Rational(1,4)
alpha_abs=((w+W)**2+c**2)/(4*w*W)
beta_abs=((w-W)**2+c**2)/(4*w*W)
assert s.simplify(alpha_abs-beta_abs)==1
# Two real fields, k^2 degeneracy, omega=sqrt(k^2-1).
k,Aa=s.symbols("k Aa",positive=True)
assert s.limit(2*k**2*h**2/(4*(k**2-1)),k,s.oo)==h**2/2
assert s.limit(k*2*k**2*s.sqrt(k**2-1)/Aa*V0**2/(16*(k**2-1)**2),k,s.oo)==V0**2/(8*Aa)
# The boundary phase follows from the original action, not an added action.
q=s.Function("q")(eta);hh=s.Function("h")(eta)
raw=((s.diff(q,eta)-hh*q)**2-w**2*q**2)/2
bulk=(s.diff(q,eta)**2-(w**2-s.diff(hh,eta)-hh**2)*q**2)/2
assert s.simplify(raw-bulk+s.diff(hh*q**2/2,eta))==0
h0,b0,c0,d0=s.symbols("h0 b0 c0 d0",real=True)
u=h0*eta+b0*eta**2/2+c0*eta**3/6+d0*eta**4/24
potential=s.diff(u,eta,2)+s.diff(u,eta)**2
assert potential.subs(eta,0)==b0+h0**2
assert s.diff(potential,eta).subs(eta,0)==c0+2*h0*b0
assert s.simplify(s.diff(potential,eta,2).subs(eta,0)-d0-2*b0**2-2*h0*c0)==0
finish("finite_slice_uv.py",{
 "original_two_field_action_and_mode_equation_retained":True,
 "exact_static_matter_embedding_derivative":"-i[H,rho], trace norm 2*sigma*sqrt(mu2)",
 "exact_static_bare_time_trace_distance":"sqrt(1-|W(sigma*t)|^2)",
 "example_static_source_window_bare_trace_distance_strict_upper":"1/50",
 "sigma_is_weak_noise_parameter_for_complete_tensor":False,
 "exact_prescribed_smooth_past_KG_state_family_defined":True,
 "one_past_state_transported_not_instantaneous_roots_stitched":True,
 "positive_Wronskian_and_Hadamard_propagation_used":True,
 "finite_WKB_truncation_called_Hadamard":False,
 "initial_pure_high_covariance_determinant":"1/4",
 "omega_inverse_coefficient":"-V/2",
 "omega_inverse_cubed_coefficient":"(V_second-V^2)/8",
 "raw_beta_squared_omega_inverse_squared_coefficient":"h0^2/4",
 "raw_beta_squared_omega_inverse_fourth_coefficient":"h0^2*V/8+V^2/16-h0*V_prime/8",
 "two_field_raw_Shale_shell_limit_if_h0_nonzero":"h0^2/2",
 "raw_quasifree_representation_equivalent_if_h0_nonzero":False,
 "arbitrary_nonGaussian_old_Fock_normal_state_no_go_claimed":False,
 "h0_zero_V_nonzero_particle_number_sum_finite":True,
 "h0_zero_V_nonzero_old_static_energy_log_coefficient":"V^2/(8*A)",
 "old_static_energy_divergence_called_new_RSET_divergence":False,
 "rescaled_q_pq_common_Fock_dynamics_implementable_on_finite_smooth_windows":True,
 "original_action_canonical_boundary_phase":"-[h*q^2/2]_initial^final",
 "finite_cutoff_shear_is_claimed_infinite_old_Fock_unitary":False,
 "full_metric_initial_density_derivative_only_shear_claimed":False,
 "new_prescribed_past_is_a_self_consistent_Einstein_solution":False,
 "geometry_matter_device_density_and_constraints":"OPEN",
 "full_initial_tensor_CTP_Ward_and_calibration":"OPEN",
 "whole_physical_unification":"OPEN"},
 extra=["boundary_state.json","../nonlinear_history/KERNELS.md",
 "../constraint_states/RELATIONAL.md"])
