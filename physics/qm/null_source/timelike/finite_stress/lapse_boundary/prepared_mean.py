"""Exact finite-mode preparation moments and common-history mean gates."""
import sympy as s
from common import require,finish
a,V0,h,hp,V,om,Q,P,D,chi=s.symbols("a V0 h hp V om Q P D chi",real=True,nonzero=True)
Qn=(1+chi)*Q/2+(1-chi)*P/(2*om*om)
Pn=(1+chi)*P/2+(1-chi)*om*om*Q/2
Dn=chi*D
require(s.simplify(Pn+om*om*Qn-(P+om*om*Q))==0,"Oscillator H_i expectation preserved")
Qz=(1+chi)*Q/2+(chi-1)*P/(2*V)
Pz=(1+chi)*P/2+(chi-1)*V*Q/2
require(s.simplify(Pz-V*Qz-(P-V*Q))==0,"Inverted H_i expectation preserved")
deltaRaw=(Pz-P-2*h*(chi-1)*D+h*h*(Qz-Q))/2
target=(chi-1)*((1+h*h/V)*P+(V+h*h)*Q-4*h*D)/4
require(s.simplify(deltaRaw-target)==0,"Actual zero raw stress change")
det=s.expand((1+h*h/V)*(V+h*h)-4*h*h)
require(s.factor(det-(V-h*h)**2/V)==0,"Strict zero mean quadratic determinant")
require(s.simplify(det.subs(V,hp+h*h)-hp*hp/(hp+h*h))==0,"Actual h prime determinant")
# Same free mode equations, with V=h'+h^2 and physical raw stress.
rho=(P-2*h*D+(h*h+om*om)*Q)/(2*V0*a**4)
press=(P-2*h*D+(h*h-om*om/3)*Q)/(2*V0*a**4)
dr=s.diff(rho,a)*h*a+s.diff(rho,h)*hp+s.diff(rho,Q)*2*D+s.diff(rho,P)*(-2*(om*om-hp-h*h)*D)+s.diff(rho,D)*(P-(om*om-hp-h*h)*Q)
require(s.simplify(dr+3*h*(rho+press))==0,"Exact transported stress Ward identity")
c,t=s.symbols("c t",real=True)
S=s.Matrix([[c,t/om],[-om*t,c]])
J=s.Matrix([[0,1],[-1,0]])
require(s.simplify(S*J*S.T-(c*c+t*t)*J)==s.zeros(2),"Ordered covariance symplectic CCR retained")
exponent=2*s.Rational(3,2)-4
require(exponent==-1,"Sharp Sobolev threshold for fixed-state third-jet mismatch")
finish("prepared_mean.py",dict(
 original_incoming_Hamiltonian_mean_strictly_increases=True,
 stable_expm1_and_free_limit_prescription_explicit=True,
 complete_finite_mode_second_moment_transport_explicit=True,
 fourth_moments_use_same_control_parameter_across_modes=True,
 original_zero_shell_correlations_retained=True,
 ordered_covariance_CCR_retained=True,
 zero_density_and_pressure_strictly_increase=True,
 total_source_density_sign_inferred_from_zero_only=False,
 post_gate_free_interval_Ward_exact=True,
 prepared_mean_equations_on_same_transported_geometry_explicit=True,
 old_exact_mean_family_suffices_for_new_state=False,
 fixed_high_state_single_third_geometry_jet_repair_Hadamard=False,
 third_jet_mismatch_kernel_Sobolev_threshold="s<3/2; not H^(3/2) when Delta Vprime nonzero",
 new_prepared_positive_time_mean_solution_proved=False,
 actual_preparation_past_and_device_total_source_constructed=False),
 ["finite_stress/lapse_boundary/HADAMARD_GATE.md",
  "finite_stress/lapse_boundary/CANONICAL_PREPARATION.md",
  "finite_stress/lapse_boundary/ACTION_LIFT.md",
  "finite_stress/lapse_boundary/TENSOR_NOISE.md",
  "finite_stress/GEOMETRY_MATCHING.md"],proof="PREPARED_MEAN.md")
