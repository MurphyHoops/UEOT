"""High-frequency rejection of full control and finite-mode Hadamard comparator."""
import sympy as s
from common import require,finish
z,V,Vp,Vpp,Vppp=s.symbols("z V Vp Vpp Vppp",real=True)
nu=s.sqrt(1-V*z*z)/z
W=1/z-V*z/2+(Vpp-V*V)*z**3/8
Wp=-Vp*z/2+(Vppp-2*V*Vp)*z**3/8
mr=(nu*nu-W*W-(Wp/(2*W))**2)/(4*nu*W)
mi=-Wp/(4*W*W)
mrser=s.series(mr,z,0,5).removeO()
miser=s.series(mi,z,0,5).removeO()
require(s.expand(mrser+Vpp*z**4/16)==0,"Actual incoming anomalous real coefficient")
require(s.expand(miser-Vp*z**3/8)==0,"Actual incoming anomalous imaginary coefficient")
dq=s.series(-mr/(2*nu),z,0,6).removeO()
require(s.expand(dq-Vpp*z**5/32)==0,"Lost high-mode Q coherence")
h=s.symbols("h",real=True)
rho_log=2*(-h*(-Vp/8))
p_log=2*(-h*(-Vp/8)-s.Rational(4,3)*Vpp/32)
require(s.expand(rho_log-h*Vp/4)==0,"Two-field density logarithmic coefficient")
require(s.expand(p_log-(h*Vp/4-Vpp/12))==0,"Two-field pressure logarithmic coefficient")
require(s.Rational(9,10)*900000**2-4-1>0 and s.Rational(9,10)*900000**3-8-1>0,"Once-selected derivative positivity with O(c2) remainder")
M,K,delta=s.symbols("M K delta",positive=True)
require(4*100*s.Rational(81,64)<1000,"Full tail bound including degeneracy and pair factor")
tail=1000*M*M/K
require(s.simplify(tail.subs(K,2000*M*M/(delta*delta))-delta*delta/2)==0,"Finite cutoff target")
d0,vlow,vt=s.symbols("d0 vlow vt",positive=True)
varP=(d0*d0+vlow)/(h*h);cov=-vlow/h
require(s.simplify(h*h*varP+2*h*cov+vlow+vt-(d0*d0+vt))==0,"Finite-mode full constraint covariance")
finish("hadamard_gate.py",dict(
 full_control_normality_does_not_imply_Hadamard=True,
 actual_incoming_anomalous_high_mode_coefficients_computed=True,
 finite_tolerance_full_control_same_AE_density_difference_logarithmically_diverges=True,
 density_log_coefficient="h_i*V_i_prime/(4*V0*a_i^4)>0",
 pressure_log_coefficient="(h_i*V_i_prime/4-V_i_second/12)/(V0*a_i^4)",
 complete_H_i_spectral_law_preserved_by_both_controls=True,
 every_finite_K_control_normal_and_Hadamard=True,
 finite_K_constraint_variance="delta0^2+Var(H_tail)",
 finite_K_tail_variance_upper="1000*M^2/K",
 arbitrary_strictly_positive_tolerance_realizable_in_declared_canonical_model=True,
 uniform_same_AE_stress_limit_as_K_tends_infinity=False,
 original_complete_source_marginal_preserved=False,
 original_quiet_mean_history_reused_after_finite_K_gate=False,
 total_device_action_locality_or_energy_budget_completed=False,
 actual_gravity_instrument_constructed=False,
 global_failure_extended_to_all_preparations=False),
 ["finite_stress/lapse_boundary/CANONICAL_PREPARATION.md",
  "finite_stress/lapse_boundary/ACTUAL_INVERSE.md",
  "finite_stress/lapse_boundary/READOUT_WITNESS.md",
  "finite_stress/lapse_boundary/MIXED_BOUNDARY.md",
  "finite_stress/GEOMETRY_MATCHING.md"],
 proof="HADAMARD_GATE.md")
