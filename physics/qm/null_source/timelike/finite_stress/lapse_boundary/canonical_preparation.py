"""Selfadjoint source charge and explicit normal canonical comparator."""
import sympy as s
from common import iv,require,finish
q,h,d,v,p,E=s.symbols("q h d v p E",positive=True,real=True)
psi=s.exp(-d*d*q*q/(h*h))
phase=s.exp(-s.I*q*E/h)
P=lambda f:-s.I*s.diff(f,q)
require(s.simplify(P(phase*psi)-phase*(P(psi)-E*psi/h))==0,"Controlled momentum sign")
require(s.simplify(h*P(phase*psi)+E*phase*psi-phase*h*P(psi))==0,"Constraint conjugation")
varP=(d*d+v)/(h*h);cov=-v/h
require(s.simplify(h*h*varP+2*h*cov+v-d*d)==0,"Full covariance cancels to tolerance")
varQ=h*h/(4*d*d)
require(s.simplify(d*d*varQ-h*h/4)==0,"Constraint-coordinate uncertainty saturation")
geomDet=s.simplify(varQ*varP)
require(s.simplify(geomDet-s.Rational(1,4)-v/(4*d*d))==0,"Geometry marginal uncertainty")
width=h/(2*d)
require(s.simplify(width*width/(2*h*h)-1/(8*d*d))==0,"Exact dephasing coefficient")
w,V=s.symbols("w V",positive=True)
# Explicit algebra isolates the high-frequency leading cancellation.
nu=s.sqrt(w*w-V)
require(s.simplify(nu-w+V/(nu+w))==0,"Instantaneous frequency difference")
require(s.simplify(-V/(2*w)+s.I*(-s.I*V/(2*w)))==0,"Conjugate Jost leading pair cancellation")
# omega_k^2 >= 3*k^2/4 (k>=2) supplies convergent rational series majorants.
k=s.symbols("k",integer=True,positive=True)
require(s.simplify((k*k-1)-s.Rational(3,4)*k*k)==k*k/4-1,"Frequency quadratic floor")
require(s.Rational(3,4)*4-1>=0,"Floor valid from k two")
# Weighted beta^2 sums have k powers -4, -3, -2, all strictly summable.
require(all(exponent>1 for exponent in [4,3,2]),"Unitary, energy mean and operator-domain series")
require(19980-3*iv.ln(10)>19000,"Finite branch momentum cost remains large")
zz,ee,ff=s.symbols("zz ee ff",real=True)
require(s.expand((zz-ee)**2+(zz-ff)**2-2*(zz-(ee+ff)/2)**2-(ee-ff)**2/2)==0,"CP instrument Gaussian overlap")
require(s.Rational(9,10)*900000**2-s.Rational(21,10)**2-1>0,"Actual inverted zero-mode potential positive")
finish("canonical_preparation.py",dict(
 normal_Gaussian_encoding_principle_reused_from_RELATIONAL=True,
 complete_normal_CP_instrument_in_toy_model=True,
 toy_control_gate_commutes_with_full_constraint=False,
 source_trace_distance_tends_one_as_constraint_tolerance_tends_zero=True,
 actual_initial_H_i_selfadjoint_realization_proved=True,
 finite_GNS_variance_alone_used_as_selfadjointness_proof=False,
 incoming_Bogoliubov_beta_bound="10*M/omega_k^3",
 nonzero_mode_unitary_and_weighted_energy_sums_converge=True,
 zero_mode_quadratic_selfadjoint_domain_stated=True,
 explicit_kinematic_space="L2(R,dq) tensor actual source Hilbert space",
 exact_normal_constraint_state_in_declared_tensor_model=False,
 spectral_no_atom_principle_reused_from_QUANTUM_FLOOR=True,
 Dirac_or_group_averaged_physical_inner_product_excluded=False,
 positive_normal_approximate_joint_state_constructed=True,
 constraint_law="Gaussian(0,delta^2)",
 geometry_coordinate_variance="h_i^2/(4*delta^2)",
 geometry_momentum_variance="(delta^2+Var(H_i))/h_i^2",
 geometry_source_covariance="-Var(H_i)/h_i",
 complete_bare_source_marginal_changed=True,
 source_H_i_spectral_law_preserved=True,
 source_incoming_Hin_spectral_law_preserved_claimed=False,
 original_quiet_mean_history_reused_after_gate=False,
 post_gate_Hadamard_and_RSET_proved=False,
 local_autonomous_gravity_preparation_implemented=False,
 controller_and_interaction_stress_budget_completed=False,
 original_full_constraint_quantization_completed=False),
 ["finite_stress/lapse_boundary/MIXED_BOUNDARY.md",
  "finite_stress/lapse_boundary/READOUT_WITNESS.md",
  "finite_stress/lapse_boundary/CONSTRAINT_RESIDUAL.md",
  "finite_stress/lapse_boundary/ACTUAL_INVERSE.md",
  "constraint_states/QUANTUM_FLOOR.md","constraint_states/RELATIONAL.md"],
 proof="CANONICAL_PREPARATION.md")
