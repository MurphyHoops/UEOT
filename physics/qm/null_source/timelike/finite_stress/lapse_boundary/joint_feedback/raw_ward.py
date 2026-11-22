"""Exact raw canonical commutators and Ward algebra, not a continuum test."""
import sympy as s
from common import *
x,a,w=s.symbols("x a omega", real=True, positive=True)
f=s.Function("f")(x)
T=lambda q:-s.diff(q,x,2)/(2*a*a)
V=lambda q:a*a*w*w*x*x*q/2
H=lambda q:T(q)+V(q)
P=lambda q:T(q)-V(q)/3
D=lambda q:-s.I*w*w*(x*s.diff(q,x)+q/2)
require(s.simplify(T(V(f))-V(T(f))+s.I*D(f))==0,"Canonical [T,V]")
require(s.simplify(s.I*(H(P(f))-P(H(f)))+s.Rational(4,3)*D(f))==0,"Pressure commutator")
Hp=a*s.diff(H(f),a)
require(s.simplify(Hp+2*T(f)-2*V(f))==0,"Explicit source derivative")
require(s.simplify(Hp-4*H(f)+3*(H(f)+P(f)))==0,"Raw energy Ward")
require(s.simplify(a*s.diff(P(f),a)-4*P(f)+6*T(f)-s.Rational(2,3)*V(f))==0,"Pressure explicit derivative")
require(s.simplify(D(f).subs(w,0))==0,"Zero-mode dilation contribution")
finish("raw_ward.py",dict(
 exact_single_mode_differential_operator_identities=5,
 direct_sum_includes_both_species_and_zero_modes=True,
 source_ward_in_log_scale="d<rho_s>/du=-3<rho_s+p_s>",
 pressure_feedback="-4 Tr(tau D_Omega)/(3 V0 a^4)",
 source_state_equation="sigma'=-i[Hs,tau]",
 inverse_expansion_replaced_by_mean=False,
 proof_domain="finite K common comparison class; actual compact-kappa Schwartz-source preparations",
 arbitrary_finite_energy_trace_C1_claimed=False,
 pressure_witness_uses_initial_core_identity=True,
 raw_finite_K_result_is_full_renormalized_joint_solution=False),
 ["physics/qm/null_source/timelike/finite_stress/lapse_boundary/relational_coupled/ALL_SIGN_EVOLUTION.md",
  "physics/qm/null_source/timelike/finite_stress/lapse_boundary/relational_coupled/RAW_SOURCE_BOUNDARY.md",
  "physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_feedback/WEIGHTED_EVOLUTION.md"])
