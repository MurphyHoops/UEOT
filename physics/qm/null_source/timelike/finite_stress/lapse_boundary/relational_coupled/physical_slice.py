"""Exact weighted-slice/gluing and momentum-transport identities."""
import sympy as s
from common import *
base="physics/qm/null_source/timelike/finite_stress/lapse_boundary/"
new=base+"relational_coupled/"
load(new+"snapshot_domain.json");load(new+"coupled_forms.json")
k=s.symbols("k",positive=True);f=k**(-s.Rational(1,2));R=1/f
p=s.Function("p")(k);P=lambda v:-s.I*s.diff(v,k)
require(s.simplify(f*k*f-1)==0,"Weighted raw gluing")
require(s.simplify(R*P(f*p)-P(p)-s.I*p/(2*k))==0,"Raw momentum to physical slice")
require(s.simplify(f*P(R*p)-P(p)+s.I*p/(2*k))==0,"Physical momentum raw pullback")
# Congruence on a clock-dependent test, keeping k independent of clock.
u=s.symbols("u",real=True);z=s.Function("z")(u)
require(s.simplify(R*(-s.I*s.diff(R*f*z,u)) - R*(-s.I*s.diff(z,u)))==0,"Constraint solution congruence")
# Both endpoint factors are needed; flat gluing leaves an extra k^{-1}.
require(s.simplify(f*f-1)!=0,"Flat-gluing negative control")
finish("physical_slice.py",dict(
 complete_finite_K_unitary_propagator_used=True,
 positive_clock_patch_physical_inner_product="integral kappa Psi1*Psi2",
 normal_physical_slice_states_constructed=True,
 exact_initial_source_bare_marginal_preserved_example=True,
 same_weight_raw_kernel_gluing=True,positive_local_rigging_form_constructed=True,
 global_kinematic_constraint_selfadjointness_or_group_averaging_equivalence=False,
 raw_first_order_halfline_momentum_selfadjoint=False,
 original_mean_history_recovered=False,
 full_field_physical_Hilbert_limit_proved=False),
 [new+"snapshot_domain.json",new+"coupled_forms.json",new+"REFERENCES.md",
 base+"CONTRACT_LAYERS.md",base+"INCOMING_PREPARATION.md",base+"ACTION_LIFT.md"],
 proof="PHYSICAL_SLICE.md")
