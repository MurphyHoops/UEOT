"""Exact two-mean construction, marginals and true raw-source cost."""
import sympy as s
from common import *
base="physics/qm/null_source/timelike/finite_stress/lapse_boundary/";new=base+"relational_coupled/"
co=load(new+"coefficient_window.json");load(new+"mean_recovery.json");load(new+"geometric_momentum.json")
h,R,L,k,pp,q,Dk,AK,Q=s.symbols("h R L k p q Dk AK Q",real=True)
weight=h/(2*R-h)
require(s.simplify((1-weight)*h/2+weight*R-h)==0,"Exact geometry mean")
between=(1-weight)*(h/2-h)**2+weight*(R-h)**2
require(s.simplify(between-h*(R-h)/2)==0,"Exact between-packet variance")
require(s.expand((Dk+L*L/2)-(L*q+L*L/2)-(Dk-L*q))==0,"Endpoint phase cancels scalar Q shift")
a,I,Mq=s.symbols("a I Mq",positive=True)
Cg=a*I*Mq+(h*h*I-R)/2
# Exact marginal Q^2 expansion; odd source moments vanish by parity.
expanded=s.expand((Q+L*q+L*L/2)**2)
even=s.expand((expanded+expanded.subs(q,-q))/2)
require(s.simplify(even-(Q*Q+L*L*(q*q+Q)+L**4/4))==0,"Exact non-Gaussian source second moment change")
require(s.expand((pp+h*L)-k*(q+L)-(pp-k*q)-(h-k)*L)==0,"True raw momentum cost")
# Genuine operator-kappa constant-field shift leaves the original constraint.
Puk,Rest=s.symbols("Pu Rest",real=True)
require(s.expand(k*(Puk-L*(pp-k*q))+Rest+k*L*(pp-k*q)-(k*Puk+Rest))==0,"Genuine constant-field symmetry of constraint")
g=box(co["g_on_patch"]);rr=iv.mpf("1e12");hh=iv.exp(-19980);Mqmax=iv.mpf("2e19")
Cr_upper=Mqmax/(2*g*iv.mpf(".9")*rr)+(hh*hh/(iv.mpf(".9")*rr)-rr)/2
require(below(Cr_upper,-rr/4),"Actual strictly negative shift coefficient")
require(below(hh,rr/100),"Separated tiny and far packet scales")
require(above((1-hh/rr)**2,iv.mpf(".8")),"Actual proper kinetic source cost coefficient")
require(above(iv.mpf(".8")*rr/iv.mpf(100000),iv.mpf("7999999")),"Raw kinetic increase at least 8e6 Delta by strict A upper bound")
# q2 lower from w and |C_R|<=R/2.
require(s.simplify(1/(R*R*weight)-(2*R-h)/(R*R*h))==0,"Exact tail source resource denominator")
finish("shifted_state.py",dict(
 finite_K=65536,normal_rank_at_most=4,all_finite_parameter_vectors_common_core=True,
 same_fixed_h_source_AP_restriction_preserved=True,
 same_quantum_geometry_raw_source_energy_preserved=False,
 complete_bare_source_state_changed=True,
 mean_kappa_and_bulk_Pu_matched_exactly=True,
 initial_parameter="L^2=(E0+Pu_ref)/(w*abs(C_R)) from explicit finite integrals",
 huge_integrals_numerically_evaluated=False,
 geometry_relative_variance_lower="R/(4*h_i), R=1e12",
 source_Q2_sqrt_lower="Delta/sqrt(R*h_i)",
 true_zero_mode_raw_proper_kinetic_increase_lower="0.8*R*Delta/A > 8e6*Delta",
 original_pure_geometric_Pi_budget_recovered=False,
 genuine_constant_field_shift_preserves_full_constraint_and_Pi=True,
 same_mean_history_or_all_canonical_data_recovered=False,
 local_autonomous_preparation_constructed=False),
 [new+"coefficient_window.json",new+"mean_recovery.json",new+"source_budgets.json",
 new+"geometric_momentum.json",new+"PHYSICAL_SLICE.md",
 base+"ACTION_LIFT.md",base+"INCOMING_PREPARATION.md"],proof="SHIFTED_STATE.md")
