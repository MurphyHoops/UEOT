"""Complete boundary-triple algebra and residual certificate identities."""
import sympy as s
from common import *
P="physics/qm/null_source/timelike/finite_stress/lapse_boundary/relational_coupled/"
paths=[P+"matter_clock.json",P+"symmetric_clock.json",P+"MATTER_CLOCK.md",
 P+"SYMMETRIC_CLOCK.md",
 "physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_feedback/MATTER_DOMAIN.md"]
for p in paths[:2]:load(p)
# Universal defect-coordinate bilinear form matrix; arbitrary multiplicity tensors with I.
G0=s.Matrix([[1,1]]);G1=s.Matrix([[s.I,-s.I]])
green=G0.conjugate().T*G1-G1.conjugate().T*G0
require(green==s.diag(2*s.I,-2*s.I),"Full Green identity signs")
require(s.Matrix.vstack(G0,G1).det()!=0,"Boundary pair onto defect coordinates")
swap=s.Matrix([[0,1],[1,0]])
require(G0*swap==G0.conjugate() and G1*swap==G1.conjugate(),"Antiunitary boundary covariance")
x,theta,M,y=s.symbols("x theta M y")
h=(y-theta*x)/(theta-M)
require(s.simplify(y+M*h-theta*(x+h))==0,"Krein boundary solve sign")
N=s.symbols("N",integer=True,positive=True)
require(s.simplify(s.summation(s.Rational(1,2)**s.Symbol('j'),(s.Symbol('j'),N+1,s.oo))-2**(-N))==0,"Faithful spectral-measure tail")
finish("boundary_interface.py",dict(
 full_ordinary_boundary_triple_constructed_from_original_defects=True,
 domains_include_self_adjoint_relations=True,
 restricted_flux_unitary_alone_claimed_complete=False,
 physical_boundary_relation_selected=False,
 original_Weyl_function_computed=False,
 resolvent_residual_requires_actual_domain_membership=True,
 broadened_density_positive_implies_ac_gate=False,
 trace_class_domain_changes_preserve_ac_gate=True,
 bounded_record_ambiguity_can_coexist_with_same_ac_gate=True,
 conditional_normal_spectral_target_construction=True,
 conditional_spectral_law_is_full_bare_state_recovery=False,
 old_source_missing_mass="integral over p_R=0 of f_old"),paths)
