"""Original-domain Cayley and Dirac-probability algebra; no spectral solver."""
import sympy as s
from common import *
P="physics/qm/null_source/timelike/finite_stress/lapse_boundary/relational_coupled/"
paths=[P+"matter_clock.json",P+"symmetric_clock.json",P+"angular_clock_input.json",
 P+"MATTER_CLOCK.md",P+"SYMMETRIC_CLOCK.md",P+"ANGULAR_CLOCK_INPUT.md"]
for p in paths[:3]:load(p)
r,lam,eps=s.symbols("r lambda epsilon",real=True);eps=s.symbols("epsilon",positive=True)
W=(r-lam-s.I*eps)/(r-lam+s.I*eps)
realW=s.simplify((W+s.conjugate(W))/2)
require(s.simplify((1-realW)/2-eps**2/((r-lam)**2+eps**2))==0,"Bounded Lorentzian effect is Cayley real part")
alpha=s.symbols("alpha",real=True)
require(s.simplify((1+alpha)**2/(2+2*alpha)-(1+alpha)/2)==0,"Same-state effect difference")
a,b,c,d=s.symbols("a b c d",positive=True)
require(s.simplify(a/(a+b)-c/(c+d)-(a*d-b*c)/((a+b)*(c+d)))==0,"Physical angular record from nonproportional rigging forms")
require(s.simplify((s.I*eps*2)/(2*s.I*eps))-1==0,"Resolvent-Cayley normalization")
finish("matter_domain.py",dict(
 original_constraint_not_replaced=True,
 J_compatible_boundary_completions_not_unique=True,
 common_core_all_finite_moments_can_agree=True,
 bounded_spectral_record_difference_lower="1/2-delta on a suitable common compact test",
 positive_bounded_band_has_two_nonzero_distinct_domain_projections=True,
 common_original_angular_Dirac_record_probabilities_differ=True,
 different_domains_are_same_completed_physics=False,
 actual_old_radial_ac_gate_computed=False,
 core_formal_nonimplication_theorem_claimed=False,
 scientific_check_scope="finite Cayley/probability algebra; operator-domain proof in text"),paths)
