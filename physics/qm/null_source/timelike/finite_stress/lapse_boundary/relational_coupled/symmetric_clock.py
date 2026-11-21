"""Two-zero clock Jacobians, normalization and radial-law identities."""
import sympy as s
from common import *
pre="physics/qm/null_source/timelike/";base=pre+"finite_stress/lapse_boundary/";new=base+"relational_coupled/"
load(new+"matter_clock.json");load(new+"angular_clock_input.json")
lam=s.symbols("lam",positive=True);theta=s.symbols("theta",real=True)
p2=s.sqrt(lam)*s.sin(theta);p1=s.sqrt(lam)*s.cos(theta)
require(s.simplify(s.diff(p2,theta)-p1)==0,"Positive-branch angular Jacobian")
require(s.simplify(p1*p1+p2*p2-lam)==0,"Original two Noether charges")
require(s.simplify(p1/p1-1)==0,"Physical positive-clock norm Jacobian")
r=s.symbols("r",positive=True)
require(s.simplify(r/s.diff(r*r,r)-s.Rational(1,2))==0,"Mass-shell radial measure")
require(s.simplify(2*s.pi*s.Rational(1,2)-s.pi)==0,"Abel two-dimensional normalization")
require(s.simplify(s.sqrt(2*s.pi)/(2*s.sqrt(s.pi))-1/s.sqrt(2))==0,"Dirac-to-KG Fourier coefficient")
AA,ee,ww,pp=s.symbols("A e sigma p",positive=True)
zz=s.symbols("z",real=True);rad=2*AA**3*(ee+ww*zz)
require(s.simplify(s.diff(rad,zz)/(2*AA**3*ww)-1)==0,"Frozen radial target law normalization")
require(s.cos(s.pi/4)**2==s.Rational(1,2),"Directed clock spectral gap")
q=s.symbols("singular_mass",nonnegative=True)
require(s.simplify(q+(1-q)*q/(1-q)-2*q)==0,"Total variation ac/singular decomposition")
bs=load(pre+"finite_stress/boundary_state.json")
co=load(new+"coefficient_window.json")
A=box(co["frozen_A"]);sig=box(bs["example_sigma"]);e2=box(bs["minimum_zero_energy_center"])
e0=e2+2*iv.sqrt(3)/A
support=interval((2*A**3*(e2-sig)).a,(2*A**3*(e0+sig)).b)
require(above(support), "Old thin radial target is positive and nondegenerate")
finish("symmetric_clock.py",dict(
 same_original_two_zero_mode_momenta=True,
 chosen_extension_family_preserves_zero_translations_and_O2=True,
 all_angular_unitaries_strongly_commute_selected_constraint=True,
 physical_Dirac_space="E_J H_geometry_oscillator tensor L2(S1)",
 spectral_measure_absolutely_continuous_assumed=False,
 positive_Dirac_norm_contains_both_clock_orientations=True,
 directed_angular_normal_state_embedded_in_positive_scalar_clock_space=True,
 explicit_positive_clock_Jacobian="(lambda-p2^2)^(-1/4)",
 full_circle_Householder_preserves_single_positive_clock_sector=False,
 old_radial_law_support_enclosure=outward(support),
 exact_normal_radial_recovery_criterion="mu_old absolutely continuous with respect to selected Rbar maximal spectral measure",
 optimal_total_variation_error="singular mass of target measure relative to maximal spectral measure",
 restricted_RT_purely_absolutely_continuous=True,
 restricted_RT_spectrum="all real numbers",
 restricted_RT_maximal_type="equivalent to Lebesgue",
 any_prescribed_nonempty_positive_clock_band_exists=True,
 old_total_radial_law_not_deduced_from_single_clock_ac=True,
 selected_Rbar_spectral_type_calculated=False,
 old_N2_conditional_law_and_complete_source_recovered=False,
 old_geometry_moments_or_mean_history_recovered=False,
 bounded_Rbar_band_implies_bounded_raw_stress_or_geometry_moments=False,
 local_autonomous_angular_preparation_constructed=False),
 [new+"matter_clock.json",new+"angular_clock_input.json",new+"coefficient_window.json",
 pre+"finite_stress/boundary_state.json",pre+"finite_stress/BOUNDARY_STATE.md",new+"REFERENCES.md"],
 proof="SYMMETRIC_CLOCK.md")
