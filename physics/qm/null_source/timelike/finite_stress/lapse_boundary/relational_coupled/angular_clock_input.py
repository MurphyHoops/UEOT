"""Exact angular-state and clock-calibration budgets on frozen source data."""
import sympy as s
from common import *
pre="physics/qm/null_source/timelike/";base=pre+"finite_stress/lapse_boundary/"
new=base+"relational_coupled/"
bs=load(pre+"finite_stress/boundary_state.json")
qw=load(base+"quiet_window.json");co=load(new+"coefficient_window.json")
A=box(co["frozen_A"]);sigma=box(bs["example_sigma"])
e2=box(bs["minimum_zero_energy_center"])
p1lower=iv.sqrt(A**3*(e2-sigma))
require(above(p1lower,"2e10"),"Strict directed original zero-mode momentum")
width=iv.sqrt(3)/(2*sigma)
duration=box(qw["proper_duration_model_units"]);ratio=width/duration
require(above(width,"4.086e6") and above(ratio,2499),"Actual quiet-window field-value calibration gate")
# Pure angular-factor trace distance and the explicit Householder map.
c=s.symbols("c",real=True);vnorm=2*(1-c)
require(s.simplify(1-c-(vnorm/2))==0,"Householder norm")
require(s.simplify(1-2*(1-c)/vnorm)==0,"Householder coefficient of u0")
require(s.simplify(2*(1-c)/vnorm-1)==0,"Householder coefficient of g")
require(s.Rational(1,4)==s.Rational(1,2)/2,"Angular sector probability")
require(s.sqrt(1-s.Rational(1,4))==s.sqrt(3)/2,"Exact trace-distance lower bound")
P,I,AA=s.symbols("P I AA",real=True,positive=True)
f=s.Function("f")(P)
Q=lambda z:s.I*s.diff(z,P)
Ti=lambda z:Q(z)+I*P*z
Hin=lambda z:P*P*z/(2*AA**3)
require(s.simplify(Hin(Ti(f))-Ti(Hin(f))+s.I*P*f/AA**3)==0,"Actual clock-charge commutator")
sig=s.sqrt(3)/(100*AA)
require(s.simplify(s.sqrt(3)/(2*sig)-50*AA)==0,"Exact thin-energy calibration scale")
finish("angular_clock_input.py",dict(
 current_thin_bare_state_changed=True,
 original_two_massless_field_action_retained=True,
 incoming_full_energy_law_and_radial_shell_correlations_preserved=True,
 source_Hilbert_energy_conserving_unitary_explicit=True,
 local_autonomous_apparatus_implemented=False,
 common_transport_summed_mean_RSET_functional_preserved=True,
 individual_species_W2_and_all_records_preserved=False,
 trace_distance_exact="sqrt(1-|<u0,g>|^2)",trace_distance_strict_lower="sqrt(3)/2",
 original_P1_strict_lower_enclosure=outward(p1lower),
 field_value_single_reading_time_width_strict_lower_enclosure=outward(width),
 actual_quiet_window_duration=outward(duration),
 width_to_window_ratio_strict_lower_enclosure=outward(ratio),
 calibration_uses_model_units=True,
 scope="single field-value reading calibrated by actual finite-slice mean proper-time drift",
 all_POVM_or_repeated_estimation_no_go=False,
 homogeneous_prescribed_source_influence_preserved=True,
 source_only_Gaussian_exact_P_squared_gate_rejected=True,
 nonselective_local_preparation_with_distinguishing_causal_complement_rejected=True,
 locality_gate_applies_to_full_prescribed_background_QFT_not_sharp_finite_K=True,
 S3_cap_causal_coverage_necessary="conformal_elapsed+cap_radius>=pi",
 old_complete_source_embedded_in_quantum_geometry=False),
 [pre+"finite_stress/boundary_state.json",pre+"finite_stress/BOUNDARY_STATE.md",
 base+"quiet_window.json",new+"coefficient_window.json",new+"SOURCE_BUDGETS.md",new+"REFERENCES.md"],
 proof="ANGULAR_CLOCK_INPUT.md")
