"""Complete-energy concentration and the actual second-order incoming gate."""
import json,hashlib
import sympy as s
from common import *
frozen={}
for stem in ["history","selection"]:
    j=json.loads((TIMELIKE/"nonlinear_history"/(stem+".json")).read_text())
    assert j["status"]=="PASS"
    for rel,digest in j["source_sha256"].items():
        assert hashlib.sha256((REPO/rel).read_bytes()).hexdigest()==digest
    frozen[stem]=j
assert frozen["history"]["exact_nonlinear_mean_history_exists"] is True
assert frozen["selection"]["randomizing_growth_amplitudes_alone_carries_nonzero_sampled_source"] is False
ratio=box(frozen["selection"]["fast_to_slow_ratio"])
assert above(ratio,2)
boundary=json.loads((HERE/"boundary_state.json").read_text())
assert boundary["status"]=="PASS"
for rel,digest in boundary["source_sha256"].items():
    assert hashlib.sha256((REPO/rel).read_bytes()).hexdigest()==digest
assert boundary["normal_rank_two_correlated_source"] is True
assert above(NU0,16)
M=iv.sqrt(iv.pi*NU0)/(2*iv.sqrt(2))
assert above(M,2) and below(32/NU0,2)
kappaE=K2/(2*A**3)
sigma=iv.sqrt(3)/(100*A)
qbound=2*sigma*M/kappaE
assert above(qbound) and below(qbound,iv.mpf("0.00000021"))
# Exact full Gaussian-radial law moments, with no radial-tail truncation.
t,nu,R=s.symbols("t nu R",positive=True)
mgf=s.exp(R*t/(1-t/nu))/(1-t/nu)
mean=s.diff(mgf,t).subs(t,0)
raw2=s.diff(mgf,t,2).subs(t,0)
assert s.simplify(mean-R-1/nu)==0
assert s.simplify(raw2-mean**2-2*R/nu-1/nu**2)==0
rhi=1+s.sqrt(3)/2
L=(1+rhi)/2
mixmean=(mean.subs(R,1)+mean.subs(R,rhi))/2
mixvar=(raw2.subs(R,1)+raw2.subs(R,rhi))/2-mixmean**2
assert s.simplify(mixmean-L-1/nu)==0
assert s.simplify(mixvar-s.Rational(3,16)-2*L/nu-1/nu**2)==0
# The exact Ward identity is independently checked from conservation.
a,h,hp,rho,press,rhop=s.symbols("a h hp rho press rhop",real=True)
E=h**2+1-s.Rational(2,3)*a**2*rho
S=hp+(h**2+1)/2+a**2*press
dE=2*h*hp-s.Rational(2,3)*a**2*(2*h*rho+rhop)
assert s.simplify((dE+h*E-2*h*S).subs(rhop,-3*h*(rho+press)))==0
r,q,Pr,Pq=s.symbols("r q Pr Pq",positive=True)
kernel=(r*Pq+q*Pr)/(r+q)
assert s.simplify((r+q)*kernel-r*Pq-q*Pr)==0
assert s.simplify(kernel.subs({q:r,Pq:Pr})-Pr)==0
assert s.simplify(kernel.subs({Pr:r**2-4,Pq:q**2-4})-r*q+4)==0
assert kernel.subs({Pr:0,Pq:0})==0
finish("total_boundary_gate.py",{
 "original_fixed_background_endpoint_source_used":True,
 "new_gravity_clock_or_lattice_introduced":False,
 "strong_energy_conservation_preserves_complete_spectral_law":True,
 "finite_energy_moments_required_for_spectral_law_theorem":False,
 "independent_input_concentration_convolution_bound":True,
 "current_old_radial_density_uniform_upper":outward(M),
 "old_energy_density_uniform_upper":outward(M/kappaE),
 "example_total_energy_window_width":outward(2*sigma),
 "old_complete_total_probability_in_any_candidate_width_band_upper":outward(qbound),
 "distance_to_full_total_band_target_lower":outward(1-qbound),
 "bound_applies_to_new_source_marginal_distance":False,
 "numeric_concentration_bound_assumes_frozen_zero_high_product_and_independent_apparatus":True,
 "arbitrary_correlated_input_has_product_characteristic_function":False,
 "same_global_volume_used_for_localized_apparatus":True,
 "normal_additive_no_point_obstruction_reused_not_new_discovery":True,
 "arbitrary_correlated_normal_endpoint_joint_state_can_have_delta_energy_law":False,
 "physical_Hilbert_space_or_interacting_quantum_gravity_excluded":False,
 "unbounded_apparatus_energy_support_means_infinite_moments":False,
 "exact_mean_Ward_and_all_order_incoming_obstruction_reused":True,
 "incoming_second_order_energy_kernel":"(r*P(s)+s*P(r))/(r+s), r,s>0",
 "classical_comparison_second_order_kernel":"r*s-4",
 "incoming_on_shell_second_order_density_charge":0,
 "off_shell_second_order_energy_form_is_positive_semidefinite":False,
 "sqrt_source_regular_ansatz_automatically_repairs_same_incoming_constraint":False,
 "finite_slice_C2_or_full_boundary_CTP_constructed":False,
 "full_geometry_matter_device_baseline":"OPEN",
 "whole_physical_unification":"OPEN"},
 extra=["boundary_state.json","../joint_history/HISTORY.md",
 "../constraint_states/POSITIVE_CLOCK.md","../constraint_states/QUANTUM_FLOOR.md",
 "../constraint_states/RELATIONAL.md","../nonlinear_history/EXISTENCE.md",
 "../nonlinear_history/SELECTION.md","../nonlinear_history/history.json",
 "../nonlinear_history/selection.json"])
