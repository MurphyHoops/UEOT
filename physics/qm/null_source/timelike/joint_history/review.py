"""Separate rational margin checks and result/scope audit, no predecessor execution."""
from fractions import Fraction as Q
import json
from common import HERE,finish
# Independent coarse proof uses rational envelopes, not the root iteration.
xmin,xmax=Q(6678924990),Q(6678931320)
umax=1+Q(1,10**10)
kmax=Q(7,1000)
pi2lo,pi2hi=Q(986,100),Q(987,100)
lo,hi=Q(4,1000),Q(45,10000)
alo=6-kmax/xmin;ahi=12*umax-6;bhi=12*umax-3
phi_lo_upper=ahi*lo+4*umax*lo**3/xmin**2
phi_hi_lower=alo*hi-bhi*hi**2/xmin
assert phi_lo_upper<Q(96,100)/(4*pi2hi)
assert phi_hi_lower>Q(104,100)/(4*pi2lo)
assert alo-2*bhi*hi/xmin>Q(5999,1000)
# log(1-z)>=-z/(1-z), 0<z<1, supplies a rational thermal lower bound.
thermal_lo=3*lo-3*umax*hi**2/xmin-hi/(xmin-hi)/(32*pi2lo)
thermal_hi=(6*umax-3)*hi
assert thermal_lo/Q(7021,10000)>Q(17,1000)
assert thermal_hi/Q(7019,10000)<Q(2,100)
# Two radial gaps >2/25 using only 43/50<d<7/8.
dlo,dhi,gap=Q(43,50),Q(7,8),Q(2,25)
assert dlo/4>(1+gap)**2-1
left=dlo/4-gap**2
assert left>0 and left**2>4*gap**2*(1+3*dhi/4)
# Density cap => conditional variance bound: exact integral for normalized M=1.
assert Q(1,4)-Q(4,3)*Q(1,8)==Q(1,12)
# L^2=19/16+sqrt(3)/2 < 33/16; a wholly rational >10% proof.
assert 3<Q(7,4)**2
assert 48*Q(33,16)<100
names=["algebra","instrument","history","response","bounds"]
r={name:json.loads((HERE/(name+".json")).read_text()) for name in names}
assert all(v["status"]=="PASS" and v["old_checkers_executed"]==0
           and v["mode_ODE_integrations"]==0 and v["geometry_ODE_integrations"]==0 for v in r.values())
assert all(r["algebra"]["identities"].values())
for name in ["success","failure"]:
    case=r["history"]["cases"][name]
    assert .004<case["x0_minus_x"][0]<=case["x0_minus_x"][1]<.0045
    assert .017<case["thermal_occupation_per_oscillator"][0]<=case["thermal_occupation_per_oscillator"][1]<.020
    response=r["response"]["cases"][name]
    assert response["variance_H_thermal"][0]>0
    assert response["characteristic_at_1"][1]<0<response["characteristic_at_3"][0]
assert r["history"]["all_eta_real_mean_history"]
assert not r["history"]["operator_constraint_solved"]
assert not r["history"]["parameters_reselected_in_time"]
assert not r["instrument"]["original_full_first_field_marginal_preserved"]
assert not r["instrument"]["S0_is_complete_energy_after_thermal_preparation"]
assert not r["instrument"]["preservation_extended_to_record_dependent_geometry_preparation"]
assert r["response"]["zero_high_cross_noise_retained"]
assert not r["response"]["new_local_noise_kernel_numerically_summed"]
floor=r["bounds"]["all_record_static_thermal_noise_floor"]
assert floor["record_count_unrestricted"] and floor["zero_high_conditional_product_required"]
assert not floor["mean_SCE_disproved"] and not floor["geometry_fluctuation_lower_bound"]
finish("review.py",{
 "independent_rational_checks":{"shifted_root_bracket":True,"root_derivative":True,
      "thermal_positivity":True,"rare_event_two_radial_gaps":True,
      "density_cap_variance_integral":True,"relative_residual_RMS_above_ten_percent":True},
 "scientific_verdict":{"conditional_mean_histories":"CLOSED within stated new static CQ preparation",
      "normal_state_and_all_record_energy_law":"CLOSED",
      "global_static_thermal_record_refinement_escape":"EXCLUDED within same preparation",
      "fixed_state_stability":"positive growth mode persists",
      "full_gravitational_fluctuation_feedback":"OPEN","physical_local_device":"OPEN",
      "Core_physical_selection_and_unification":"OPEN"},
 "native_mathematical_review_agents":3,"external_peer_review_claimed":False,
 "old_scientific_files_modified":False},
 extra=tuple(name+suffix for name in names for suffix in [".py",".json"]))
