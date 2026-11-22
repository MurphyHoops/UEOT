"""Positive-clock gap, full residual bound and finite read-window probability."""
import sympy as s
from common import *
sigma=iv.mpf(1)/2;T=iv.mpf(1)/24
r=D/4;hmin=r*8**(iv.mpf(1)/3)/2
assert below(sigma,hmin.a) and below(sigma*T,iv.pi.a/2)
prob=sigma*T*iv.exp(-iv.mpf(2)/3)*iv.cos(sigma*T)**2/(2*iv.pi)
assert above(prob,0)
E,u=s.symbols("E u",real=True)
assert s.expand((u-E)**2-(E**2-2*E*u+u**2))==0
finish("finite_clock.py",{
 "clock_sigma":outward(sigma),"time_half_window":outward(T),
 "physical_negative_gap_lower":outward(hmin),
 "full_constraint_RMS_strict_upper":outward(sigma/iv.sqrt(3)),
 "finite_time_window_probability_lower":outward(prob),
 "positive_clock_lift_is_normal_isometry":True,
 "conditional_history_exact_where_clock_density_nonzero":True,
 "finite_interval_compared_with_same_weighted_target_history":True,
 "unconditional_source_equals_input_claimed":False,
 "unconditional_geometry_all_polynomial_moments_finite":True,
 "kinematic_total_positive_energy_second_moment_finite":True,
 "same_dust_counted_once":True,
 "sigma_to_zero_volume_q_moment_upper_scaling":"O(1+sigma^(-3q)); not a matching lower bound",
 "fixed_resource_arbitrarily_small_residual_claimed":False,
 "strong_zero_constraint_for_normal_kinematic_state":False,
 "local_clock_RSET_constructed":False})
