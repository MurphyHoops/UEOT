"""Quantitative residual and selection bounds, including all-record static cap."""
from common import *
assert above(NU,16)
# Density f_r(s)=(nu/2)exp[-nu(s+r)/2] I0(nu*sqrt(rs)).
# I0(z)<=exp(z)*sqrt(pi)/(2*sqrt(2z)); small s uses I0<=exp(z).
small_region_ratio=8*iv.exp(-2)/iv.sqrt(iv.pi)
assert below(small_region_ratio,1)
density_cap=iv.sqrt(iv.pi*NU)/4
finite_two_record_floor=4/(3*iv.pi*NU*4)
assert above(finite_two_record_floor)
# Gaussian reverse-triangle tail for the interval in the gap of the two rings.
gap_low=iv.sqrt(1+D/4)-1
gap_high=iv.sqrt(1+D)-iv.sqrt(1+3*D/4)
assert above(gap_low,iv.mpf(2)/25) and above(gap_high,iv.mpf(2)/25)
log_success_upper=iv.log(2)-2*NU/625
assert below(log_success_upper,iv.log(2)-iv.mpf("1.152e9"))
# G>0 implies N'<-3/2-k/x, so all n>=0 static branches have x<=x0,
# mu<=mu_old. Total variance then gives an all-record floor (no N limit).
assert below(E(X0),0)
all_record_variance_floor=iv.mpf(3)/16+L/NU0
density_floor=M**2*all_record_variance_floor/(4*X0**6)
relative_floor=M**2*all_record_variance_floor/(9*X0**4)
universal_relative_floor=1/(48*L**2)
assert above(universal_relative_floor,iv.mpf(1)/100)
assert above(iv.sqrt(universal_relative_floor),iv.mpf(1)/10)
# The stronger comparison M2/x0^2>1/L uses the exact inherited root
# identity, not interval subtraction of two correlated wide parameters.
finish("bounds.py",{
 "density_bound":{"formula":"sup f_S0 <= sqrt(pi*nu)/(4*sqrt(rmin))",
       "rmin":1,"nu_rmin_at_least":16,"density_cap":outward(density_cap),
       "small_region_to_cap_ratio_at_nu_rmin_16":outward(small_region_ratio)},
 "finite_classical_records":{"average_conditional_variance_lower":"4*rmin/(3*pi*nu*N^2)",
       "two_record_floor":outward(finite_two_record_floor),
       "selected_N_records_mass_p_unnormalized_lower":"4*rmin*p^3/(3*pi*nu*N^2)",
       "preserves_nonselective_S0_law_required":True},
 "rare_mean_preserving_selection":{"mean_window":"abs(mu_selected-L)<=d/8",
       "variance_at_most":"d^2/128","gap_radius_distances":[outward(gap_low),outward(gap_high)],
       "success_upper":"2*exp(-2*nu/625)","log_success_upper":outward(log_success_upper),
       "arbitrary_filter_without_preserved_input_law_covered":False},
 "global_static_thermal_cap":{"mu_upper":"mu_old=L+2/nu0","radius_upper":"x0",
       "positive_mu_unique_root":True,"all_positive_radius_roots_covered":True,
       "N_derivative_on_G_positive":"N'<-3/2-kappa/x<0",
       "n_nonnegative_required":True,"U0_and_M2_fixed":True},
 "all_record_static_thermal_noise_floor":{
       "conditional_variance_S0_lower":"3/16+L/nu0",
       "numeric_lower_enclosure":outward(all_record_variance_floor),
       "average_conditional_density_variance_lower":outward(density_floor),
       "average_branch_relative_density_variance_lower":outward(relative_floor),
       "universal_strict_relative_variance_lower":outward(universal_relative_floor),
       "universal_strict_record_weighted_relative_RMS_lower":outward(iv.sqrt(universal_relative_floor)),
       "record_count_unrestricted":True,
       "complete_energy_marginal_preserved":True,
       "zero_high_conditional_product_required":True,
       "mean_SCE_disproved":False,"geometry_fluctuation_lower_bound":False},
 "acceptance_scope":"extra second-moment/operator-constraint requirement, distinct from mean SCE",
 "external_matter_nonstatic_or_changed_U_excluded_by_this_theorem":False})
