"""New complete second-moment static bound, with conditional positive parts."""
import sympy as s
from common import *
ell,nu=s.symbols("ell nu",positive=True)
mu=ell+1/nu;v=s.Rational(3,16)+2*ell/nu+1/nu**2
old=ell+2/nu
assert s.simplify(v+mu**2-old**2-(s.Rational(3,16)-2/nu**2))==0
aa,bb=s.symbols("aa bb",nonnegative=True)
assert s.expand((aa+bb)**2-aa**2)==2*aa*bb+bb**2
# The conditional positive part is essential before multiplying by a smaller coefficient.
assert 2*(-1)<1*(-1)
coarse=s.Rational(433,4305)
assert s.Rational(3,16)-s.Rational(2,1000**2)>s.Rational(433,1000)**2
assert coarse>s.Rational(1,10)
assert above(NU0,1000) and below(L,"1.435")
lower=iv.sqrt(exact(3)/16-2/NU0**2)/(3*L)
assert above(lower,".1007")
finish("static_bound.py",{
 "strict_record_weighted_relative_RMS_lower":outward(lower),
 "exact_input_second_moment_excess":"3/16-2/nu0^2",
 "rational_lower":str(coarse),
 "supersedes_old_correlated_static_seven_to_ten_percent_open_window":True,
 "all_records_retained":True,
 "arbitrary_zero_high_correlations_and_entanglement_allowed":True,
 "same_M2_U0_AE_two_fields_static_mean_and_stationary_high_required":True,
 "conditional_positive_part_before_radius_comparison":True,
 "every_individual_record_ten_percent_claimed":False,
 "sharp_optimum_claimed":False,"metric_RMS_or_experimental_sensitivity_claimed":False,
 "expanded_apparatus_or_nonstatic_model_included":False,
 "mean_SCE_disproved":False})
