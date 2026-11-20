"""Exact rare-flag experiment and data-processing scope."""
import math
import sympy as s
from mpmath import iv
from common import *
q=s.symbols("q",real=True)
w=(1-q)**8*q*q
assert w.subs(q,s.Rational(1,5))==s.Rational(65536,9765625)
threshold=iv.ln(exact(".1"))/iv.ln(1-2*WEIGHT)
shots=math.ceil(float(threshold.b))
err=iv.exp(shots*iv.ln(1-2*WEIGHT))/2
prev=iv.exp((shots-1)*iv.ln(1-2*WEIGHT))/2
assert below(err,".05") and above(prev,".05")
finish("discrimination.py",{
 "proof":"DISCRIMINATION.md","shell_trace_distance_main_endpoint":outward(2*WEIGHT),
 "single_shot_equal_prior_error":outward(exact(1)/2-WEIGHT),
 "mean_shots_to_nonoutside_flag":outward(1/(2*WEIGHT)),
 "first_independent_shots_for_error_below_0_05":shots,
 "error_at_certified_shots":outward(err),
 "universal_thermal_weight_max":"65536/9765625",
 "local_gravitational_implementation_or_calibration_proved":False,
 "data_processing_applied_to_unspecified_nonlinear_gravity":False
},("DISCRIMINATION.md","PREPARATION.md","TOTAL_FUTURE.md"))
