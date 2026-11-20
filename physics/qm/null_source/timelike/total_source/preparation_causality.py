"""Causal geometry, bounded Weyl coefficient and duration gate."""
import sympy as s
from mpmath import iv
from common import *
delta=s.symbols("delta",positive=True)
# Minimum cap distance minus maximum causal time for the selected diamond.
assert s.simplify(delta-delta/8-3*delta/8)==delta/2
d,c,e,Z=s.symbols("d c e Z",positive=True)
connecting=e*Z/(2*d)
assert s.simplify(4*c*connecting-2*c*e*Z/d)==0
ratio=24*A*(iv.pi-exact(1)/128)
proper=A*(iv.pi-exact(1)/128)
assert above(ratio,"6140000")
finish("preparation_causality.py",{
 "proof":"PREPARATION_CAUSALITY.md",
 "necessary_static_cap_conformal_duration":"T>=pi-chi0",
 "strict_short_cap_exact_global_pair_preparation_excluded":True,
 "bounded_local_Weyl_witness_explicit":True,
 "correlated_joint_inputs_allowed_without_assuming_reduced_CPTP_map":True,
 "approximate_outputs_max_trace_error_lower":"abs(Delta<W_lambda>)/4",
 "example_chi0":"1/128","example_proper_duration_lower":outward(proper),
 "example_ratio_to_old_response_window":outward(ratio),
 "equality_case_claimed_achievable":False,
 "postselected_or_distributed_protocols_excluded":False,
 "abstract_global_dilation_claimed_short_local_instrument":False
},("PREPARATION_CAUSALITY.md","COHERENCE.md","PREPARATION.md","PRESSURE_NOISE.md"))
