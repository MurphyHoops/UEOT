"""Conditional causal response gains and retained-pole normalizations."""
import sympy as s
from mpmath import iv
from common import *
sig,O,dp,Ap,der=s.symbols("sig O dp A der",positive=True)
rc=sig/((sig**2+O**2)*der);rs=O/((sig**2+O**2)*der)
assert s.simplify(Ap**4*dp*(rc**2+rs**2)-Ap**4*dp/((sig**2+O**2)*der**2))==0
num=16*WEIGHT*D*(OMEGA/(3*V0*A**4))**2
T=box(CAUSAL["short_conformal_window"])
gain=box(CAUSAL["short_window_sup_w_per_sup_f"])
assert below(gain,"4.2e-14")
assert CAUSAL["both_positive_poles_retained"] is True
curv=12*iv.sqrt(num)*gain*iv.sqrt(1+(2*OMEGA*T)**2)
relative=2*A**2*iv.sqrt(num)*gain*iv.sqrt(1+(2*OMEGA*T)**2)
finish("response.py",{
 "proof":"RESPONSE.md","conformal_window":outward(T),
 "conditional_sqrt_added_curvature_variance_upper":outward(curv),
 "conditional_sqrt_added_curvature_variance_over_R0_upper":outward(relative),
 "both_positive_poles_retained":True,
 "finite_initial_qc_C5_or_qs_C6_claimed":False,
 "absolute_constraint_compatible_baseline_supplied":False,
 "source_geometry_cross_block_fixed_or_computed_in_actual_preparation":False,
 "old_bare_response_claimed_for_expanded_apparatus":False,
 "calibrated_gravitational_instrument_closed":False
},("RESPONSE.md","CONSTRAINTS.md","PRESSURE_NOISE.md"))
