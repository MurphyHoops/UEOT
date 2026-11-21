"""Outward fixed-prefix witness bounds and exact projection identities."""
from __future__ import annotations
import sympy as sp
from common import finish, require, iv, interval, outward, above, below
a=iv.mpf(11)/10; b=iv.mpf(19)/10
b1=iv.mpf(13)/10; a2=iv.mpf(17)/10
J=3; M=10**6; s=iv.mpf(4); beta=1+b*b; r0=beta/J**2
eps=b*b/(4*(1-r0)*iv.sqrt(M))+3*(b-a)*beta**2/(32*(1-r0)**iv.mpf("2.5")*M**2)
delta=iv.sin((s/4)*(1/b1-1/a2))**2
require(below((s/2)*(1/a-1/b),iv.pi.a),"No phase wrapping")
require(above(delta),"Strict witness gap")
require(below(eps+eps**2,(delta/4).a),"Fixed prefix tail below gap")
# Exact two-component illustrative projection, independent of the tail estimates.
z=sp.exp(sp.I*sp.Rational(2,3))
v=sp.Matrix([sp.sqrt(2)/2,sp.sqrt(2)/2])
F=sp.diag(1,z); P=v*v.conjugate().T
chi=(1+z)/2
prob=(v.conjugate().T*F.conjugate().T*P*F*v)[0]
require(sp.simplify(prob-chi*sp.conjugate(chi))==0,"Fixed coherent projection expectation")
finish("bounded_witness.py",{
"profile":"two translated smooth bumps, supports [11/10,13/10],[17/10,19/10], masses 1/2",
"J":J,"fixed_M":M,"s":4,"prefix_norm_error_outward":outward(eps),
"strict_gap_lower_outward":outward(delta),"eventual_C5_drop_at_least_outward":outward(delta/2),
"eventual_C9_drop_at_least_outward":outward(delta/4),
"quantified_actual_K_threshold":False,
"observable":"one fixed bulk finite-prefix coherence projection",
"local_autonomous_detector_constructed":False,
"multiplication_B_observes_this_layer":False
},inputs=[
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_feedback/CORRELATED_GAUSSIAN.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_propagation/INITIAL_LAYER.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_propagation/RARE_PREPARATION.md"])
