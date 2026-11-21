"""Noncommutative full-generator residual and exact Taylor bookkeeping."""
import sympy as s
from common import *
t=s.symbols("t",real=True)
H,H0,H1=s.symbols("H H0 H1",commutative=False)
P=1-s.I*t*H0+t*t*(-s.I*H1-H0*H0)/2
res=s.I*s.diff(P,t)-H*P
rhs=-(H-H0-t*H1)+s.I*t*(H-H0)*H0+t*t*H*(s.I*H1+H0*H0)/2
require(s.expand(res-rhs)==0,"Full-generator Taylor residual")
v0,v1,v2,b0,b1,b2=s.symbols("v0 v1 v2 b0 b1 b2",commutative=False)
poly=(v0+t*v1+t*t*v2/2)*(b0+t*b1+t*t*b2/2)
tail=s.expand(poly).coeff(t,3)*t**3+s.expand(poly).coeff(t,4)*t**4
require(s.expand(tail-t**3*(v1*b2+v2*b1)/2-t**4*v2*b2/4)==0,"Projector cubic/quartic tail")
I,J,rt,rs,st0,st1,ta0,ta1=s.symbols("I J rt rs st0 st1 ta0 ta1",commutative=False)
rI=s.symbols("rI",commutative=False)
sigma=st0+t*st1+rs
exact_delta=ta0+t*ta1+rt-(I+t*J+rI)*sigma
linear=ta0-I*st0+t*(ta1-I*st1-J*st0)
require(s.expand(exact_delta-linear-(rt-I*rs-t*J*(sigma-st0)-rI*sigma))==0,"Correlation remainder grouping")
terms=[(i,k,l,i+k+l-3) for i in range(3) for k in range(3) for l in range(3) if i+k+l>=3]
require(len(terms)==17 and all(q[3]>=0 for q in terms),"Bounded-form tail inventory")
d,C=s.symbols("d C",positive=True)
require(s.simplify(d/2-C*(d/(4*C))-d/4)==0,"Positive-window expectation margin")
finish("positive_window.py",dict(
 full_generator_is_used_in_Taylor_residual=True,
 strong_raw_snapshot_domain_transport_required=False,
 H_error_upper="R_H t^3/3",
 Q_error_separately_proved="M_Q R_Q t^3/3",
 source_trace_and_weighted_trace_remainders=True,
 bounded_form_polynomial_tail_terms=len(terms),
 correlation_positive_window="min(T0,c_s Var(kappa^-1)/(2 C_Delta))",
 phase_pair_positive_window="min(T0,abs(c_s DeltaJ)/(4(Csigma+ + Csigma-)))",
 phase_pair_trace_distance_lower="abs(c_s DeltaJ) t^2/8",
 raw_pressure_positive_window=True,
 explicit_norm_formulas_not_numerically_evaluated=True,
 uniform_window_over_all_normal_states=False,
 window_is_SI_or_experimentally_reached=False),
 ["physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_feedback/WEIGHTED_EVOLUTION.md",
 "physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_feedback/CLOSURE_COUNTEREXAMPLE.md"])
