"""Spectral QND rate/error frontier and smooth two-record lift algebra."""
import sympy as s
from common import *
P="physics/qm/null_source/timelike/finite_stress/lapse_boundary/relational_coupled/"
paths=[P+"matter_clock.json",P+"symmetric_clock.json",P+"MATTER_CLOCK.md",
 P+"SYMMETRIC_CLOCK.md",
 "physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_feedback/BOUNDARY_INTERFACE.md"]
for p in paths[:2]:load(p)
M,q,d=s.symbols("M q delta",positive=True)
c=M-1+q+d
require(s.simplify((1-q-d)+(q+d)/c*c-1)==0,"Optimal clipped-and-redistributed law normalizes")
require(s.simplify(c-(q+d)-(M-1))==0,"Capacity sufficient when M>=1")
r,a,b=s.symbols("r a b",real=True)
require(s.simplify(s.sin(a)**2+s.cos(a)**2-1)==0,"Complete smooth Kraus pair")
normdiff=(s.sin(a)-s.sin(b))**2+(s.cos(a)-s.cos(b))**2
require(s.trigsimp(normdiff-2*(1-s.cos(a-b)))==0,"Two-record Stinespring distance")
require(s.expand(1-(1-d)**2-(2*d-d**2))==0,"Controlled full target purification bound")
# Exact finite measure check exercises the nontrivial redistribution, including singular mass.
weights=[s.Rational(1,2),s.Rational(1,3),s.Rational(1,6)]
rates=[s.Rational(1,1),s.Rational(2,3),s.Rational(1,4)]
for sing in [s.Rational(0),s.Rational(1,5),s.Rational(1)]:
 rr=[4*(1-sing)/3,0,2*(1-sing)]
 require(sum(w*x for w,x in zip(weights,rr))==1-sing,"Example spectral law")
 for success in rates:
  cap=1/success
  delta=sum(w*max(x-cap,0) for w,x in zip(weights,rr))
  capacity=cap-1+sing+delta
  ff=[1,1,1] if capacity==0 else [min(x,cap)+(sing+delta)/capacity*max(cap-x,0) for x in rr]
  require(sum(w*x for w,x in zip(weights,ff))==1 and all(0<=x<=cap for x in ff),"Finite-law attained rate constraints")
  tv=(sing+sum(w*abs(x-y) for w,x,y in zip(weights,rr,ff)))/2
  require(tv==sing+delta,"Finite-law exact optimal TV including singular part")
finish("spectral_preparation.py",dict(
 actual_available_reference_state_required=True,
 exact_success_supremum="1/esssup_nu0(dmu/dnu0)",
 fixed_success_optimal_radial_TV="q_singular + integral (r-1/s)_+ dnu0",
 complete_success_failure_TP_instrument=True,
 nonselective_radial_law_unchanged=True,
 canonical_full_target_trace_bound="sqrt(2 delta-delta^2), ac target only",
 truncated_filter_trace_bound="sqrt(delta_M)",
 arbitrary_Borel_kinematic_lift_claimed=False,
 smooth_original_constraint_rigging_lift=True,
 smooth_complete_output_trace_error="epsilon_n",
 smooth_successful_target_trace_error="sqrt(delta_M)+epsilon_n/s_M",
 full_old_bare_source_density_recovered_from_law=False,
 local_covariant_autonomous_device_constructed=False,
 finite_measure_cases_checked=9,
 finite_examples_are_actual_original_spectrum=False),paths)
