"""Symbolic constraints and directed bounds for an autonomous classical pulse."""
from common import *
import sympy as sp
a,a0,k0,v0,u0=sp.symbols("a a0 K V0 U0",positive=True)
h2=2*u0/3+2*k0/(3*v0**2*a**6)-1/a**2
hdot=sp.simplify(a*sp.diff(h2,a)/2)
rho=sp.simplify(sp.Rational(3,2)*(h2+1/a**2))
press=sp.simplify(-hdot-(3*h2+1/a**2)/2)
assert sp.simplify(rho-u0-k0/(v0**2*a**6))==0
assert sp.simplify(press+u0-k0/(v0**2*a**6))==0
assert sp.simplify(h2.subs({u0:3/(2*a0**2),k0:v0**2*a0**4,a:a0})-sp.Rational(2,3)/a0**2)==0
p,pc,b=sp.symbols("p pc b",positive=True)
assert sp.simplify(sp.diff(p/sp.sqrt(pc**2-b*p**2),p)-pc**2/(pc**2-b*p**2)**sp.Rational(3,2))==0
gap=exact(14)/15
length=exact(1)/20
zeta_budget_factor=3/(2*iv.sqrt(14))
time_over_a0=-iv.log(1-zeta_budget_factor)/(3*iv.sqrt(exact(5)/3))
gain_hi=exact(2)/75*iv.sqrt(exact(15)/14)
assert below(zeta_budget_factor,1)
assert above(iv.exp(-exact(1)/3),exact(2)/3)
assert above(time_over_a0,exact(132)/1000) and below(time_over_a0,exact(133)/1000)
assert above(gain_hi,exact(1)/120) and below(gain_hi,exact(28)/1000)
benchmark_a0=iv.sqrt(3/(2*U0))
finish("autonomous.py",{
 "proof":"AUTONOMOUS.md",
 "benchmark_a0":outward(benchmark_a0),
 "classical_crossing_proper_time_over_a0_upper":outward(time_over_a0),
 "classical_probe_displacement_strict_lower":"1/120",
 "classical_probe_displacement_upper":outward(gain_hi),
 "finite_available_clock_time_budget_fraction_upper":outward(zeta_budget_factor),
 "complete_density_equals_pressure":"K/(V0^2*a^6)",
 "both_leading_GR_equations_and_initial_constraints_checked":True,
 "controller_and_interaction_included_in_classical_total_source":True,
 "same_original_CQ_initial_state_or_full_AE_QFT_claimed":False,
 "quantum_ordering":"nonnegative Friedrichs Laplace-Beltrami",
 "classical_crossing_bound_claimed_for_all_quantum_wavepackets":False,
 "local_small_cap_quantum_device_implemented":False},("AUTONOMOUS.md","FIELDSPACE.md"))
