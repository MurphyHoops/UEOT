"""Finite-stress dust exclusion: exact coefficients and quantitative source gap."""
import sympy as s
from common import *
V,v=s.symbols("V v",positive=True)
c=s.Rational(3,8)/V
pc2=c/2
assert s.simplify(pc2-s.Rational(3,16)/V)==0
disk=s.simplify(s.pi*pc2/(2*s.pi*v))
assert disk==s.Rational(3,32)/(V*v)
x,ell,nu=s.symbols("x ell nu",positive=True)
g=nu**2+s.Rational(1,4)
u=s.sqrt(x)*s.cos(nu*s.log(x/ell))
w=s.sqrt(x)*s.sin(nu*s.log(x/ell))
for b in [u,w]:
    assert s.simplify(s.diff(b,x,2)+g*b/x**2)==0
for b in [s.sqrt(x),s.sqrt(x)*s.log(x/ell)]:
    assert s.simplify(s.diff(b,x,2)+b/(4*x**2))==0
# A full logarithmic period has positive square integral independently of phase.
y,phase=s.symbols("y phase",real=True)
period=s.integrate(s.cos(nu*y+phase)**2,(y,0,2*s.pi/nu))
assert s.simplify(period-s.pi/nu)==0
E,eta,t=s.symbols("E eta t",real=True)
z=t+s.I*eta
assert s.simplify(s.re(-s.I*E*z)-E*eta)==0
# The graph functional representative is conjugated in the first slot.
assert s.simplify(s.conjugate(1/(E+s.I))*(E-s.I))==1
bound=3/(32*V0*VP)
threshold=3/(16*V0)
assert below(bound,iv.mpf("2.85e-12"))
assert above(VP,1669000000) and above(V0,iv.mpf("19.73"))
rational=s.Rational(3,32)/(s.Rational(1973,100)*1669000000)
assert rational==s.Rational(3,1053739840000)
assert rational<s.Rational(285,10**14)
finish("dust_regularity.py",{
 "positive_matter_form":"K0=|P|^2/(2*x^2)",
 "critical_momentum_squared":outward(threshold),
 "original_subcritical_probability_upper":outward(bound),
 "rational_probability_upper":str(rational),
 "original_vs_any_admissible_source_trace_distance_lower":outward(1-bound),
 "mixed_state_and_source_geometry_correlations_covered":True,
 "finite_total_H_second_moment_required":True,
 "positive_dust_nonpositive_H_sector_required":True,
 "open_time_interval_finite_positive_K_required":True,
 "compact_spectral_support_required":False,
 "fixed_decomposable_separated_extension_required":True,
 "LC_LP_scalar_cyclic_trace_and_weighted_measure_in_proof":True,
 "Schwarz_reflection_and_Fourier_uniqueness_in_proof":True,
 "every_individual_time_divergence_claimed":False,
 "all_quantizations_or_all_physical_Hilbert_spaces_excluded":False,
 "original_momentum_law_and_stress_equivalent_family_embeddable":False,
 "positive_clock_code_can_be_spliced_without_new_dynamics":False,
 "operator_self_adjointness_retracted":False,
 "analytic_domain_theorem_computer_formalized":False,
 "next_gate":"independently justified finite-positive-stress geometric domain",
 "whole_physical_unification":"OPEN"},extra=["GRAVITY_CONTRACT.md","gravity_contract.json"])
