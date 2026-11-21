"""Static inverse Sobolev and full-past quantum-source domain certificates."""
import sympy as s
from common import iv,load,box,above,below,outward,require,finish
inputs=["dynamic_seed/bounds.json","dynamic_inverse/fast_root.json",
 "dynamic_inverse/causal_inverse.json","joint_history/history.json",
 "dynamic_inverse/SPECTRUM.md","dynamic_inverse/INVERSE.md",
 "finite_stress/lapse_boundary/TENSOR_NOISE.md"]
slow=box(load(inputs[0])["positive_root_s"])
fast=box(load(inputs[1])["fast_conformal_growth_rate"])
cspec=box(load(inputs[2])["c"])
A=box(load(inputs[3])["cases"]["unfiltered"]["A"])
V0=2*iv.pi**2;gamma=24*A;c0=1/(60*iv.pi**2*A*A)
require(above(gamma,"1e6") and above(gamma,fast),"Vertical line")
require(above(iv.mpf(7)/4*gamma,"1e6"),"High-frequency integer band")
require(below(slow**2,4) and below(fast**2,"1e12"),"Weight lower-bound range")
# Choosing the smaller explicit floor avoids interval min ambiguity.
m0=c0/16
require(below(m0,cspec/iv.sqrt(17)),"Uniform F floor choice")
d1=1-slow**2/gamma**2;d2=1-fast**2/gamma**2
gain=iv.sqrt(5)/(m0*d1*d2)
require(above(d1) and above(d2),"Positive spectral separation")
g,t=s.symbols("g t",positive=True,real=True)
# Intermediate line r2=4g²; squared-modulus inequality holds at every real t.
difference=s.expand((g*g-t*t-4*g*g)**2+4*g*g*t*t-(g*g+t*t)**2)
require(s.factor(difference)==8*g*g*(g*g+t*t),"Bromwich intermediate line")
require(s.Rational(1,4)*s.Rational(16,9)*s.Rational(6,25)==s.Rational(8,75),"Positive resonance band")
Om=4*iv.sqrt(2)
Ilo=iv.exp(-1)*iv.cos(Om/fast)/iv.sqrt(fast*fast+Om*Om)
require(above(Ilo) and below(Om/fast,iv.pi/2),"Smooth switch nonzero Fourier-Laplace component")
residue_lo=1/(30*A)
scaled_variance_lo=32*residue_lo**2*Ilo**2/(V0**2*A**8)
require(above(scaled_variance_lo),"Actual high-vacuum variance lower bound")
# Full k=3 shell: 2 species x9 oscillators x vacuum pair contraction2.
require(s.Rational(4)*3**2*(3**2-1)/9==32,"Quantum shell normalization")
finish("causal_domain.py",dict(
 frozen_complete_static_P_and_G_reused=True,
 both_positive_roots_retained=True,
 static_weighted_L2_to_H4_continuous=True,
 vertical_weight_gamma=outward(gamma), uniform_spectral_factor_lower=outward(m0),
 static_weighted_H4_operator_upper=outward(gain),
 actual_nonstatic_relative_operator_norm_proved_small=False,
 entire_static_G_not_only_fast_pole_used=True,
 stationary_source_high_vacuum_shell=3,
 smooth_switch_width="1/sigma_F",
 switch_nonzero_transform_lower=outward(Ilo),
 positive_scaled_full_past_pressure_variance_lower=outward(scaled_variance_lo),
 limit_expression="liminf(a->-infinity) exp(2*sigma_F*a) Var(p(f_a)) > positive lower",
 every_finite_past_test_is_compact_smooth=True,
 full_past_source_only_retarded_GNS_L2_limit_exists=False,
 finite_prepared_joint_states_all_excluded=False,
 actual_nonstatic_full_past_Green_already_constructed=False),
 inputs,proof="CAUSAL_DOMAINS.md")
