"""Analytic strict constants for the complete normal finite-record construction."""
import sympy as s
from common import iv, above, below, outward, require, finish
# Normalize bump bounds analytically, rather than using a quadrature error estimate.
peak=iv.exp(iv.mpf(2)/3)
mu_lower=iv.exp(-iv.mpf(2)/3)/64
require(below(peak,2) and above(mu_lower,iv.mpf(1)/128),"Bump inequalities")
x=s.symbols("x",nonnegative=True)
require(s.integrate(2*x*(1-x),(x,0,1))==s.Rational(1,3),"Finite-pointer tail integral")
n=21; tau=s.Rational(1,420); r=s.Rational(1,n)+tau
require(r==s.Rational(1,20),"Every-output error support")
q=iv.mpf(1)/5; succ=iv.mpf(19)/20
angle=(iv.sqrt(succ*(1-q))-iv.sqrt(q*(1-succ)))**2
require(above(angle,".59"),"State disturbance bound")
require(s.Rational(1,400)*128==s.Rational(8,25),"Variance-improvement ratio")
x=s.symbols("x", real=True)
rot=s.Matrix([[s.cos(x),-s.sin(x)],[s.sin(x),s.cos(x)]])
require(s.simplify(rot.T*rot-s.eye(2))==s.zeros(2),"Exact normal unitary fiber")
m=rot[:,0]
require(s.simplify((m.T*m)[0])==1,"Complete record")
require(s.simplify((m.T*m.diff(x))[0])==0,"No cross derivative resource")
require(s.simplify((m.diff(x).T*m.diff(x))[0])==1,"Resource derivative norm")
# Diagonalization of the joint record is not used in the positive construction.
finish("smooth_preparation.py",dict(
 memory_dimension=21,
 minimum_levels_in_declared_continuous_spectral_record_class=21,
 residual_variance_strict_lower="B^2/21168", record_precision_over_bandwidth="1/20",
 smooth_transition_half_width_over_bandwidth="1/420",
 all_outcome_success_probability=1, postselection=False,
 residual_variance_strictly_between_zero_and="(8/25)*Var(C)",
 original_charge_spectral_law_preserved=True,
 bare_source_trace_distance_strict_lower="4/5",
 success_19_over_20_disturbance_lower=outward(angle),
 bump_peak_upper=outward(peak), bump_mu2_strict_lower=outward(mu_lower),
 finite_Q_and_dilation_moments=True,
 sharp_binning_finite_Q_resource_rejected=True,
 source_memory_cross_block_derived=True,
 memory_is_geometry_charge=False,
 compact_local_implementation_with_spacelike_complement_excluded=True,
 all_local_or_approximate_preparations_excluded=False,
 integral_diagnostics_are_not_interval_certificates=True),
 ["finite_stress/BOUNDARY_STATE.md","finite_stress/BOUNDARY_EXTENSION.md"],
 proof="SMOOTH_PREPARATION.md")
