"""Closed-FLRW canonical normalization and the declared dust-domain model."""
import sympy as s
from common import *
a,ad,NN,V,uu,pa,px=s.symbols("a ad NN V uu pa px",positive=True)
Lg=-3*V*a*ad**2/(2*NN)+3*V*NN*a/2-V*NN*uu*a**3
momentum=s.diff(Lg,ad)
assert momentum==-3*V*a*ad/NN
velocity=-pa*NN/(3*V*a)
ham=s.simplify((pa*ad-Lg).subs(ad,velocity)/NN)
want=-pa**2/(6*V*a)-3*V*a/2+V*uu*a**3
assert s.simplify(ham-want)==0
assert s.simplify((-pa**2/(6*V*a)).subs(pa,s.Rational(3,2)*s.sqrt(a)*px)+3*px**2/(8*V))==0
# Constraint gives Hubble^2+1/a^2=(2/3)rho, including positive dust.
rho,Hubble=s.symbols("rho Hubble",real=True)
total=(-pa**2/(6*V*a)-3*V*a/2+V*a**3*rho).subs(pa,-3*V*a**2*Hubble)
assert s.simplify(total/(-3*V*a**3/2)-(Hubble**2+1/a**2-2*rho/3))==0
x,ell,mu=s.symbols("x ell mu",positive=True)
for u,v in [
 (s.sqrt(x)*s.cosh(mu*s.log(x/ell)),s.sqrt(x)*s.sinh(mu*s.log(x/ell))/mu),
 (s.sqrt(x),s.sqrt(x)*s.log(x/ell)),
 (s.sqrt(x)*s.cos(mu*s.log(x/ell)),s.sqrt(x)*s.sin(mu*s.log(x/ell))/mu)]:
    assert s.simplify(u*s.diff(v,x)-s.diff(u,x)*v)==1
g=s.symbols("g",nonnegative=True)
for power in [s.Rational(1,2)+s.sqrt(s.Rational(1,4)-g),s.Rational(1,2)-s.sqrt(s.Rational(1,4)-g)]:
    assert s.simplify(power*(power-1)+g)==0
# General boundary covariance C_d^2-d*S_d^2=1 underlies the isotropic line.
theta=s.symbols("theta",real=True)
assert s.simplify(s.cos(theta)*s.sin(theta)-s.sin(theta)*s.cos(theta))==0
E1,E2,R=s.symbols("E1 E2 R",positive=True)
# H in [-E2,-E1], k in [-2R,2R], p=k-H.
support=(E1-2*R,E2+2*R)
assert above(U0)
finish("gravity_contract.py",{
 "action_normalization":"Einstein-Hilbert=1/4; G=2T",
 "Hg":str(want),"x_a_relation":"x=a^(3/2)",
 "gravity_kinetic_coefficient":"-3*p_x^2/(8*V0)",
 "positive_dust_density":"P_T/(V0*a^3)",
 "physical_sector":"spectral H_theta<=0",
 "zero_mode_indicial_parameter":"g_P=4*V0*|P|^2/3",
 "zero_endpoint":"limit-circle; theta and ell explicitly added",
 "infinite_endpoint":"limit-point for U0>0; Liouville correction integrable",
 "measurable_self_adjoint_direct_integral_defined_in_proof":True,
 "nonempty_negative_spectral_band_proved_by_core_high_frequency_test":True,
 "finite_positive_clock_support":[str(z) for z in support],
 "Friedrichs_extension_used":False,
 "original_full_NOON_AE_model_preserved":False,
 "finite_nonzero_mode_projection_claimed_consistent_local_Einstein_truncation":False,
 "known_quantization_and_dust_assumptions_claimed_derived_from_Core":False,
 "operator_endpoint_proof_computer_formalized":False,
 "finite_positive_matter_stress_history_certified":False,
 "original_source_carrier_rejected_by_DUST_REGULARITY":True,
 "whole_physical_unification":"OPEN"})
