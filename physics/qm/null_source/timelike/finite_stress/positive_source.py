"""Gaussian source moments and dust-density commutator constants."""
import sympy as s
from common import *
t,v,k,r=s.symbols("t v k r",positive=True)
mgf=s.exp(t*k*r/(1-2*v*t))/(1-2*v*t)
m1=s.diff(mgf,t).subs(t,0)
m2=s.diff(mgf,t,2).subs(t,0)
assert s.simplify(m1-(2*v+k*r))==0
assert s.simplify(m2-(8*v**2+8*v*k*r+k**2*r**2))==0
rhi=1+s.sqrt(3)/2
assert s.simplify((1+rhi**2)/2-(s.Rational(11,8)+s.sqrt(3)/2))==0
n,g,delta=s.symbols("n g delta",positive=True)
edge=g*delta*s.sqrt(n*(n+1))*(1/s.sqrt(delta*(n+1))-1/s.sqrt(delta*n))
assert s.simplify(edge-g*s.sqrt(delta)*(s.sqrt(n)-s.sqrt(n+1)))==0
P2=2*VP+K2*L
P4=8*VP**2+8*VP*K2*L+K2**2*(iv.mpf(11)/8+iv.sqrt(3)/2)
cc=GAMMA*iv.sqrt(DELTA)*(iv.sqrt(3)-1)
assert above(P2) and above(P4)
finish("positive_source.py",{
 "original_P_squared_mean":outward(P2),"original_P_fourth_mean":outward(P4),
 "dust_inverse_sqrt_commutator_norm_upper":outward(cc),
 "dust_density_H2_coefficient":outward(2/(V0**2*DELTA**2)),
 "dust_density_additive_second_moment_upper":outward(2*GAMMA**2*(iv.sqrt(3)-1)**2/V0**2),
 "zero_density_second_moment_coarse_upper":outward(P4/(4*V0**2*DELTA**4)),
 "positive_total_J2_bound":"3[(V0 U0)^2 <v^2>+<P^4>/(4 delta^2)+<H^2>]",
 "strict_negative_sector_dense_closed_positive_forms":True,
 "no_infinite_energy_cancellation":True,
 "total_positive_energy_variance_finite_each_finite_time_window":True,
 "dust_density_ordering":"(E^(1/2) Pi v^(-1/2) Pi)^*(E^(1/2) Pi v^(-1/2) Pi)/V0",
 "uncompressed_M_minusH_M_claimed_positive":False,
 "covariant_RSET_Ward_identity_proved":False,
 "all_high_moments_of_noncommuting_J_claimed":False})
