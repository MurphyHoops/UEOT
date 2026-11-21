"""Exact harmonic sums and an outward full-field smearing/tail certificate."""
import math
import sympy as s
from common import finish,require,iv,outward,above,below
m,j=s.symbols('m j',integer=True,positive=True)
d=2*j-(m-1);ell=m*m-1
sumd=s.summation((d*d-ell/3)**2,(j,0,m-1))
target=4*m*(m*m-1)*(m*m-4)/45
require(s.simplify(sumd-target)==0,'Gaunt shell arithmetic')
# Central degree-11 B-spline value = exact squared norm of order-6 spline.
norm=sum((-1)**j*s.binomial(12,j)*(6-j)**11 for j in range(7))/s.factorial(11)
require(norm==s.Rational(655177,1663200),'spline norm')
# m=3 finite-mode shell: central pair contributes 2/3.
dvals=[-2,0,2];weights=[(s.Rational(d*d)-s.Rational(8,3))**2 for d in dvals]
require(s.simplify(weights[1]/sum(weights))==s.Rational(2,3),'last cutoff shell')
n,L=s.symbols('n L',positive=True)
v=s.Matrix([1,-s.I*n/L,(1-3*n*n/L)/(2*(L-3))])
require(s.simplify(s.I*n+L*v[1])==0,'temporal Ward mode')
require(s.simplify(-s.I*n*v[1]+s.Rational(1,3)+(2-2*L/3)*v[2])==0,'spatial Ward mode')
delta=iv.mpf(1)/600;V=2*iv.pi**2;ns=iv.mpf(2);C=ns/(9*V)
sinc=lambda x:iv.sin(x)/x
variance=C*(iv.pi*iv.mpf(655177)/(3326400*delta)-iv.mpf('.5')-sinc(delta)**12)
require(above(variance),'positive spatially nonconstant noise')
K=10000
partial=C*(sum((sinc(iv.mpf(j)*delta)**12 for j in range(2,K)),iv.mpf(0))
           +iv.mpf(2)/3*sinc(K*delta)**12)
tail=C*(iv.mpf(1)/3/(K*delta)**12+1/(11*delta**12*K**11))
difference=variance-partial
require(above(difference) and bool(difference.b<=tail.b),'complete finite-K bound')
finish('spatial_noise.py',{'real_scalars':2,'harmonic':3,'delta':'1/600',
 'test_regular':{'C4':True,'W5_1':True,'C_infinity_claimed':False},
 'variance_bounds':outward(variance),'RMS_bounds':outward(iv.sqrt(variance)),
 'mode_cutoff':K,'cutoff_variance_bounds':outward(partial),
 'omitted_variance_bounds':outward(difference),'omitted_variance_upper_bound':outward(tail),
 'low_harmonic_vacuum_noise_zero':[1,2],
 'scalar_stress_cross_block_retained':True,
 'vector_tensor_stress_sectors_completed':False,
 'scope':'fixed-background conformal vacuum, normalized compact smearing',
 'sharp_time_full_stress_variance_finite':False})
