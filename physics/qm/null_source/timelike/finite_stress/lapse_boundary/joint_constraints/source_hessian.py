"""Independent interval spectral bounds and exact subtraction bookkeeping."""
import sympy as sp
from common import iv,require,above,below,outward,finish
mu=iv.mpf(1)/5
maxratio=iv.mpf(0)
for k in range(1,257):
    w=iv.sqrt(k*k+mu);v=iv.sqrt((k+1)**2+mu)
    W=k*(k+1)/(32*w*v);Om=w+v
    diff=iv.mpf(1)/(64*k)-W/Om
    require(above(diff) and below(diff,iv.mpf(1)/(80*k*k)),'spectral subtraction bound')
    if diff.b*k*k>maxratio.b:maxratio=diff*k*k
t=sp.symbols('t',nonnegative=True)
den=(1+t*t/5)*(1+t/2+t*t/10)
num=sp.expand((den-1)/t)
require(sp.expand(num-(sp.Rational(1,2)+3*t/10+t*t/10+t**3/50))==0,'elementary denominator expansion')
require(sp.expand(sp.Rational(4,5)*(1+t/2)-(sp.Rational(1,2)+21*t/50))==sp.Rational(3,10)-t/50,'uniform rational comparison')
K=256
h0=iv.mpf(1);h2=iv.mpf(1)
rt=(h0/40+h2/64)/(K-1)+h0/(32*K)
nt=h2*h2/(1536*(K-1)**3)
require(below(rt,iv.mpf('.000282')) and below(nt,iv.mpf('4e-11')),'unit-norm illustrative tails')
finish('source_hessian.py',{
 'mode_cutoff_edge_range':'k=1,...,K-1; scalar counterterm harmonic sum through K',
 'fourier_convention':'exp(+i Omega t)',
 'tested_spectral_range':[1,256],
 'maximum_k2_subtraction_difference_in_tested_range':outward(maxratio),
 'analytic_all_k_bound':'0 <= 1/(64k)-W_k/Omega_k <= 1/(80 k^2)',
 'K256_response_tail_for_unit_declared_norms_upper':outward(rt),
 'K256_noise_tail_for_unit_second_derivative_norm_upper':outward(nt),
 'quadratic_noise_positive':True,'causal_response_with_local_contact':True,
 'actual_same_cutoff_Hessian_limit':True,
 'extra_trace_source_finite_terms':'declared zero, not inferred from old traceless datum',
 'sharp_source_force_variance_finite':False,
 'general_metric_Hessian':False
},inputs=['physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/SOURCE_ACCOUNTING.md',
'physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/LOCAL_PREPARATION.md'])
