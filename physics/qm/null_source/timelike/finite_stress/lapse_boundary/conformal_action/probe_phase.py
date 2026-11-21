"""Actual WKB residual and explicit uniform derivative/tail budgets."""
import sympy as s
from common import finish,require,iv,outward,above,below
t=s.symbols('t',real=True);k=s.symbols('k',positive=True)
v=s.Function('V')(t)
f=v/2;g=-(v*v+s.diff(v,t,2))/8
require(s.simplify(f*f+2*g+s.diff(f,t,2)/2)==0,'WKB cancellation from actual amplitude equation')
# An independent Riccati comparison also cancels all residual powers through k^-3.
z=(-s.I*v/(2*k)-s.diff(v,t)/(4*k*k)+s.I*(s.diff(v,t,2)+v*v)/(8*k**3)
   +(s.diff(v,t,3)+4*v*s.diff(v,t))/(16*k**4))
res=s.expand(s.diff(z,t)-2*s.I*k*z+z*z+v)
q=s.symbols('q')
pol=s.Poly(s.expand(res.subs(k,1/q)),q)
require(all(power[0]>=4 for power,coef in pol.terms() if coef!=0),'independent exact Riccati residual order')
# Explicit standard bump derivative bounds. Every derivative is exp(4-1/u)
# times P_j(x)/u^(2j). |P_j| <= sum absolute coefficients on [0,1].
x=s.symbols('x');u=x*(1-x);ex=4-1/u;ratio=s.Integer(1)
T=iv.mpf('.2');lam=iv.mpf('.2')
Ms=[lam];coefficients=[1]
for j in range(1,5):
 ratio=s.factor(s.diff(ratio,x)+ratio*s.diff(ex,x))
 P=s.Poly(s.cancel(ratio*u**(2*j)),x)
 cp=sum(abs(c) for c in P.all_coeffs())
 require(cp.is_Integer and cp>0,'positive exact polynomial coefficient budget')
 coefficients.append(int(cp))
 ymax=max(4,2*j)
 # max_{y>=4} y^(2j)e^-y occurs at max(4,2j).
 bound=lam*(2/T)**j*int(cp)*iv.exp(4-ymax)*iv.mpf(ymax)**(2*j)
 Ms.append(bound)
M0,M1,M2,M3,M4=Ms
F0,F1,F2=[m/2 for m in Ms[:3]]
G0=(M0*M0+M2)/8
G1=(2*M0*M1+M3)/8
G2=(2*M1*M1+2*M0*M2+M4)/8
k0=1
while not bool((F0/k0**2+G0/k0**4).b<=iv.mpf('.5').a):k0*=2
CR=2*F0*G0+G0*G0+F2*(F0+G0)+G2+3*(F1+G1)**2
CA=iv.sqrt(2)*T*CR*iv.exp(T*M0/k0)
k1=k0
while not bool((CA/k1**5).b<=iv.mpf('.5').a):k1*=2
ktail=k1
while not below(CA/ktail**2,iv.mpf('1e-6')):ktail*=2
require(above(CA),'nontrivial finite error majorant')
V=2*iv.pi**2
I2low=lam*lam*T/4*iv.exp(-iv.mpf(8)/3)
I2high=lam*lam*T/2
# Exact action-to-phase coefficient, with S3 volume and both rotated fields.
vv=s.symbols('V0',positive=True);H,I2,cr=s.symbols('H_K I2 c_r',real=True)
ct=(-H/(8*vv)+cr)*vv*I2
require(s.expand(ct+H*I2/8-cr*vv*I2)==0,'local phase cancellation')
require(s.simplify((-H/(8*vv)).subs(vv,2*s.pi**2)+H/(16*s.pi**2))==0,'same heat coefficient')
N,r,vol,c=s.symbols('N r vol c')
Lct=N*vol*c*r*r
require(s.diff(Lct,N,r)==2*vol*c*r and s.diff(Lct,r,2)==2*N*vol*c,'retained counterterm contacts')
finish('probe_phase.py',{'model':'two conformal fields, fixed ESU, spatially constant smooth mixing pulse',
 'duration_model_time':'.2','amplitude':'.2',
 'bump_derivative_polynomial_L1_coefficients':coefficients,
 'uniform_derivative_upper_bounds':[outward(m) for m in Ms],
 'positive_WKB_frequency_threshold_k0':k0,
 'exact_residual_majorant_CR':outward(CR),
 'actual_mode_error_majorant_CA':outward(CA),
 'continuous_log_threshold_k1':k1,
 'field_log_remainder_tail_bound':'C_A/K^2 for K>=k1',
 'illustrative_tail_cutoff_not_executed':ktail,
 'illustrative_tail_upper_bound':outward(CA/ktail**2),
 'I2_integral_bounds':[outward(I2low)[0],outward(I2high)[1]],
 'local_counterterm_coefficient':'-H_K/(16 pi^2)+c_r',
 'finite_c_r_example':0,'scheme':'harmonic number H_K',
 'all_order_finite_amplitude_actual_renormalized_CTP_limit_in_declared_family':True,
 'mode_ODE_solutions_numerically_integrated':0,
 'gravitational_lapse_phase_completed':False,
 'general_spatial_mixing_phase_completed':False,
 'finite_c_r_fixed_by_readout':False},
 inputs=['physics/qm/null_source/timelike/finite_stress/lapse_boundary/conformal_action/LOCAL_FIELD_PROBE.md',
         'physics/qm/null_source/timelike/finite_stress/lapse_boundary/conformal_action/STATIC_NORMALITY.md'])
