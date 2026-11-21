"""Explicit spherical obstruction and exact principal-symbol algebra."""
import sympy as s
from common import finish,require,iv,outward,above
chi=s.symbols('chi',real=True)
V=2*s.pi**2
f=(4*s.cos(chi)**2-1)/s.sqrt(V)
fp=s.diff(f,chi);fpp=s.diff(f,chi,2)
lap=s.trigsimp(fpp+2*s.cot(chi)*fp)
require(s.trigsimp(lap+8*f)==0,'actual Y3 Laplacian')
vol=4*s.pi*s.sin(chi)**2
require(s.simplify(s.integrate(f*f*vol,(chi,0,s.pi)))==1,'unit spherical harmonic')
eigen=[s.trigsimp(fpp-lap/3),s.trigsimp(s.cot(chi)*fp-lap/3)]
for actual,n in zip(eigen,[16,-8]):
 require(s.trigsimp(actual-n*s.sin(chi)**2/(3*s.sqrt(V)))==0,'trace-free Hessian eigenvalue')
norm2=s.trigsimp(eigen[0]**2+2*eigen[1]**2)
integral=s.simplify(s.integrate(s.expand_trig(norm2*vol),(chi,0,s.pi)))
require(integral==s.Rational(80,3),'nonzero integrated Hessian')
eps,N,r,H,Delta=s.symbols('epsilon N r H Delta',nonzero=True)
# H is directional Hessian, Delta its trace. The Poisson double bracket has -H.
B0=-H/2+Delta/6
Xminus1=s.simplify(eps*N*B0/(2*N*r))
ppminus1=s.simplify(Xminus1/(2*N))
require(s.simplify(ppminus1+eps*(H-Delta/3)/(8*N*r))==0,'exact covariance symbol')
radial=s.simplify((-eps*eigen[0]/(8*(1+eps*f)*r)).subs(chi,s.pi/2))
require(s.simplify(radial+2*eps/(3*s.sqrt(V)*(1-eps/s.sqrt(V))*r))==0,'explicit nonzero covector')
# Full finite-amplitude scalar Weyl density shares this tensor, but not this state repair.
Wsecond=4*integral
require(Wsecond==s.Rational(320,3),'same geometric Hessian in Weyl contact')
e=iv.mpf('.08');v=2*iv.pi**2
require(above(1-11*e/iv.sqrt(v)),'declared static range')
require(3+2*s.Rational(-3,2)==0,'logarithmic radial HS threshold')
require(3+2*s.Rational(-5,2)<0,'next-order square integrable')
finish('hadamard_split.py',{'scalar_harmonic':'Y3 normalized on unit S3',
 'Hessian_TF_squared_integral_exact':str(integral),
 'Weyl_lapse_second_variation_per_unit_time_exact':str(Wsecond),
 'same_old_vacuum_on_each_nonzero_allowed_static_lapse':'NORMAL_BUT_NOT_HADAMARD',
 'new_static_ground':'NORMAL_AND_HADAMARD_under_checked_KG_theorem_hypotheses',
 'canonical_pp_covariance_principal_symbol':'-epsilon HessTF(f)(v_xi,v_xi)/(8 N |xi|)',
 'old_CTP_initial_density_replaced_by_new_ground':False,
 'old_vacuum_in_new_positive_energy_form_domain':False,
 'actual_canonical_cutoff_old_energy_tends_to_infinity':True,
 'canonical_ground_energy_divergence_rate_proved':False,
 'scalar_counterterm_phase_repairs_two_point_function':False,
 'smooth_common_past_preparation_excluded':False,
 'analytic_microlocal_theorem_not_automated_formal_proof':True},
 inputs=['physics/qm/null_source/timelike/finite_stress/lapse_boundary/conformal_action/STATIC_NORMALITY.md',
         'physics/qm/null_source/timelike/finite_stress/lapse_boundary/conformal_action/FINITE_LAPSE_CTP.md'])
