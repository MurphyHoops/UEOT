"""Raw finite-mode local positivity and exact Gaussian preparation obstructions."""
import sympy as s
from common import finish,require,iv,outward,above
P='physics/qm/null_source/timelike/finite_stress/lapse_boundary/autonomous_preparation/'
r=s.symbols('r',nonnegative=True);K=s.symbols('K',integer=True,positive=True)
minimum=s.simplify((r*r/80-r/(30*s.sqrt(3))).subs(r,4/(3*s.sqrt(3))))
require(minimum==-s.Rational(1,135),'quartic split minimum')
require(s.Rational(1,2)-s.Rational(1,135)==s.Rational(133,270),'coercive quadratic coefficient')
V0=s.symbols('V0',positive=True);sig2=K*(K+1)/(4*V0)
lam=s.Rational(1,10);gg=s.Rational(1,10);J3,J4=s.symbols('J3 J4',nonnegative=True)
Omean=K*(K+1)/8;Ovar=K/8
cov=5*lam*sig2*K/8
hvar=gg*gg*J3+15*lam*lam*J4/2+75*lam*lam*sig2**2*K/8
require(s.simplify(cov-K*K*(K+1)/(64*V0))==0,'actual mixed block')
residual=s.simplify(hvar-cov*cov/Ovar)
require(s.simplify(residual-(gg*gg*J3+15*lam*lam*J4/2+25*lam*lam*sig2**2*K/4))==0,'strict Schur complement')
raw_lower=75*lam*lam*sig2**2*K/8
require(s.simplify(raw_lower-3*K**3*(K+1)**2/(512*V0**2))==0,'raw variance growth')
wick_lower=15*lam*lam*K*K/(32*V0**2)
require(s.simplify(wick_lower-3*K*K/(640*V0**2))==0,'quartic-chaos variance growth')
require(s.simplify(cov-(5*lam/2)*sig2*(K/4))==0,'quadratic counterterm cancels raw mixed block')
# Gaussian moments via independent normal coordinates: verify Wick polynomial and cross covariance.
t,v=s.symbols('t v')
moment=lambda n: s.Integer(0) if n%2 else s.factorial2(n-1) if n else s.Integer(1)
xs=s.symbols('x0:3');ys=s.symbols('y0:3');sigma,c=s.symbols('sigma c',real=True)
# Use a bivariate Gaussian Wick recursion for one species, variance a and cross covariance c.
aa=s.symbols('a',positive=True)
cache={(0,0):s.Integer(1)}
def bm(i,j):
 if i<0 or j<0:return s.Integer(0)
 if (i,j) in cache:return cache[(i,j)]
 if (i+j)%2:return s.Integer(0)
 if i:
  z=(i-1)*aa*bm(i-2,j)+j*c*bm(i-1,j-1)
 else:z=(j-1)*aa*bm(0,j-2)
 cache[(i,j)]=s.expand(z);return cache[(i,j)]
def em(poly):
 ans=0
 for powers,coef in s.Poly(s.expand(poly),*(xs+ys)).terms():
  ans+=coef*s.prod(bm(powers[i],powers[i+3]) for i in range(3))
 return s.expand(ans)
Rx=sum(z*z for z in xs);Ry=sum(z*z for z in ys)
require(s.expand(em(Rx**2*ys[0]**2)-em(Rx**2)*aa-20*aa*c*c)==0,'quartic/quadratic Gaussian contraction')
require(s.expand(em(Rx**2*Ry**2)-em(Rx**2)*em(Ry**2)-120*c**4-600*aa*aa*c*c)==0,'quartic covariance contraction')
require(em(Rx**2)==15*aa*aa,'raw quartic mean')
require(em((Rx**2-10*aa*Rx+15*aa*aa)*ys[0]**2)==0,'Wick quartic/quad orthogonality')
n=s.symbols('n',positive=True)
require(s.limit((-s.Rational(1,4)*n*n*s.log(1+s.Rational(1,4)/n**2)),n,s.oo)==-s.Rational(1,16),'sharp mass pulse exponential coefficient at s=1')
v0=2*iv.pi**2
tail_exponent=iv.mpf(100)/(16*(1+iv.mpf(1)/(4*101**2)))
tail_distance=2-2*iv.exp(-tail_exponent)
require(above(tail_distance,'1.996'),'finite nested mass-kick separation')
require(s.simplify(s.Rational(15,2)*lam**2*s.pi*K*(K+1)**4/(12288*V0**3)-s.pi*K*(K+1)**4/(163840*V0**3))==0,'four-particle K5 lower bound')
finish('local_ctp.py',{
 'model':'AL stable raw local polynomial with g=alpha=beta=kappa=eta=.1 and ESU effective masses one',
 'finite_real_mode_dimension':'K*(K+1)*(2*K+1)/2',
 'finite_mode_Hilbert_space_infinite_dimensional':True,
 'potential_lower_bound':'R_field^4/80+(133/270)*R_field^2',
 'fixed_K_Friedrichs_self_adjoint_and_compact_resolvent':True,
 'fixed_K_Gaussian_in_all_H_power_domains':True,
 'same_normal_density_CTP_Gram_positive':True,
 'arbitrary_normal_state_unbounded_derivatives_claimed':False,
 'mass_port_mean':str(Omean),'mass_port_variance':str(Ovar),
 'raw_initial_H_mass_covariance':'K^2*(K+1)/(64*V0)',
 'raw_H_variance_lower':'3*K^3*(K+1)^2/(512*V0^2)',
 'raw_covariance_matrix_strictly_positive':True,
 'raw_full_vacuum_energy':'3*K^2*(K+1)^2/8+3*K^2*(K+1)^2/(128*V0)',
 'Wick_quartic_changes_the_generator_not_just_scalar':'R^4-10*sigma_K^2*R^2+15*sigma_K^4',
 'Wick_initial_H_mass_covariance':'0',
 'fixed_quartic_Wick_variance_lower':'3*K^2/(640*V0^2)',
 'stronger_fixed_quartic_Wick_variance_lower':'pi*K*(K+1)^4/(163840*V0^3)',
 'K_squared_Wick_lower_coefficient_interval':outward(3/(640*v0**2)),
 'fixed_free_vacuum_graph_recovery_with_scalar_or_quadratic_counterterms':False,
 'sharp_mass_pulse_overlap_log_leading':'-s^2*K/16',
 'nested_K100_K200_s1_phase_adjusted_squared_distance_lower_interval':outward(tail_distance),
 'sharp_mass_pulse_same_interacting_energy_increment':'s^2*K*(K+1)/8',
 'free_smooth_mass_port_variance':'(1/8)*sum_k abs(g_hat(2*k))^2',
 'sharp_mass_pulse_phase_adjusted_cutoff_vectors_strong_Cauchy':False,
 'smooth_source_history_or_other_preparation_excluded':False,
 'full_local_diffeomorphism_Ward_at_spatial_mode_cutoff_claimed':False,
 'positive_normal_interacting_continuum_constructed':False
},inputs=[P+'LOCAL_BASIS.md',P+'local_basis.json',P+'LOCAL_FORCING.md',P+'local_forcing.json'])
