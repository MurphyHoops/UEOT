"""Complete symmetric scalar potential, exact heat polynomial and UV-scope gate."""
import sympy as s
from common import finish,require,iv,outward
P='physics/qm/null_source/timelike/finite_stress/lapse_boundary/autonomous_preparation/'
x,p,q,a,b,g,alpha,beta,kappa,eta=s.symbols('x p q a b g alpha beta kappa eta',real=True)
S=p*p+q*q
V=a*x*x/2+b*S/2+g*x*p*q+alpha*x**4/4+beta*(p**4+q**4)/4+kappa*p*p*q*q/2+eta*x*x*S/2
M=s.hessian(V,(x,p,q))
coefs={
 'constant':a*a/2+b*b,
 'chi_squared':3*a*alpha+2*b*eta+g*g,
 'source_probe_squared':a*eta+b*(3*beta+kappa)+g*g,
 'cubic':4*g*(2*eta+kappa),
 'chi_fourth':9*alpha*alpha/2+eta*eta,
 'source_probe_fourth':(eta*eta+9*beta*beta+kappa*kappa)/2,
 'source_probe_mixed':eta*eta+6*beta*kappa+4*kappa*kappa,
 'chi_source_probe_mixed':eta*(3*alpha+3*beta+kappa+4*eta)
}
monomials=[1,x*x,S,x*p*q,x**4,p**4+q**4,p*p*q*q,x*x*S]
expected=sum(c*m for c,m in zip(coefs.values(),monomials))
require(s.expand(s.trace(M*M)/2-expected)==0,'complete Hessian coefficient table')
require(s.expand(s.trace(M)-(a+2*b+(3*alpha+2*eta)*x*x+(eta+3*beta+kappa)*S))==0,'trace total derivative')
# Enumerate monomial orbits exactly under the declared finite symmetry.
allowed=[]
for i in range(5):
 for j in range(5-i):
  for k in range(5-i-j):
   if i%2==j%2==k%2:allowed.append((i,j,k))
orbits={tuple(sorted({z,(z[0],z[2],z[1])})) for z in allowed}
require(len(orbits)==8,'complete degree<=4 invariant potential basis')
for signs in [(-1,-1,1),(-1,1,-1),(1,-1,-1)]:
 require(s.expand(V.subs({x:signs[0]*x,p:signs[1]*p,q:signs[2]*q},simultaneous=True)-V)==0,'pair-flip symmetry')
require(s.expand(V.subs({p:q,q:p},simultaneous=True)-V)==0,'exchange symmetry')
beta_alpha=s.expand(4*coefs['chi_fourth'])
require(beta_alpha==18*alpha**2+4*eta**2,'one-loop normalization')
beta_beta=2*(eta**2+9*beta**2+kappa**2)
beta_kappa=2*(eta**2+6*beta*kappa+4*kappa**2)
beta_eta=2*eta*(3*alpha+3*beta+kappa+4*eta)
require(s.expand(beta_beta+beta_kappa-2*(2*eta**2+(3*beta+kappa)**2+4*kappa**2))==0,'formal stability cone derivative')
ll=s.symbols('lambda',real=True)
for bv in [beta_alpha,beta_beta,beta_kappa,beta_eta]:
 require(s.expand(bv.subs({alpha:ll,beta:ll,kappa:ll,eta:ll})-22*ll**2)==0,'isotropic quartic normalization')
alpha0=iv.mpf('.1');alphaw=iv.mpf('.2')
exitlog=16*iv.pi**2/18*(1/alpha0-1/alphaw)
c3,c4,z=s.symbols('c3 c4 z',positive=True)
zmax=3*c3/c4
require(s.simplify((c3*z**3-c4*z**4/4).subs(z,zmax)-27*c3**4/(4*c4**3))==0,'cubic Young maximum')
finish('local_basis.py',{
 'model':'new local three-scalar polynomial candidate',
 'independent_potential_orbits':8,
 'symmetry':['simultaneous sign reversal of any two fields','phi/psi exchange'],
 'half_trace_Hessian_squared_coefficients':{k:str(s.expand(v)) for k,v in coefs.items()},
 'one_loop_potential_basis_closed':True,
 'formal_one_loop_raw_stability_cone_forward_invariant':True,
 'complete_curved_action_requires_kinetic_nonminimal_gravity_boundary_terms':True,
 'raw_classical_stability_region':'alpha>0,beta>0,kappa>-beta,eta>=0',
 'one_loop_beta_alpha':'(18*alpha^2+4*eta^2)/(16*pi^2)',
 'example_alpha0':'.1','example_declared_alpha_threshold':'.2',
 'formal_one_loop_threshold_logscale_upper_interval':outward(exitlog),
 'formal_one_loop_UV_pole_used_as_nonperturbative_no_go':False,
 'R_squared_inhomogeneous_lapse_Hessian':'8*gamma_R*Delta_h^2',
 'homogeneous_lapse_Hessian_for_this_term':'0',
 'R_squared_coefficient_forced_nonzero_for_all_conformal_fields':False,
 'local_response_contact_identified_as_stochastic_noise':False,
 'positive_normal_interacting_continuum_constructed':False
},inputs=[P+'LOCAL_COUNTERTERMS.md',P+'local_counterterms.json'])
