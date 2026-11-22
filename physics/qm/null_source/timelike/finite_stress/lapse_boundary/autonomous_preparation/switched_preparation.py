"""Actual first-Dyson spectral weights, endpoint criterion and explicit bump bounds."""
import sympy as s
from common import finish,require,iv,outward,above,below
P='physics/qm/null_source/timelike/finite_stress/lapse_boundary/autonomous_preparation/'
rr=s.symbols('r',integer=True,nonnegative=True)
n4=4+2*rr
co4=(rr+1)*(rr+2)**2*(rr+3)/12
require(s.expand(co4-n4*n4*(n4*n4-4)/192)==0,'quartic total-frequency coefficient')
n3=3+2*rr
require(s.expand((rr+1)*(rr+2)/2-(n3*n3-1)/8)==0,'cubic coefficient')
require(24*3+16*s.binomial(3,2)==120,'three-field Wick factor')
require(s.Rational(120,1)/16/16/192==s.Rational(5,2048),'quartic spatial/Wick/coupling normalization')
# Exact character products for low total frequencies, independent of the generating formula.
def multiply(left,right):
 out={}
 for (n,j),a in left.items():
  for (m,k),b in right.items():
   if n+m>16:continue
   for ell in range(abs(j-k),j+k+1,2):
    out[(n+m,ell)]=out.get((n+m,ell),0)+a*b
 return out
base={(k,k-1):1 for k in range(1,17)}
sq=multiply(base,base);cu=multiply(sq,base);qu=multiply(sq,sq)
for n in range(3,17):
 require(cu.get((n,0),0)==((n*n-1)//8 if n%2 else 0),'cubic character count')
 require(qu.get((n,0),0)==(n*n*(n*n-4)//192 if n%2==0 and n>=4 else 0),'quartic character count')
# Fixed bump derivative maximum, evaluated outward.
tau=iv.mpf('.1');g=iv.mpf('.1');lam=iv.mpf('.1');V0=2*iv.pi**2
fprime=iv.sqrt(36+21*iv.sqrt(3))*iv.exp(-(1+iv.sqrt(3))/2)/tau
require(below(fprime,22),'compact bump exact derivative maximum')
full_lower=tau**2*iv.exp(-iv.mpf(2)/3)*(g*g/(8*V0)*iv.cos(3*tau)**2+15*lam*lam/(32*V0**2)*iv.cos(4*tau)**2)
require(above(full_lower,'0.0000003'),'nonzero complete outgoing first vector')
active=lambda K:iv.mpf(K)**3/(10485760*V0**2)
require(above(active(176),'.0013') and above(active(1000),'.24'),'actual active-endpoint lower bounds')
y=(3+s.sqrt(3))/2
require(s.simplify(3/y+1/(y-1)-2)==0,'unique derivative stationary root')
require(s.simplify(4*y**3*(y-1)-(36+21*s.sqrt(3)))==0,'derivative amplitude simplification')
finish('switched_preparation.py',{
 'object':'free first-Dyson vector of AL/AM cubic plus Wick quartic comparison',
 'cubic_weight':'g^2*(n^2-1)/(64*V0), odd n>=3',
 'quartic_weight':'5*lambda^2*n^2*(n^2-4)/(2048*V0^2), even n>=4',
 'actual_constituent_K_full_cubic_sectors':'n<=K+2',
 'actual_constituent_K_full_quartic_sectors':'n<=K+3',
 'complete_C_infinity_compact_switch_all_free_energy_graph_limits':True,
 'constructed_normalized_free_comparison_state_Hadamard':True,
 'comparison_state_claimed_as_exact_interacting_preparation':False,
 'active_endpoint_squared_norm_lower':'5*lambda^2*abs(f(T))^2*K^3/(2^19*V0^2)',
 'active_endpoint_K_condition':'K>=max(8,4*A_T/abs(f(T))), A_T=abs(f_prime(T))+L1_past(f_second)',
 'quartic_endpoint_jet_graph_condition':'m>p+3/2',
 'pure_cubic_endpoint_jet_graph_condition':'m>p+1/2',
 'm2_endpoint_finite_free_mean_energy':False,
 'fixed_bump_tau':'.1','fixed_g':'.1','fixed_lambda':'.1',
 'bump_derivative_maximum_interval':outward(fprime),
 'complete_outgoing_first_vector_squared_norm_lower_interval':outward(full_lower),
 'active_center_T':'0','active_center_K_minimum':176,
 'active_center_squared_norm_lower_at_K176':outward(active(176)),
 'active_center_squared_norm_lower_at_K1000':outward(active(1000)),
 'cutoff_uniform_normalized_state_O_epsilon_squared_remainder_at_active_end':False,
 'normalized_active_first_vector_trace_norm_limit':False,
 'all_continuum_representations_or_nondifferentiable_limits_excluded':False,
 'higher_Dyson_remainder_or_interacting_unitary_constructed':False
},inputs=[P+'LOCAL_CTP.md',P+'local_ctp.json',P+'LOCAL_FORCING.md',P+'local_forcing.json',P+'LOCAL_BASIS.md',P+'local_basis.json'])
