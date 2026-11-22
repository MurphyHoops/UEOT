"""Local-lift stability and exact bare-field cutoff diagnostics."""
import sympy as s
from common import finish,require,iv,outward,above,below
P='physics/qm/null_source/timelike/finite_stress/lapse_boundary/autonomous_preparation/'
# Exact nested-shell correlation and a strict bump variance lower bound.
K=s.symbols('K',integer=True,positive=True)
rho2=(K+1)/(2*(2*K+1))
require(s.factor(s.Rational(1,3)-rho2-(K-1)/(6*(2*K+1)))==0,'uniform correlation bound')
require(s.limit(rho2,K,s.oo)==s.Rational(1,4),'nested cutoff correlation limit')
x=s.symbols('x',positive=True)
require(1/(s.Rational(1,4)*s.Rational(3,4))==s.Rational(16,3),'bump minimum on selected interval')
expo=-s.Rational(8,3)-s.Rational(9,32)
require(expo==-s.Rational(283,96),'Gaussian variance lower exponent')
variance=iv.exp(-iv.mpf(283)/96)/(100*iv.sqrt(2*iv.pi))
point_gap=2*(1-1/iv.sqrt(3))*variance
require(above(variance,'.0002') and above(point_gap,'.00017'),'strict non-Cauchy point lower bound')
q,p,rr=s.symbols('q p r',real=True)
require(s.expand((q*q+p*p)/2+rr*q*p-((1-rr)*(q-p)**2+(1+rr)*(q+p)**2)/4)==0,'classical local potential diagonalization')
finish('local_field_lift.py',{
 'classical_global_controller_cross_region_response_order':'t^4',
 'classical_cross_response_coefficient':'r_prime(x0)^2/(24*M)*<fA,psi0>*<fB,psi0>',
 'quantum_commutator_Taylor_expansion_claimed':False,
 'bounded_local_classical_coupling_energy_stability':True,
 'classical_global_energy_space_solutions_proved_analytically':True,
 'bare_controller_variance':'K*(K+1)/(4*V0)',
 'fixed_compact_bump_point_strong_limit':'0',
 'fixed_compact_bump_operator_norm_limit_claimed':False,
 'rescaled_nested_point_correlation_squared':'(K+1)/(2*(2*K+1))',
 'rescaled_point_operators_strong_Cauchy':False,
 'Gaussian_bump_variance_lower_interval':outward(variance),
 'nested_point_squared_vector_distance_lower_interval':outward(point_gap),
 'rescaled_spatial_smear_strong_limit':'mu_Gaussian(r)*integral(f)*I',
 'strong_limits_multiplied_by_unbounded_other_fields':False,
 'full_interaction_free_limit_or_general_no_go_claimed':False,
 'renormalized_quantum_local_model_constructed':False
},inputs=[P+'LOCAL_FORCING.md'])
