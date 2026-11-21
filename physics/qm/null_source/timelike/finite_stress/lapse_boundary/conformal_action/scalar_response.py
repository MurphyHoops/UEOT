"""Exact single-frequency matrix identities and actual m=3 cutoff moments."""
import sympy as s
from common import finish,require
n,z,L,w=s.symbols('n z L w',positive=True,real=True)
# z is an algebraic complex-frequency variable; conjugate only v(n), never z.
bn=(1-3*n*n/L)/(2*(L-3));bz=(1-3*z*z/L)/(2*(L-3))
v=s.Matrix([1,-s.I*n/L,bn])
exact=s.Matrix(3,3,lambda i,j:w*(s.conjugate(v[i])*v[j]/(n-z)+s.conjugate(v[j])*v[i]/(n+z)))
chi=2*w*n/(n*n-z*z);M1=2*w*n;M3=2*w*n**3
cross=bz*chi-3*M1/(2*L*(L-3))
target=s.Matrix([[chi,-s.I*z*chi/L,cross],
 [s.I*z*chi/L,(z*z*chi+M1)/L**2,s.I*z*cross/L],
 [cross,-s.I*z*cross/L,bz*bz*chi+(9*M3/L**2+(-6/L+9*z*z/L**2)*M1)/(4*(L-3)**2)]])
for i in range(3):
 for j in range(3):require(s.simplify(exact[i,j]-target[i,j])==0,'causal row '+str((i,j)))
K,j,C=s.symbols('K j C',integer=True,positive=True)
m1=2*C*(s.summation(2*j,(j,2,K-1))+s.Rational(2,3)*2*K)
m3=2*C*(s.summation((2*j)**3,(j,2,K-1))+s.Rational(2,3)*(2*K)**3)
require(s.simplify(m1-C*(2*K*K+s.Rational(2,3)*K-4))==0,'actual cutoff M1')
require(s.simplify(m3-C*(4*K**4+s.Rational(8,3)*K**3+4*K*K-16))==0,'actual cutoff M3')
# All finite spectral rows decay rather than retain spurious contact polynomials.
for item in target:
 require(s.limit(item,z,s.oo)==0,'large-frequency contact cancellation')
finish('scalar_response.py',{'exact_causal_matrix_rows':9,
 'moments_include_incomplete_edge_shell':True,
 'retarded_convention':'+i theta(t) commutator; Fourier exp(+izt)',
 'Hamiltonian_plus_source_expectation_response':'minus chi',
 'noise_and_response_independently_tunable':False,
 'primitive_metric_seagulls_included':False,
 'full_renormalized_CTP_Hessian_constructed':False},
 inputs=['physics/qm/null_source/timelike/finite_stress/lapse_boundary/conformal_action/SPATIAL_NOISE.md',
         'physics/qm/null_source/timelike/finite_stress/lapse_boundary/conformal_action/WEYL_RESPONSE.md'])
