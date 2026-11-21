"""Signs and exact leading terms for the two negative-energy witnesses."""
import sympy as s
from common import finish,require
n,eps,R,m1,m2,m3=s.symbols('n eps R m1 m2 m3',positive=True)
lam=n/240+eps
d3=n/720-lam/2
require(s.simplify(d3+n/1440+eps/2)==0,'positive-g cubic sign')
poly=d3*(R**3+3*R**2*m1+3*R*m2+m3)
require(s.expand(poly).coeff(R,3)==-n/1440-eps/2,'translated packet leading coefficient')
alpha_negative=-1/(2*eps)
require(s.diff(alpha_negative*s.Symbol('j')**2,s.Symbol('j'),2)==-1/eps,'negative principal coefficient')
finish('energy_stability.py',{
 'negative_g_witness':'alpha n^2 integral |f|^2/kappa + constant -> -infinity',
 'positive_g_witness':'d3 R^3+O(R^2), d3<-n_s/1440',
 'all_nondegenerate_lambda_have_unbounded_below_u_generator':True,
 'complete_four_dimensional_ghost_theorem':False,
 'critical_lambda_requires_new_reduction':True})
