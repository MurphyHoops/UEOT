"""Full target heat tensor benchmarks and exact quartic lapse contacts."""
import sympy as s
from common import finish,require
A,B,C,K=s.symbols('A B C K',real=True)
x,y,z,p,q,r=s.symbols('x y z p q r',real=True)
S=s.Matrix([[x,p,q],[p,y,r],[q,r,z]])
E=s.Matrix([[A*y+B*z,-A*p,-B*q],[-A*p,A*x+C*z,-C*r],[-B*q,-C*r,B*x+C*y]])
require((E.subs({A:K,B:K,C:K})-K*(s.trace(S)*s.eye(3)-S)).applyfunc(s.expand)==s.zeros(3),'constant curvature endomorphism')
v=s.Matrix(s.symbols('v1:4',real=True))
rankone={x:v[0]**2,y:v[1]**2,z:v[2]**2,p:v[0]*v[1],q:v[0]*v[2],r:v[1]*v[2]}
wedge=A*A*(x*y-p*p)+B*B*(x*z-q*q)+C*C*(y*z-r*r)
require(s.expand(wedge.subs(rankone,simultaneous=True))==0,'homogeneous connection-curvature wedges')
k,k1,k2,vp=s.symbols('k k1 k2 vp',real=True)
aa=-k2/(2*(1+k))+k1*k1/(4*(1+k)**2)
bb=k2/(2*(1-k))+k1*k1/(4*(1-k)**2)
cc=k1*k1/(4*(1-k*k))
# Original phi direction in the orthonormal +/- coframe.
jet={x:0,y:(1+k)*vp*vp/2,z:(1-k)*vp*vp/2,p:0,q:0,r:s.sqrt(1-k*k)*vp*vp/2}
jE=E.subs({A:aa,B:bb,C:cc}).subs(jet,simultaneous=True)
require(s.simplify(s.trace(jE*jE)-k1**4*vp**4/(8*(1-k*k)**2))==0,'actual phi witness recovered')
N,V=s.symbols('N V',positive=True);r1,r2,c1,c2,c3=s.symbols('r1 r2 c1 c2 c3',real=True)
F=lambda a,b:c1*a**4+c2*a*a*b*b+c3*b**4
L=N*V*F(r1/N,r2/N)
Fv=F(r1/N,r2/N)
require(s.simplify(s.diff(L,N)+3*V*Fv)==0,'quartic lapse row')
require(s.simplify(s.diff(L,N,2)-12*V*Fv/N)==0,'quartic NN contact')
for ri in [r1,r2]:
 require(s.simplify(s.diff(L,N,ri)+3*s.diff(L,ri)/N)==0,'quartic lapse velocity contact')
# First-order fixed-momentum stress in one active coordinate verifies factors.
a,g,c,vel0=s.symbols('a g c vel0',positive=True)
dvel=-4*c*vel0**3/(a*a*g)
drho=g*vel0*dvel/(a*a)+3*c*vel0**4/a**4
dp=g*vel0*dvel/(a*a)+c*vel0**4/a**4
require(s.simplify(drho+c*vel0**4/a**4)==0,'fixed-p density correction')
require(s.simplify(dp+3*c*vel0**4/a**4)==0,'fixed-p pressure correction')
finish('sigma_counterterms.py',{'flat_four_gradient_heat_tensor':'explicit in orthonormal coframe',
 'homogeneous_quartic_lapse_contacts_verified':True,
 'curvature_matter_and_boundary_terms_required':True,
 'finite_renormalized_coefficients_determined':False,
 'all_background_heat_quartic_positive_claimed':False,
 'first_order_Hamiltonian_used_as_exact_positive_operator':False},
 inputs=['physics/qm/null_source/timelike/finite_stress/lapse_boundary/conformal_action/SIGMA_UV_GATE.md'])
