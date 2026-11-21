"""Independent target-curvature and first-order Legendre identities."""
import sympy as s
from common import finish,require
x=s.symbols('chi',real=True);k=s.Function('k')(x)
G=s.Matrix([[1,0,0],[0,1,k],[0,k,1]]);Gi=G.inv()
def der(expr,i):return s.diff(expr,x) if i==0 else 0
Gamma=[[[s.simplify(sum(Gi[i,l]*(der(G[l,j],q)+der(G[l,q],j)-der(G[j,q],l))/2 for l in range(3))) for q in range(3)] for j in range(3)] for i in range(3)]
def riem(i,j,q,r):
 return s.simplify(der(Gamma[i][r][j],q)-der(Gamma[i][q][j],r)+sum(Gamma[i][q][m]*Gamma[m][r][j]-Gamma[i][r][m]*Gamma[m][q][j] for m in range(3)))
require(all(Gamma[i][1][1]==0 for i in range(3)),'phi affine background on shell')
J=s.Matrix(3,3,lambda i,j:riem(i,1,j,1))
aa=s.diff(k,x)**2/(4*(1-k*k))
require(s.simplify(s.trace(J*J)-2*aa*aa)==0,'Jacobi squared trace')
require(s.simplify(J.det())==0,'tangent zero eigenvalue')
require(s.simplify(s.trace(J)-2*aa)==0,'two transverse eigenvalues')
Jc=s.Matrix(3,3,lambda i,j:riem(i,0,j,0))
rp=-s.diff(k,x,2)/(2*(1+k))+s.diff(k,x)**2/(4*(1+k)**2)
rm=s.diff(k,x,2)/(2*(1-k))+s.diff(k,x)**2/(4*(1-k)**2)
require(s.simplify(s.trace(Jc*Jc)-rp*rp-rm*rm)==0,'controller tidal trace')
# Covariant derivative of constant-chi phi-background endomorphism.
A=s.Matrix(3,3,lambda i,j:Gamma[i][1][j])
require(s.simplify(A*J-J*A)==s.zeros(3),'constant background endomorphism')
V,a,c,pp,ps,kk,eps=s.symbols('V a c pp ps kk eps',nonzero=True)
v0=(pp-kk*ps)/(V*a*a*(1-kk*kk))
w0=(ps-kk*pp)/(V*a*a*(1-kk*kk))
dv,dw=s.symbols('dv dw');v=v0+eps*dv;w=w0+eps*dw
L=V*a*a*(v*v+w*w+2*kk*v*w)/2+eps*V*c*v**4
H=pp*v+ps*w-L
corr=s.expand(H).coeff(eps,1)
require(s.simplify(corr+V*c*v0**4)==0,'first-order Legendre correction')
ss,astar,Cq,Pp,Ps=s.symbols('ss astar Cq Pp Ps',nonzero=True)
scaled=s.factor((-c*(pp-kk*ps)**4/(V**3*a**8*(1-kk*kk)**4)).subs({c:Cq*ss**4,pp:ss*Pp,ps:ss*Ps},simultaneous=True)).subs(ss**8,V**4*astar**8)
target=-V*Cq*(astar/a)**8*((Pp-kk*Ps)/(1-kk*kk))**4
require(s.simplify(scaled-target)==0,'fixed-coordinate scaling')
finish('sigma_uv_gate.py',{'exact_curvature_and_Legendre_checks':True,
 'spacetime_dimension':4,'target_dimension':3,
 'heat_a4_density':'k_c_prime^4 v^4/[16 (1-k_c^2)^2 (4pi)^2]',
 'new_four_derivative_matter_input_required':True,
 'unchanged_full_QFT_promotion_rejected':True,
 'bare_homogeneous_theorem_invalidated':False,
 'full_counterterm_basis_or_UV_completion_constructed':False},
 inputs=['physics/qm/null_source/timelike/total_source/FIELDSPACE.md',
         'physics/qm/null_source/timelike/total_source/AUTONOMOUS.md',
         'physics/qm/null_source/timelike/finite_stress/lapse_boundary/conformal_action/LOCAL_AUTONOMOUS.md'])
