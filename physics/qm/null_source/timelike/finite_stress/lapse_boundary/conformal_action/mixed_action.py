"""Exact retained-lapse mixed boundary, Ward, contacts and rank identities."""
import sympy as s
from common import finish,require
u,kap,ch,k3,k4,X,v,acc,jerk,c=s.symbols('u kap ch k3 k4 X v acc jerk c')
rr=s.Function('Ricc')(X)
J=rr*v*v;W=ch+kap*kap+1;L=-c*W*J
def D(f):
 return s.diff(f,u)*kap+s.diff(f,kap)*ch+s.diff(f,ch)*k3+s.diff(f,k3)*k4+s.diff(f,X)*v+s.diff(f,v)*acc+s.diff(f,acc)*jerk
Pk=s.diff(L,ch);Px=s.diff(L,v);Pu=s.diff(L,kap)-D(Pk)
E=kap*Pu+ch*Pk+v*Px-L
Eu=s.diff(L,u)-D(Pu);Ex=s.diff(L,X)-D(Px)
def zero(name,expr):require(s.simplify(expr)==0,name)
zero('mixed energy',E-c*(kap*D(J)-(2*ch+3*kap*kap+1)*J))
zero('off-shell Ward',D(E)+kap*Eu+v*Ex)
zero('endpoint transport',L-(-c*D(kap*J)+c*kap*D(J)-c*(kap*kap+1)*J))
zero('u Euler row',Eu-c*(2*ch*J+2*kap*D(J)-D(D(J))))
N,M,w,z,vel,BB=s.symbols('N M w z vel BB',nonzero=True)
density=-c*BB*((z+w*w)/N**3-w*M/N**4+1/N)
zero('NN contact',s.diff(density,N,2)+c*BB*(12*(z+w*w)/N**5-20*w*M/N**6+2/N**3))
zero('NNprime contact',s.diff(density,N,M)+4*c*BB*w/N**5)
zero('NprimeNprime contact',s.diff(density,M,2))
zero('Nu2 contact',s.diff(density,N,z)-3*c*BB/N**4)
# Complete interior Euler NN contact, including the lapse-derivative column.
Bp=s.symbols('Bp')
cross=s.diff(density,N,M)
dcross=s.diff(cross,BB)*Bp+s.diff(cross,w)*z+s.diff(cross,N)*M
Jraw=BB/N**2
DJraw=Bp/N**3-2*BB*M/N**4
kapraw=w/N;chiraw=z/N**2-w*M/N**3
zero('complete Euler NN contact',
     s.diff(density,N,2)-dcross-c/N*(4*kapraw*DJraw-(2+8*chiraw+12*kapraw**2)*Jraw))
# Extended endpoint columns must also be transported.
F=w*BB/N**3
zero('endpoint lapse derivative',s.diff(F,N)+3*F/N)
zero('endpoint NN contact',s.diff(F,N,2)-12*F/N**2)
alpha,beta,V0=s.symbols('alpha beta V0')
zero('Einstein tensor homogeneous cancellation',
 (-6*alpha*V0*(ch+kap*kap+1)*J-3*beta*V0*ch*J).subs(beta,-2*alpha)
 +6*alpha*V0*(kap*kap+1)*J)
# Independent lapse Euler derivative, using B'=DJ and N=1,N'=0.
Bp=s.symbols('Bp')
dNprime=s.diff(density,M)
total=s.diff(dNprime,BB)*Bp+s.diff(dNprime,w)*z+s.diff(dNprime,N)*M
lapserow=(s.diff(density,N)-total).subs({N:1,M:0})
zero('retained lapse versus energy',lapserow+c*(w*Bp-(2*z+3*w*w+1)*BB))
m11,m12,m13,m22,m23,m33,b1,b2,b3=s.symbols('m11 m12 m13 m22 m23 m33 b1 b2 b3')
MM=s.Matrix([[m11,m12,m13],[m12,m22,m23],[m13,m23,m33]]);b=s.Matrix([b1,b2,b3])
H=s.zeros(4);H[0,1:4]=b.T;H[1:4,0]=b;H[1:4,1:4]=MM
zero('Schur determinant',H.det()+(b.T*MM.adjugate()*b)[0])
# Noncommuting R derivative: old scalar connection really misses a term.
t=s.symbols('t',real=True);R=s.Matrix([[2,t],[t,3]]);Rp=s.diff(R,t);K=R*R
zero('matrix connection',(R*Rp-s.diff(K,t)/2-(R*Rp-Rp*R)/2).norm()**2)
require(R*Rp-Rp*R!=s.zeros(2),'nonzero connection commutator example')
finish('mixed_action.py',{'finite_boundary_identity_and_retained_lapse_verified':True,
 'mixed_row_contains_source':True,
 'independent_carrier_reinterpretation_valid':False,
 'nondegenerate_Hessian_scope':'exact finite representative, M>0 and b nonzero',
 'Schur_lifting_order':'alpha^2',
 'one_loop_forces_exact_ghost_or_degree_of_freedom_claimed':False,
 'unbounded_endpoint_quantum_phase_implemented':False,
 'normal_joint_state_and_full_field_limit_constructed':False,
 'noncommuting_connection_retained':True},
 inputs=['physics/qm/null_source/timelike/finite_stress/lapse_boundary/conformal_action/SIGMA_COUNTERTERMS.md',
         'physics/qm/null_source/timelike/finite_stress/lapse_boundary/conformal_action/SIGMA_UV_GATE.md'])
