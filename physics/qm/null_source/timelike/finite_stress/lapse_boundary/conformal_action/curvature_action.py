"""Independent finite-mode action, constraint and contact identities."""
import sympy as s
from common import finish,require
N,v,r,q,b,k,kap,ch,g,A,P,p=s.symbols('N v r q b k kap ch g A P p', nonzero=True)
Q=q*q/2
raw=r*r/2-b*kap*q*r+b*kap**2*Q-(k*k-b)*Q
bulk=r*r/2-(k*k-b)*Q+b*(ch+kap**2)*Q
checks={}
def zero(name,x):
    require(s.simplify(x)==0,name);checks[name]=True
zero('bulk_minus_endpoint_is_raw',bulk-b*(ch*Q+kap*q*r)-raw)
zero('curvature_action_difference',bulk-bulk.subs(b,1)+(1-b)*(ch+kap**2+1)*Q)
C=(P-A-b*Q)**2/(2*g)+(p*p+(k*k-b)*q*q)/2-b*kap*kap*Q
delta=((1-b)*2*(P-A)*Q+(b*b-1)*Q*Q)/(2*g)+(1-b)*(kap*kap+1)*Q
zero('linked_constraint_difference',C-C.subs(b,1)-delta)
rawC=s.expand(C.subs({P:P+b*Q,p:p+b*kap*q},simultaneous=True))
target=(P-A)**2/(2*g)+(p*p+(k*k-b)*q*q)/2+b*kap*q*p+(b*b-b)*kap*kap*Q
zero('canonical_endpoint_transport',rawC-target)
L=r*r/(2*N)-b*v*q*r/N+b*v*v*Q/N-N*(k*k-b)*Q
rows={
'N_N':(N,N,(r*r-2*b*v*q*r+2*b*v*v*Q)/N**3),
'N_v':(N,v,b*(q*r-2*v*Q)/N**2),
'v_v':(v,v,2*b*Q/N),
'N_r':(N,r,-(r-b*v*q)/N**2),
'v_r':(v,r,-b*q/N),
'r_r':(r,r,1/N)}
for name,(x,y,t) in rows.items():zero('contact_'+name,s.diff(L,x,y)-t)
zero('conformal_lapse_row',s.diff(L.subs(b,0),N)+r*r/(2*N*N)+k*k*Q)
zero('conformal_configuration_contact',s.diff(L.subs(b,0),N,2)-r*r/N**3)
zero('conformal_no_geometry_velocity',s.diff(L.subs(b,0),v))
zero('net_scalar_boundary',-kap*Q+(1-b)*kap*Q+b*kap*Q)
# Verify a mixed variation independently by finite-polynomial extraction.
eps,t=s.symbols('eps t')
aN,av,ar,aq,bN,bv,br,bq=s.symbols('aN av ar aq bN bv br bq')
xs=[N,v,r,q];aa=[aN,av,ar,aq];bb=[bN,bv,br,bq]
shift={x:x+eps*a+t*z for x,a,z in zip(xs,aa,bb)}
num=r*r/2-b*v*q*r+b*v*v*Q
pot=(k*k-b)*Q
dN=eps*aN+t*bN
inverse2=1/N-dN/N**2+dN**2/N**3
expanded=s.expand(num.subs(shift,simultaneous=True)*inverse2
                  -(N+dN)*pot.subs(shift,simultaneous=True))
coefficient=expanded.coeff(eps,1).coeff(t,1)
h=s.hessian(L,xs)
zero('full_mixed_hessian_polynomial_coefficient',
     coefficient-(s.Matrix(aa).T*h*s.Matrix(bb))[0])
finish('curvature_action.py',{'identities':checks,'finite_modes':'arbitrary by additivity',
 'xi_conformal':'1/6','beta_conformal':0,'changed_physical_model':True,
 'original_minimal_AE_mean_history_inherited':False,
 'quantum_boundary_renormalization_completed':False})
