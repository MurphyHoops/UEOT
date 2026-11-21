"""Covariant source response algebra and contact ledger checks."""
import sympy as s
from common import require,finish
xx=s.symbols("t x y z",real=True)
sg=[-1,1,1,1]
f=s.Function("f")(*xx)
hab=[[s.Function("h"+str(min(i,j))+str(max(i,j)))(*xx) for j in range(4)] for i in range(4)]
H=sum(sg[i]*hab[i][i] for i in range(4))
def box(expr):
    return sum(sg[i]*s.diff(expr,xx[i],2) for i in range(4))
dP=-sum(sg[i]*sg[j]*hab[i][j]*s.diff(f,xx[i],xx[j]) for i in range(4) for j in range(4))
dP-=sum((sum(sg[i]*sg[j]*s.diff(hab[i][j],xx[i]) for i in range(4))-sg[j]*s.diff(H,xx[j])/2)*s.diff(f,xx[j]) for j in range(4))
comm=H*box(f)/4-box(H*f)/4
target=-sum(sg[i]*sg[j]*s.diff(hab[i][j]*s.diff(f,xx[j]),xx[i]) for i in range(4) for j in range(4))-box(H)*f/4
require(s.expand(dP+comm-target)==0,"Half-density perturbation identity")
xi=[s.Function("xi"+str(i))(*xx) for i in range(4)]
div=sum(s.diff(xi[i],xx[i]) for i in range(4))
def K(expr):
    return sum(xi[i]*s.diff(expr,xx[i]) for i in range(4))+div*expr/2
hd=[[sg[j]*s.diff(xi[j],xx[i])+sg[i]*s.diff(xi[i],xx[j]) for j in range(4)] for i in range(4)]
Hg=sum(sg[i]*hd[i][i] for i in range(4))
Vg=-sum(sg[i]*sg[j]*s.diff(hd[i][j]*s.diff(f,xx[j]),xx[i]) for i in range(4) for j in range(4))-box(Hg)*f/4
require(s.expand(Vg-K(box(f))+box(K(f)))==0,"Diffeomorphism commutator")
require(s.simplify(Hg-2*div)==0,"Diffeomorphism trace")
require(s.Rational(4,2*(4+2))==s.Rational(1,3),"Four-dimensional conservation coefficient")
# Exact matrix derivative with arbitrary symmetric lower stress and metric variation.
g=s.diag(*sg)
hh=s.Matrix(4,4,lambda i,j:s.Symbol("b"+str(min(i,j))+str(max(i,j))))
T=s.Matrix(4,4,lambda i,j:s.Symbol("T"+str(min(i,j))+str(max(i,j))))
dT=s.Matrix(4,4,lambda i,j:s.Symbol("dT"+str(min(i,j))+str(max(i,j))))
trace=s.trace(g*hh)
invprime=-g*hh*g
matrix_derivative=trace*g*T*g/2+invprime*T*g+g*dT*g+g*T*invprime
expected=g*dT*g-(g*hh)*(g*T*g)-(g*T*g)*(hh*g)+trace*g*T*g/2
require(matrix_derivative==expected,"Raised-index and volume contacts")
S=s.Matrix(4,4,lambda i,j:s.Symbol("S"+str(min(i,j))+str(max(i,j))))
dS=s.Matrix(4,4,lambda i,j:s.Symbol("dS"+str(min(i,j))+str(max(i,j))))
dcl=dS-hh*s.trace(g*S)/2-g*(s.trace(invprime*S)+s.trace(g*dS))/2
ledger=dS-g*s.trace(g*dS)/2-hh*s.trace(g*S)/2+g*s.trace(g*hh*g*S)/2
require(dcl==ledger,"Contraction seagull")

# Homogeneous lapse/scale specialization of the same half-density map.
tt=xx[0];aa=s.Function("a")(tt);hh0=s.Function("h")(tt)
ww=s.Function("w")(tt);nu=s.Function("nu")(tt);ff=s.Function("phi")(tt)
lam=s.symbols("lambda",real=True)
def PP(expr):
    return -(s.diff(expr,tt,2)+2*hh0*s.diff(expr,tt)+lam*expr)/aa**2
deltaP=(2*(ww+nu)*(s.diff(ff,tt,2)+2*hh0*s.diff(ff,tt))
        -(2*s.diff(ww,tt)-s.diff(nu,tt))*s.diff(ff,tt)+2*ww*lam*ff)/aa**2
kk=2*ww+nu/2
lhs=deltaP+kk*PP(ff)-PP(kk*ff)
sw=ww+nu
rhs=(2*sw*s.diff(ff,tt,2)+(4*hh0*sw+2*s.diff(sw,tt))*s.diff(ff,tt)
     +(2*ww*lam+2*s.diff(ww,tt,2)+4*hh0*s.diff(ww,tt)
       +s.diff(nu,tt,2)/2+hh0*s.diff(nu,tt))*ff)/aa**2
require(s.expand(lhs-rhs)==0,"Actual lapse specialization")
e1,e2,w1,w2,n1,n2,rho,press=s.symbols("e1 e2 w1 w2 n1 n2 rho press")
scale=s.exp(2*(e1*w1+e2*w2));lapse=1+e1*n1+e2*n2
chain=s.diff(-rho*scale*lapse**2/2+3*press*scale/2,e1,e2).subs({e1:0,e2:0})
target=(-2*rho+6*press)*w1*w2-2*rho*(w1*n2+w2*n1)-rho*n1*n2
require(s.expand(chain-target)==0,"Second metric chain contact for linear lapse")

finish("covariant_response.py",dict(
 metric_variation="real compact smooth h_ab after common initial surface",
 fixed_measure_half_density_variation_exact=True,
 pure_diffeomorphism_commutator_exact=True,
 homogeneous_lapse_specialization_and_second_metric_chain_exact=True,
 retarded_two_leg_formula="delta_W_tilde=-GR*Vh*W-W*Vh*GA",
 physical_scalar_measure_endpoint="-((trh)(x)+(trh)(y))*W/4",
 spacetime_measure_identification_claimed_Fock_unitary=False,
 conservation_split_coefficient="-g_ab*(P_x+P_y)/6 for P=box",
 contraction_conservation_raised_index_volume_and_chain_contacts_retained=True,
 arbitrary_tensor_AE_reference_conversion_completed=False,
 new_Weyl_or_R2_coupling_selected=False,
 full_tensor_retarded_extension_completed=False),
 ["dynamic_seed/DYNAMICS.md","nonlinear_history/KERNELS.md",
  "finite_stress/lapse_boundary/ACTION_BOUNDARY.md",
  "finite_stress/lapse_boundary/TENSOR_NOISE.md",
  "finite_stress/lapse_boundary/RETARDED_RESPONSE.md"],
 proof="COVARIANT_RESPONSE.md")
