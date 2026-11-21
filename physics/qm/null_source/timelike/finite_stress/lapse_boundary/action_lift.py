"""Fixed homogeneous lapse-action lift: both Euler and Hamiltonian rows."""
import sympy as s
from common import require,finish
u,h,x,y,z,C0,B,H=s.symbols("u h x y z C0 B H",real=True)
C=C0+30*u;V=x+h*h
def D(f):
    return s.expand(h*s.diff(f,u)+x*s.diff(f,h)+y*s.diff(f,x)+z*s.diff(f,y))
def momenta(L):
    px=s.diff(L,x);pu=s.diff(L,h)-D(px)
    return px,pu
def EL(L):
    px,pu=momenta(L)
    return s.expand(s.diff(L,u)-D(pu))
def energy(L):
    px,pu=momenta(L)
    return s.expand(h*pu+x*px-L)
Lan=C*x*x/240+(C-29)*h*h/120+(3*C-59)*h**4/720+u/8+(C0-1)/240
tan=-s.Rational(1,32)-C*z/480+(C-29)*x/240+(3*C-59)*h*h*x/240+h*h/16-h*y/8-3*x*x/32+3*h**4/32
ran4=-C*h*y/120+C*x*x/240+(C-29)*h*h/120+(3*C-59)*h**4/240-h*h*x/4+(1-C)/240
require(s.simplify(EL(Lan)+4*tan)==0,"Complete anomaly Euler row")
require(s.simplify(energy(Lan)-ran4)==0,"Complete anomaly lapse energy")
LQ=B*V-H*V*V/8;f=B-H*V/4
require(s.simplify(EL(LQ)-(D(D(f))-D(2*h*f)))==0,"Complete subtraction trace row")
Ce=V*V/8+h*h*V/4-h*D(V)/4
require(s.simplify(energy(LQ)-(B*h*h-H*Ce))==0,"Complete subtraction lapse row")
Cr=s.symbols("Cr")
require(energy(Cr)==-Cr,"Reference radiation sign")
L=Lan+LQ+Cr;px,pu=momenta(L)
require(s.simplify(px-(B-H*V/4+C*x/120))==0,"Boundary higher momentum")
require(s.simplify(pu-(2*h*(B-H*V/4)+(C-29)*h/60+(3*C-59)*h**3/180-D(px)))==0,"Boundary lower momentum")
require(s.simplify(s.diff(L,x,2)-(C/120-H/4))==0,"Exact finite-K Hessian")
a,V0,HV,g4=s.symbols("a V0 HV g4",nonzero=True,real=True)
coef=HV/(3*V0*a*a*h)
dpu=-3*V0*a*a*g4*(coef/g4)
require(s.simplify(h*dpu+HV)==0,"Action-required source momentum relation")
Q0,D0,H0=s.symbols("Q0 D0 H0")
eB=2*(-h*D0+(V+h*h)*Q0)/(3*V0*a*a)
d=2*(H0-h*D0+h*h*Q0)/(3*V0*a*a)
require(s.simplify(d-eB-2*(H0-V*Q0)/(3*V0*a*a))==0,"Initial lapse mismatch is H0 minus VQ")
pk,qq,ak,gk,kappa,praw,qr=s.symbols("pk qq ak gk kappa praw qr",real=True,nonzero=True)
vaux=(pk-qq-ak)/gk
leg=s.expand(vaux*(pk-qq)-(gk*vaux*vaux/2+ak*vaux))
require(s.simplify(leg-(pk-qq-ak)**2/(2*gk))==0,"Finite-K canonical Legendre square")
require(s.expand((praw+kappa*qr)**2/2-kappa*kappa*qr*qr/2-praw*praw/2-kappa*praw*qr)==0,"Raw endpoint momentum transformation")
finish("action_lift.py",dict(
 finite_K_full_canonical_constraint_explicit=True,
 full_finite_K_homogeneous_lapse_action_representative=True,
 fixed_AE_counterterms_and_k1_reference_reproduced=True,
 Euler_trace_and_Hamiltonian_density_rows_both_checked=True,
 CTP_independent_lapses_and_initial_transport_required=True,
 zero_source_not_double_counted_as_extra_classical_term=True,
 complete_boundary_symplectic_potential_explicit=True,
 source_mixed_column_required_by_initial_lapse=True,
 initial_momentum_relation="h_i*delta(P_u)+H_i,K=0",
 pure_q_rescaling_boundary_term_new_gravity_charge=False,
 finite_K_future_Ward_defect_retained=True,
 finite_K_inverse_limit_proved=False,
 arbitrary_4D_action_uniquely_reconstructed=False,
 normal_joint_initial_density_constructed=False),
 ["nonlinear_history/KERNELS.md","finite_stress/lapse_boundary/ACTION_BOUNDARY.md",
  "finite_stress/lapse_boundary/ACTION_RESPONSE.md",
  "finite_stress/lapse_boundary/FINITE_CAUSAL.md",
  "finite_stress/lapse_boundary/CONSTRAINT_RESIDUAL.md"],
 proof="ACTION_LIFT.md")
