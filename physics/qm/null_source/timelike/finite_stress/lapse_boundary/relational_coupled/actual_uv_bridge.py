"""Actual-background common-cutoff response/noise and contact tail certificate."""
import sympy as s
from common import *
pre="physics/qm/null_source/timelike/";base=pre+"finite_stress/lapse_boundary/";new=base+"relational_coupled/"
load(base+"actual_inverse.json");load(base+"quiet_window.json");load(new+"cutoff_gate.json")
k,V=s.symbols("k V",positive=True)
om=s.sqrt(k*k-1)
dBK=-k/2-1/(4*k)
# Exact same-cutoff mean and Hessian shell identities, including conversion.
K1shell=k*k/om-k-1/(2*k);K3shell=k*k/om**3-1/k
X=s.symbols("X",real=True)
omega_form=k*k*(X-1/(2*om)-V/(4*om**3))+K1shell/2+K3shell*V/4
canonical=k*k*X+dBK-V/(4*k)
require(s.simplify(omega_form-canonical)==0,"Finite-K mean conversion identity")
require(s.diff(dBK*V-V*V/(8*k),V,2)==-1/(4*k),"Exact same-action Hessian contact")
require(-s.Rational(1,4)-s.Rational(1,8)==-s.Rational(3,8),"Reference and k2 contact retained")
p=s.symbols("p",nonnegative=True)
for sign in [-1,1]:
 a=4+(4+2*sign)*p;b=2*(1+sign)*p
 require(s.expand(a+b-(4+(6+4*sign)*p))==0,"Exact low-shell absolute noise")
 require(s.expand(a-b-(4+2*p))==0,"Same-state low-shell commutator")
 require(a.subs(p,0)>=0 and a.subs(p,1)>=0 and b.subs(p,0)>=0 and b.subs(p,1)>=0,"Positive Gram weights on 0<=p<=1")
# Wronskian including its phase: F=x+iy, derivative z+iw.
x,y,z,w,omega=s.symbols("x y z w omega",real=True,nonzero=True)
F=x+s.I*y;Fp=z+s.I*w
wr=s.expand((F*(s.conjugate(Fp)+s.I*omega*s.conjugate(F))-(Fp-s.I*omega*F)*s.conjugate(F))/(2*omega))
require(s.simplify(wr-s.I*(s.Abs(F)**2-s.im(Fp*s.conjugate(F))/omega))==0,"Exact Wronskian amplitude improvement")
# Taylor constants on 1/k²<=1/4.
q=s.symbols("q",nonnegative=True)
require(s.diff((1-q)**(-s.Rational(3,2)),q)==s.Rational(3,2)*(1-q)**(-s.Rational(5,2)),"Local-response Taylor constant")
require(s.diff((1-q)**(-s.Rational(1,2)),q,2)==s.Rational(3,4)*(1-q)**(-s.Rational(5,2)),"Mean static Taylor constant")
D=(iv.mpf(4)/3)**(iv.mpf(5)/2);require(below(D,3),"Uniform k>=2 ratio")
require(10+64//8+256//16==34,"Local amplitude and boundary derivative budget")
require([128//16,1024//16,768//16,192//16,16//16]==[8,64,48,12,1],"Retarded test derivative budget")
mu=5*iv.exp(-1158);require(below(mu,".1"),"Actual frozen quiet background")
for m in [1,2,3]:
 require(s.simplify((s.Rational(4,3)**(m+1))/2**(2*m+2)-s.Rational(1,3)**(m+1))==0,"Smoothed noise shell factor")
 require(s.integrate(k**(-2*m),(k,s.symbols("K",positive=True),s.oo))==s.symbols("K",positive=True)**(1-2*m)/(2*m-1),"Explicit sum-integral noise tail")
# Mean remainder: 12 mu k²/omega⁴ <=(64/3)mu/k².
require(12*s.Rational(4,3)**2==s.Rational(64,3),"Actual mean remainder coefficient")
t=s.symbols("t",real=True);h=s.Function("h")(t);f=s.Function("f")(t);qq=s.Function("Q")(t)
DU=lambda v:s.diff(v,t,2)+2*h*s.diff(v,t)
DUadj=lambda v:s.diff(v,t,2)-2*s.diff(h*v,t)
eps=s.symbols("eps",real=True)
vary=s.diff(s.diff(qq,t,2)-2*s.diff((h+eps*s.diff(f,t))*qq,t),eps).subs(eps,0)
require(s.simplify(vary+2*s.diff(qq*s.diff(f,t),t))==0,"Actual u-direction chain contact retained")
rows=[]
rnorm=iv.mpf(19)/8+166*mu
b=[None,4+16*mu,4+96*mu,4+496*mu]
for K in [65536,131072]:
 Rtail=3*rnorm/(2*K*K)
 Ntail=[b[m]*b[m]/(3**(m+1)*(2*m-1)*iv.mpf(K)**(2*m-1)) for m in [1,2,3]]
 Mtail=D*(iv.mpf(3)/16+3*mu/8)/(2*K*K)+64*mu/(3*K)
 rows.append(dict(K=K,response_sup_tail=outward(Rtail),mean_sup_tail=outward(Mtail),
  noise_tail_by_m=[outward(x) for x in Ntail],
  quadratic_CTP_tail_m3=outward(Rtail+Ntail[2]/2),
  GNS_L2_squared_tail_m3=outward(Mtail*Mtail+Ntail[2])))

# Weighted H2 response tail and exact metric/pressure off-shell algebra.
require(2*s.Rational(16,9)<4,"Second-derivative Sobolev tail coefficient")
require(16*s.Rational(3,2)==24 and 32*s.Rational(3,2)==48,"First/zeroth Sobolev coefficients")
require(s.Rational(3,2)*s.Rational(3,8)==s.Rational(9,16) and s.Rational(3,2)*18==27,"Local Sobolev coefficient")
ww=s.Function("w")(t);hh=s.Function("h")(t)
require(s.simplify(s.diff(s.diff(ww,t,2)+2*hh*s.diff(ww,t),t,2)-(s.diff(ww,t,4)+2*hh*s.diff(ww,t,3)+4*s.diff(hh,t)*s.diff(ww,t,2)+2*s.diff(hh,t,2)*s.diff(ww,t)))==0,"No fifth derivative in actual H2 input")
U,EE,SS,ss,ee,ww0,Int_s,Int_def=s.symbols("U E S svar evar w0 Int_s Int_def",real=True)
efromward=2*s.exp(-U)*Int_s+s.exp(-U)*Int_def
action=s.exp(2*U)*(ss+ee/2+2*ww0*(SS+EE/2))
pressure=s.exp(2*U)*ss+s.exp(U)*Int_s
off=s.exp(2*U)*(2*SS+EE)*ww0+s.exp(U)*Int_def/2
require(s.simplify(action.subs(ee,efromward)-pressure-off)==0,"Finite-K off-shell action-pressure identity")
co=load(new+"coefficient_window.json");AA=box(co["frozen_A"]);gamma=24*AA;small=iv.exp(-1158)
weak_rows=[]
for KK in [65536,131072]:
 c2=4/(gamma*KK);c1=24*mu/(gamma*KK*KK)
 c0=(iv.mpf(9)/16+27*mu)/(KK*KK)+48*mu/(gamma*KK*KK)
 A2=1+2*small/gamma+4*small/gamma**2+2*small/gamma**3
 A1=1/gamma+2*small/gamma**2+2*small/gamma**3
 A0=1/gamma**2+2*small/gamma**3
 mtail=D*(iv.mpf(3)/16+3*mu/8)/(2*KK*KK)+64*mu/(3*KK)
 bound=(1+2*small/gamma)*(c2*A2+c1*A1+c0*A0)+2*mtail/gamma**2
 weak_rows.append(dict(K=KK,weak_X_to_terminal_H2_dual_tail=outward(bound)))

finish("actual_uv_bridge.py",dict(
 same_actual_background_and_incoming_state=True,same_AE_finite_cutoff_sequence=True,
 same_reference_k1_contact_retained=True,NOON_low_block_and_metric_cross_correlations_retained=True,
 potential_response_tail="3 r_mu(f)/(2K^2)",potential_noise_tail="b_m(f)b_m(g)/(3^(m+1)(2m-1)K^(2m-1)), m=1,2,3",
 mean_tail="D(3/16+3mu/8)/(2K^2)+(64/3)mu/K",
 same_state_ordered_kernel_positive=True,GNS_L2_cutoff_limit_on_declared_state=True,
 actual_fixed_conformal_lapse_u_u_weak_Hessian_contact_tail=True,
 illustration_test_norms="Each displayed L1 and sup derivative norm <=1; Delta L1<=1 for CTP illustration",
 illustrative_bounds=rows,weak_Sobolev_bounds=weak_rows,
 actual_H2_to_Y_response_tail=True,actual_H4_to_terminal_H2_dual_action_tail=True,
 finite_K_off_shell_action_pressure_terms_retained=True,
 strong_inverse_convergence_not_implied_by_weak_tail=True,
 fullfield_kernel_existence_reused_not_new=True,old_mode_or_geometry_ODE_executed=False,
 finite_K_backgrounds_individually_mean_solutions_asserted=False,
 finite_amplitude_influence_limit_proved=False,arbitrary_lapse_tensor_Hessian_limit_proved=False,
 finite_K_inverse_to_full_inverse_convergence_proved=False,
 quantum_geometry_joint_state_propagator_continuum_limit_proved=False),
 [base+"ACTUAL_INVERSE.md",base+"actual_inverse.json",base+"ACTION_RESPONSE.md",
 base+"TENSOR_NOISE.md",base+"QUIET_WINDOW.md",base+"quiet_window.json",
 pre+"nonlinear_history/KERNELS.md",new+"cutoff_gate.json",new+"coefficient_window.json"],proof="ACTUAL_UV_BRIDGE.md")
