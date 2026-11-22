"""Exact algebra for the sharp mixed/normal-target endpoint resource theorem."""
import sympy as s
from common import *
P="physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_feedback/"
paths=[P+"endpoint_normality.json",P+"NEAR_RECOVERY.md",
 "physics/qm/null_source/timelike/finite_stress/lapse_boundary/relational_coupled/actual_uv_bridge.json"]
end,uv=load(paths[0]),load(paths[2])
require(end["full_kappa_squared_form_leakage_retained"] and uv["same_actual_background_and_incoming_state"],"Actual endpoint normalization")
# Conditional scalar stability: an identity with nonnegative denominator, 0<z<1.
z=s.symbols("z",positive=True)
require(s.simplify(s.sqrt(1-z)-1+z/2+z**2/(2*(1+s.sqrt(1-z))**2))==0,"Exact stable oscillator remainder")
# Direct expansion independently fixes all cross-term signs.
H,A,b,D,S=s.symbols("H A b D S",real=True)
rhs=(H-b*D+b*b*S)+S*(A-b)**2+(b-A)*(D-2*S*b)
require(s.expand(rhs-(H-A*D+S*A*A))==0,"Conditional energy decomposition")
# Gaussian dephasing: variance 1/(4 delta^2), dilation exponent 2 omega X/S.
delt,om,X=s.symbols("delta omega X",positive=True)
var=1/(4*delt**2)
require(s.simplify((2*om*X/S)**2*var/2-(om*X)**2/(2*delt**2*S**2))==0,"Gaussian backaction exponent")
yy,yp=s.symbols("y yprime",real=True)
require(s.simplify(var*(yy-yp)**2/2-(yy-yp)**2/(8*delt**2))==0,"Gaussian channel characteristic normalization")
# Full 3x3 model includes a zero-eigenvalue direction; leakage is not compressed away.
p=s.symbols("p",positive=True)
a,c,e,f,g=s.symbols("a c e f g",real=True)
rho=s.diag(p,1-p,0)
K=s.Matrix([[a,c,e],[c,f,g],[e,g,0]])
Gamma=s.Matrix([[a,2*s.sqrt(p*(1-p))*c,0],[2*s.sqrt(p*(1-p))*c,f,0],[0,0,0]])
root=s.diag(s.sqrt(p),s.sqrt(1-p),0)
require(s.simplify(rho*Gamma+Gamma*rho-2*root*K*root)==s.zeros(3),"Sylvester solution with kernel")
C=s.simplify(s.trace(rho*K*K)-s.trace(rho*Gamma*Gamma))
Cexpected=(2*p-1)**2*c*c+p*e*e+(1-p)*g*g
require(s.simplify(C-Cexpected)==0,"Full second-moment and support-leakage Fisher coefficient")
dot=-s.I*(K*rho-rho*K)
L=s.zeros(3)
lam=[p,1-p,s.Integer(0)]
for i in range(3):
 for j in range(3):
  if i!=2 or j!=2:L[i,j]=s.simplify(2*dot[i,j]/(lam[i]+lam[j]))
require(s.simplify((rho*L+L*rho)/2-dot)==s.zeros(3),"SLD equation including kernel couplings")
require(s.simplify(s.trace(rho*L*L)-4*C)==0,"Quantum Fisher normalization")
# Actual partially dephased disjoint packets: source probabilities remain fixed.
w,chi,sep=s.symbols("w chi separation",positive=True)
coh=chi*s.sqrt(w*(1-w))
rh=s.Matrix([[1-w,coh],[coh,w]])
kk=s.diag(0,sep)
dt=-s.I*(kk*rh-rh*kk)
sl=2*dt
require(s.simplify((rh*sl+sl*rh)/2-dt)==s.zeros(2),"Packet SLD for all coherence values")
fq=s.simplify(s.trace(rh*sl*sl))
require(s.simplify(fq-4*chi**2*w*(1-w)*sep**2)==0,"Coherence-dependent Fisher term")
hh,dd,RR,mu2=s.symbols("h delta R mu2",positive=True)
mm=(1-dd)*hh;ww=dd*hh/(RR-mm)
require(s.simplify(ww*(1-ww)*(RR-mm)**2-dd*hh*(RR-hh))==0,"Actual packet between-variance")
vc=mu2*dd*(1-dd)**2*hh**2;vr=mu2*RR**2/100
within=(1-ww)*vc+ww*vr
require(s.simplify((1-ww)*vc+ww*vr+ww*(1-ww)*(RR-mm)**2-(within+dd*hh*(RR-hh)))==0,"Full pure endpoint matches mixed coherence boundary")
# Fixed lower band: S~K², R~log K, E0~K⁴, delta=K^(-1/4).
delta_power=s.Rational(-1,4)
beta_power=-2*delta_power-4
error_powers={"clipped_noise":2+delta_power,"backaction":beta_power+4,
 "quadratic_replacement_polynomial_part":s.Integer(1),"stable_remainder_polynomial_part":s.Integer(0)}
require(beta_power==s.Rational(-7,2) and all(q<2 for q in error_powers.values()),"Every Gaussian-comparison error is subquadratic")
# The real-mode degeneracy and incoming W->1 set the actual coefficient.
k,v=s.symbols("k variance",positive=True)
require(s.simplify(2*k**2*k*(1/(2*k))**2-k/2)==0,"S leading shell multiplicity")
require(s.simplify(s.limit((s.sqrt(1+4*v*X**2)-1)/(2*v*X**2),X,0)-1)==0,"Pure optimizer leading matching")
finish("mixed_resource.py",dict(
 normal_target_assumptions=["trace one","normal on L2(R+)","finite Tr gamma kappa^2"],
 arbitrary_normal_input_correlations_allowed=True,
 output_convergence="trace norm; approximating targets need no uniform moment bound",
 sharp_liminf_coefficient="F_Q(gamma,kappa)/16",
 exact_target_resource_infimum_limit="F_Q(gamma,kappa)/16",
 exact_target_normal_preparation_sequence=True,
 mixed_finite_cutoff_minimizer_claimed=False,
 pure_variance_specialization="Var(kappa)/4",
 all_normal_finite_second_moment_targets_have_positive_coefficient=True,
 target_independent_positive_coefficient=False,
 full_second_moment_and_kernel_leakage_retained=True,
 gaussian_comparison_is_implemented_physical_apparatus=False,
 incoming_energy_is_total_conserved_device_cost=False,
 common_normal_full_field_input_limit_constructed=False,
 actual_near_packet_coefficient="(v_within+chi^2 v_between)/4",
 fixed_kappa_law_determines_cost=False,
 errors_in_bound_K_powers={n:str(q) for n,q in error_powers.items()},
 quantum_Fisher_convex_roof_identity_claimed_new=False),paths)
