"""Full homogeneous lapse matrix, anchored chain contact, and gauge identities."""
import sympy as s
from common import *
P="physics/qm/null_source/timelike/finite_stress/lapse_boundary/"
paths=[P+"tensor_noise.json",P+"retarded_response.json",
 P+"relational_coupled/actual_uv_bridge.json",P+"ACTION_BOUNDARY.md",
 P+"RETARDED_RESPONSE.md",P+"TENSOR_NOISE.md",
 P+"relational_coupled/ACTUAL_UV_BRIDGE.md",
 P+"joint_feedback/ADVANCED_CUTOFF.md",P+"joint_feedback/PREPARED_LIMIT.md"]
noise,ret,uv=[load(v) for v in paths[:3]]
require(noise["full_absolute_source_tensor_noise_explicit_bidistr"] and noise["zero_radial_fourth_and_zero_shell_cumulants_retained"],"Actual full source noise")
require(ret["actual_fixed_incoming_homogeneous_retarded_RSET_response_defined"] and uv["same_AE_finite_cutoff_sequence"],"Same mean action cutoff")
t=s.symbols("t",real=True);h=s.Function("h")(t);A=s.Function("A")(t)
f=s.Function("f")(t);g=s.Function("g")(t);w=s.Function("w")(t);z=s.Function("z")(t)
nu=s.diff(f,t);mu=s.diff(g,t)
B=h*(nu*g+mu*f)+s.diff(h,t)*f*g-s.diff(w,t)*g-s.diff(z,t)*f
gauge=s.expand(B.subs(w,h*f))
require(s.simplify(gauge+f*(s.diff(z,t)-h*mu))==0,"Anchored mixed gauge contact")
NN=A*(h*(nu*g+mu*f)+s.diff(h,t)*f*g)
require(s.simplify(NN+s.diff(A,t)*h*f*g-s.diff(A*h*f*g,t))==0,"NN contact integration by parts")
Rho,Pr,dr,dp,zz,mm,a4,V0=s.symbols("Rrho Rp dRrho dRp z mu a4 V0")
ep=s.symbols("eps")
u_expr=V0*a4*s.exp(4*ep*zz)*(1+ep*mm)*(3*(Pr+ep*dp)-(Rho+ep*dr))
n_expr=-V0*a4*s.exp(4*ep*zz)*(Rho+ep*dr)
require(s.simplify(s.diff(u_expr,ep).subs(ep,0)-V0*a4*(3*dp-dr+(mm+4*zz)*(3*Pr-Rho)))==0,"u row complete chain derivative")
require(s.simplify(s.diff(n_expr,ep).subs(ep,0)+V0*a4*(dr+4*zz*Rho))==0,"N row complete chain derivative")
L=s.Matrix([[-1,3],[-1,0]])
Nr,Nrp,Np=s.symbols("Nrr Nrp Npp")
C=L*s.Matrix([[Nr,Nrp],[Nrp,Np]])*L.T
require(C==s.Matrix([[Nr-6*Nrp+9*Np,Nr-3*Nrp],[Nr-3*Nrp,Nr]]),"Four same-source noise blocks")
require(L.det()==3,"Metric-stress map retains both rows")
finish("interior_lapse.py",dict(
 homogeneous_interior_two_by_two_response_noise_limit=True,
 general_compact_lapse_integral_need_not_vanish=True,
 unit_lapse_final_times_may_differ=True,moving_scalar_evaluation_retained=True,
 response_weak_tail="C_xy/K^2 on stated smooth directions",
 noise_tail="8 C_x C_y/K",GNS_tail="sqrt(8/K) C_x",
 chain_metric_contacts_retained=True,bare_seagull_separate_fullfield_value_claimed=False,
 anchored_gauge_contact="minus integral A_K f(z_prime-h mu)",
 finite_K_mean_off_shell_retained=True,anchored_case_counted_as_separate_theorem=False,
 proper_clock_initial_tests_automatically_interior=False,
 matter_integrated_external_geometry=True,geometry_quantum_integrated=False,
 all_spatial_tensor_response_limit=False,finite_amplitude_full_influence=False,
 sufficient_scale_and_background_jets=9,sufficient_lapse_jets=8),paths)
