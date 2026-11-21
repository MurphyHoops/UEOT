"""Arbitrary normal-pointer frontier plus exact Gaussian lower bound."""
import sympy as s
from common import *
p="physics/qm/null_source/timelike/";base=p+"finite_stress/lapse_boundary/";new=base+"relational_coupled/"
load(new+"mean_recovery.json");src=load(new+"source_budgets.json")
thin=load(p+"finite_stress/boundary_state.json")
A=box(load(p+"joint_history/history.json")["cases"]["unfiltered"]["A"])
sig=box(thin["example_sigma"]);Ez=box(thin["mean_unfiltered_zero_energy"])
mu=iv.exp(-iv.mpf(2)/3)/64
s2h=A*500000*sig*iv.sqrt(mu)
require(above(s2h,100),"Source-intrinsic quadratic variance is nonzero")
require(below(iv.mpf("1e15")+(1/iv.mpf(80000)**2+iv.mpf("1e-14"))*iv.mpf("1e22"),iv.exp(36)),"Linear residual coefficient budget")
h=iv.exp(-19980);s1=iv.exp(-1122);s0=iv.exp(-1098)
require(below(iv.mpf("1e19")*h*h+iv.mpf("2e7")*h+iv.mpf("1e-4"),iv.mpf(".01")),"Mean budget forces x>1/(1e8 h)")
# Scale by h to avoid tiny/huge float conversions.
margin=iv.mpf("1e-14")-s1/iv.mpf("1e8")-s0*h
require(above(margin,iv.mpf("5e-15")) and above(iv.ln(iv.mpf("5e-15"))+19980,19940),"Arbitrary pointer actual residual floor")
require(above(iv.mpf("2e-6")-s1),"Quadratic lower bound increasing above required x")
t,aa,j,ll,Q=s.symbols("t a j l Q",real=True);d=s.symbols("delta",positive=True)
# Classical conditional-mean variance for a shared real Gaussian t.
r1,r2,v=s.symbols("r1 r2 v",real=True)
gauss_var=r1*r1*v+r2*r2*(3*v*v-v*v)
require(s.simplify(gauss_var.subs(v,1/(4*d*d))-(r1*r1/(4*d*d)+r2*r2/(8*d**4)))==0,"Gaussian conditional-mean variance")
ar=s.symbols("aR",positive=True);optimal=(ar/2)**s.Rational(1,3)
value=d*d+ar*ar/(8*d**4)
require(s.simplify(s.diff(value,d).subs(d,optimal))==0,"Minimum of displayed lower bound")
require(s.simplify(value.subs(d,optimal)-3*ar**s.Rational(2,3)/2**s.Rational(5,3))==0,"Exact Gaussian lower-bound optimum")
req,J,L=s.symbols("required J L",positive=True)
xmin=2*req/(J+s.sqrt(J*J+4*L*req))
require(s.simplify(L*xmin*xmin+J*xmin-req)==0,"Stable resource-frontier root")
finish("preparation_frontier.py",dict(
 fixed_gate="U_B=exp(-i Q_g A delta H_in,K / h_i)",
 arbitrary_independent_normal_pointer_states_including_mixtures_and_phases=True,
 initial_source_pointer_correlations_covered=False,
 finite_residual_second_moment_implies_pointer_fourth_moment=True,
 source_orthogonal_projection_prevents_derivative_phase_cancellation=True,
 source_quadratic_residual_s2_over_h_lower=outward(s2h),
 necessary_pointer_x_lower="1/(1e8*h_i)",
 actual_toy_centered_residual_RMS_strict_lower="5e-15/h_i > exp(19940)",
 simultaneous_old_mean_resource_and_small_toy_residual="REJECTED for this gate and input",
 Gaussian_lower_bound="delta^2+r1^2/(4 delta^2)+(A*h_prime*E_z)^2/(8 delta^4)",
 pointer_identified_with_original_Pu=False,all_possible_preparations_excluded=False,
 local_autonomous_total_device_constructed=False),
 [new+"mean_recovery.json",new+"source_budgets.json",p+"joint_history/history.json",
 p+"finite_stress/boundary_state.json",base+"INCOMING_PREPARATION.md",base+"READOUT_WITNESS.md",
 base+"ACTUAL_INVERSE.md",p+"finite_stress/BOUNDARY_STATE.md"],proof="PREPARATION_FRONTIER.md")
