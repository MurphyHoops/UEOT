"""Actual initial incoming coefficient bounds, using positive-frequency Wiener tails."""
import sympy as s
from common import *
P="physics/qm/null_source/timelike/"
paths=[P+"dynamic_inverse/fast_root.json",P+"joint_history/history.json",
 P+"finite_stress/boundary_state.json",P+"finite_stress/lapse_boundary/quiet_window.json",
 P+"finite_stress/lapse_boundary/relational_coupled/negative_recovery.json"]
fast,hist,thin,quiet,neg=[load(p) for p in paths]
r=box(fast["fast_conformal_growth_rate"]);slow=box(fast["old_positive_root_reused"])
A=box(hist["cases"]["unfiltered"]["A"]);p=box(thin["shell_N2_probability"])
require(above(r,900000) and below(r,937000),"Actual fast root")
require(above(slow,"1.9") and below(slow,"2.1"),"Actual slow root")
require(above(A,80000) and below(A,100000) and above(p) and below(p,".08"),"Actual source constants")
require(quiet["new_initial_slow_amplitude_exact"]=="exp(-20000)" and neg["actual_K"]==131072,"Same actual history and cutoff")
c=iv.exp(-20000);K=neg["actual_K"]
w4=lambda z:(1+z)**4*iv.log(iv.e+z)
Ws=w4(slow);Wf=w4(r)
require(below(Ws,200) and below(Wf,"1e26"),"Frozen weights")
C0=exact("2e20")*6400/(2*(1-exact(".128")))
seed=(Ws+exact("1.1")*Wf)*c
Rgeo=C0*seed**2*(1+Wf)
require(below(Rgeo,iv.exp(300)*c**2),"Relative nonlinear geometry remainder")
M=(Ws+Wf)*c+Rgeo
require(below(M,iv.exp(62)*c),"Actual E4 norm")
Mv=M+M*M;Vdiff=Rgeo+M*M
require(below(Mv,iv.exp(63)*c) and below(Vdiff,iv.exp(301)*c*c),"Potential bounds")
RW=Vdiff/2+Mv**2/(2*(1-Mv/3))
require(below(RW,iv.exp(302)*c*c),"Product remainder coefficient")
h_bound=(r+slow)*c+Rgeo
require(below(h_bound,1000000*c),"Expansion relative to c")
W1coef=Mv/(2*(1-Mv/3))
Nerr=RW/2+Rgeo+h_bound*W1coef
require(below(Nerr,iv.exp(305)*c*c),"Dilation numerator remainder")
sumcube=(K*(K+1)//2)**2
Derr=(sumcube+1)*Nerr
require(below(Derr,iv.exp(400)*c*c),"Full finite-K error")
fast_factor=exact(900000)/(10**12+4*K*K)
require(above(fast_factor,".0000008"),"High-half fast bound")
fast_lower=exact("0.00000000625")*K**6
slow_upper=exact(3)*sumcube
lower=(fast_lower-slow_upper-36)-Derr/c
vac_lower=(fast_lower-slow_upper)-Derr/c
require(above(lower,"1e22") and above(vac_lower,"1e22"),"Actual strictly negative D_Omega")
extra_N=12*(exact(1)/900000+exact(3)/12)+Nerr/c
require(below(extra_N,5) and below(4*extra_N,100),"Support-compressed excitation bound")
V0=2*iv.pi**2
product_lower=exact(2)*exact("1e16")/(3*V0*A**4)
entangled_lower=exact("1e16")/(3*V0*A**4)
require(above(product_lower,"1e-6") and above(entangled_lower,"1e-7"),"Pressure derivative margins")
h,R=s.symbols("h R",positive=True);wt=h/(2*R-h)
require(s.simplify((1-wt)*2/h+wt/R-(2/h-1/R))==0,"Exact packet inverse mean")
rr,ss,om=s.symbols("r s omega",positive=True)
nlin=rr**3/(rr**2+4*om**2)-ss**3/(ss**2+4*om**2)-(rr-ss)
require(s.simplify(nlin+4*om**2*(rr/(rr**2+4*om**2)-ss/(ss**2+4*om**2)))==0,"Exact Jost product coefficient")
finish("pressure_witness.py",dict(
 actual_K=K,actual_source_shell_probability=outward(p),
 actual_fast_root=outward(r),actual_slow_root=outward(slow),
 log_c=-20000,
 nonlinear_geometry_relative_error_log_upper=outward(iv.log(Rgeo/c**2)),
 product_relative_error_coefficient_log_upper=outward(iv.log(RW/c**2)),
 full_D_error_over_c_log_upper=outward(iv.log(Derr/c)),
 fast_negative_coefficient_lower=outward(fast_lower),
 slow_positive_coefficient_upper=outward(slow_upper),
 minus_D_over_c_strict_lower=outward(lower),
 minus_D_over_h_strict_lower="1e16",
 product_pressure_u_derivative_difference_strict_lower=outward(product_lower),
 fixed_geometry_law_joint_row_strict_lower=outward(entangled_lower),
 joint_extension_may_be_entangled=True,
 joint_extension_requires_same_full_source_and_same_two_packet_kappa_law=True,
 arbitrary_geometry_laws_excluded=False,
 unbounded_pressure_derivative_requires_stated_domain=True,
 model_units_are_SI=False,raw_finite_K_is_full_AE_joint_solution=False,
 no_time_dependent_reselection=True),
 paths+[P+"nonlinear_history/KERNELS.md",P+"nonlinear_history/EXISTENCE.md",
 P+"finite_stress/GEOMETRY_MATCHING.md",P+"finite_stress/BOUNDARY_STATE.md",
 P+"finite_stress/lapse_boundary/joint_feedback/RAW_WARD.md"])
