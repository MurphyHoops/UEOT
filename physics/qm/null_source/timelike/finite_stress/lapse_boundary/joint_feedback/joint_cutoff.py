"""Original complete-generator cutoff/current and actual incoming pair algebra."""
import sympy as s
from common import *
P="physics/qm/null_source/timelike/finite_stress/lapse_boundary/"
paths=[P+"RELATIONAL_DOMAIN.md",P+"relational_coupled/COEFFICIENT_WINDOW.md",
 P+"relational_coupled/ALL_SIGN_EVOLUTION.md",P+"relational_coupled/ORDERING_DOMAIN.md",
 P+"relational_coupled/ACTUAL_UV_BRIDGE.md",P+"relational_coupled/actual_uv_bridge.json",
 P+"quiet_window.json"]
uv,quiet=load(paths[-2]),load(paths[-1])
require(uv["same_actual_background_and_incoming_state"] and quiet["new_initial_slow_amplitude_exact"]=="exp(-20000)","Same accepted incoming history")
kap,om,Om,c,h=s.symbols("kappa omega Omega c h",positive=True)
w=-s.I*Om-c
pair=(w*w+om*om)/(4*kap*Om)+w/(2*Om)
target=(om*om-Om*Om+c*c)/(4*kap*Om)-c/(2*Om)+s.I*(c/kap-1)/2
require(s.simplify(pair-target)==0,"Complete H0/kappa plus original dilation pair coefficient")
aa,bb=s.symbols("omega_correction momentum_correction",real=True)
asym={Om:om+aa/om,c:h+bb/om**2}
require(s.simplify(s.limit(pair.subs(asym),om,s.oo)-s.I*(h/kap-1)/2)==0,"Actual leading high pair mismatch")
mean=(Om*Om+c*c+om*om)/(4*Om)
dmean=-c/(2*Om)
require(s.simplify(s.limit(om*(mean.subs(asym)-om/2),om,s.oo)-h*h/4)==0,"Actual vacuum energy correction")
require(s.simplify(s.limit(om*dmean.subs(asym),om,s.oo)+h/2)==0,"Dilation mean correction")
k,K=s.symbols("k K",integer=True,positive=True)
sum2=s.summation(k*k,(k,3,K))
require(s.limit(sum2/K**3,K,s.oo)==s.Rational(1,3),"Two-particle growth coefficient")
require(s.simplify(2*(2*k*k)*(h/kap-1)**2/4-k*k*(h/kap-1)**2)==0,"Real-mode and pair multiplicity")
H=s.symbols("harmonic",real=True)
Crad=K*(K+1)*(K*(K+1)-1)/4-H/8
require(s.simplify(s.summation(k**3-k/2,(k,1,K))-H/8-Crad)==0,"All static vacuum subtraction terms")
eps=s.symbols("eps",positive=True)
require(s.limit((s.sqrt(1-eps)-1+eps/2+eps**2/8)/eps**3,eps,0)==-s.Rational(1,16),"Summable actual static remainder order")
require(s.simplify(h*h/(4*kap)-h/2+kap/4-(kap-h)**2/(4*kap))==0,"Complete expectation mismatch square")
# Test the differential commutator on independent smooth symbols.
eta=s.symbols("ordering",real=True)
f=s.Function("f")(kap);psi=s.Function("psi")(kap)
A=lambda z:-s.diff(s.diff(z,kap)/kap,kap)+(eta-s.Rational(3,4))*z/kap**3
B=lambda z:-s.I*(s.diff(z,kap)/kap-z/(2*kap**2))
comm=s.simplify(A(f*psi)-f*A(psi))
explicit=-2*s.diff(f,kap)*s.diff(psi,kap)/kap-s.diff(f,kap,2)*psi/kap+s.diff(f,kap)*psi/kap**2
require(s.simplify(comm-explicit)==0,"Exact bounded geometry commutator")
require(s.simplify(s.I*comm-B(s.diff(f,kap)*psi)-s.diff(f,kap)*B(psi))==0,"Anticommutator current identity")
r=1+s.sqrt(1+4*eta)/2
require(s.simplify(r*r-2*r-eta+s.Rational(3,4))==0,"Friedrichs ground-state form drift")
g,dg=s.symbols("g delta_g",nonzero=True)
require(s.simplify(1/(2*(g+dg))-1/(2*g)+dg/(2*g*(g+dg)))==0,"Nonzero cutoff kinetic difference")
finish("joint_cutoff.py",dict(
 original_complete_generator_and_dilation_retained=True,
 all_original_AE_counterterms_and_U0_retained=True,
 exact_cutoff_dynamical_intertwining=False,
 bounded_witness_nonzero_current_minimum_form_growth="Omega(log(K)^2), conditional instantaneous bound",
 unbounded_kappa_current_required="g_K nu, on its stronger Ehrenfest domain",
 actual_source_product_core_pair_norm_squared_over_K_cubed="expectation[(h_i/kappa-1)^2]/3 >0",
 complete_product_core_mean_over_K_squared="expectation[(kappa-h_i)^2/kappa]/4 >0",
 vacuum_reference_is_same_actual_incoming_state=True,
 fixed_product_core_generator_convergence=False,
 source_pair_coefficient_canceled_by_scalar_counterterms=False,
 strong_propagator_nonexistence_claimed=False,
 time_integrated_oscillation_and_correlated_preparation_still_require_proof=True,
 no_cutoff_independent_joint_dynamics_proved=True),paths)
