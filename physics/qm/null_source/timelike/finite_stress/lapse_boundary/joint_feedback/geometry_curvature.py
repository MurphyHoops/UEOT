"""Exact force algebra and outward actual-history obstruction bounds."""
import sympy as s
from common import *
P="physics/qm/null_source/timelike/finite_stress/lapse_boundary/"
paths=[P+"relational_coupled/negative_recovery.json",P+"quiet_window.json",
 P+"relational_coupled/NEGATIVE_RECOVERY.md",P+"joint_feedback/NEAR_RECOVERY.md",
 P+"joint_feedback/POSITIVE_WINDOW.md",P+"joint_feedback/WEIGHTED_EVOLUTION.md"]
neg,quiet=load(paths[0]),load(paths[1])
require(neg["actual_K"]==131072 and quiet["new_initial_slow_amplitude_exact"]=="exp(-20000)","Actual fixed history")
x=s.symbols("kappa",positive=True);eta=s.symbols("eta",real=True)
f=s.Function("f")(x);v=s.Function("V")(x)
A=lambda y:-s.diff(y,x,2)/x+s.diff(y,x)/x**2+(eta-s.Rational(3,4))*y/x**3
B=lambda y:-s.I*(s.diff(y,x)/x-y/(2*x**2))
require(s.simplify(s.I*(A(B(f))-B(A(f)))-s.diff(s.diff(f,x)/x**3,x)-(3*eta+s.Rational(7,4))*f/x**5)==0,"Exact kinetic force")
require(s.simplify(s.I*(v*B(f)-B(v*f))+s.diff(v,x)*f/x)==0,"Exact potential force")
require(s.simplify(s.I*(A(x*f)-x*A(f))-2*B(f))==0,"Exact geometry current")
# Real scalar polarization gives the vector-valued Hardy identity; boundary derivative explicit.
F=s.Function("F")(x);psi=x**2*F
hardy=s.diff(psi,x)**2/x**3-4*psi**2/x**5
require(s.simplify(hardy-x*s.diff(F,x)**2-s.diff(2*F**2,x))==0,"Weighted Hardy plus vanishing boundary term")
h=iv.exp(-19980)
Pbound=8*iv.exp(50)*h**2+8*iv.exp(30)*h**4+24*h**6+2*h**4
require(below(Pbound,1),"Positive force budget")
require(6*9*s.Rational(1,4)-1>10,"Uniform ordering margin")
require(6*9*s.Rational(3,4)-1>30,"Original ordering margin")
require(below(2*h**2,2),"Target second-jet bound")
require(s.Rational(128,729)-s.Rational(1,16)>s.Rational(1,12),"Fixed-ordering central packet force")
require((s.Rational(512,441))**3<2,"Packet inverse-cube bound")
require((s.Rational(512,441))<2,"Packet inverse-first bound")
positive_packet=16*iv.exp(50)*h**2+16*iv.exp(30)*h**4+24*h**6+2*h**4
require(below(positive_packet,8),"Packet positives <1/(8 delta h^5), delta<=1/64")
require(s.Rational(18,48)-s.Rational(1,8)==s.Rational(1,4),"Packet final force coefficient")
finish("geometry_curvature.py",dict(actual_K=131072,
 exact_kinetic_force="d_kappa(kappa^-3 d_kappa)+(3 eta+7/4) kappa^-5",
 weighted_Hardy_coefficient=4,
 positive_budget_log_upper=outward(iv.log(Pbound)),
 fixed_ordering_class=[-.25,.5],class_force_strict_upper="-10 h^-5",
 original_eta_zero_force_strict_upper="-30 h^-5",
 target_force_absolute_upper="2 h^-3",second_jet_gap_strict_lower="8 h^-5",
 arbitrary_fixed_ordering_packet_condition="delta (3 eta+7/4) <= 1/32",
 packet_force_strict_upper="-1/(4 delta h^5)",
 actual_core_right_second_derivative_proved=True,
 general_Q3_implies_second_Ehrenfest=False,
 source_independence_assumed=False,momentum_budget_needed_for_class_gate=False,
 positive_window="min(T0, d_kappa/(4 C_kappa))",
 positive_gap_strict_lower="2 h^-5 t^2",
 model_units_are_SI=False,full_quantum_gravity_no_go=False),paths)
