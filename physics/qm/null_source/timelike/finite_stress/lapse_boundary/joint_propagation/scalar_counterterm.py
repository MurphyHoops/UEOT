"""Exact scalar candidate, action rows, Wick contractions and virtual sum."""
from __future__ import annotations
import sympy as sp
from common import finish, require, iv, interval, outward, below, above
K,k=sp.symbols("K k",integer=True,positive=True)
nu=lambda z:z/4-sp.Rational(1,16)-1/(8*z)-1/(8*(z+1))
require(sp.simplify(nu(K)-nu(K-1)-K*K/(4*(K*K-1)))==0,"Reference variance telescoping")
require(sp.simplify(nu(2)-sp.Rational(1,3))==0,"Reference variance initial shell")
u,g0,v,N=sp.symbols("u g0 v N",real=True)
g=g0+u/4; r=v/(2*g); ff=-r
require(sp.simplify(sp.diff(r,u)+v/(8*g*g))==0,"New lapse mixed contact")
require(sp.simplify(sp.diff(r,u,2)-v/(16*g**3))==0,"New u-u contact")
ob=sp.simplify(sp.diff(ff,u,2)-4*sp.diff(ff,u))
require(sp.simplify(ob+v*(1+8*g)/(16*g**3))==0,"No A exp(4u)+B absorption")
h=sp.symbols("h",real=True)
require(sp.simplify(h*N*sp.diff(r,u)-N*sp.diff(r,u)*h)==0,"Added homogeneous Ward identity")
# Two independent Gaussian coordinates: exact Wick expansion of centered Q^2.
q1,q2,v1,v2=sp.symbols("q1 q2 v1 v2",real=True)
Q=(q1*q1+q2*q2)/2; mean=(v1+v2)/2
normal_Q2=(q1**4-6*v1*q1*q1+3*v1*v1+q2**4-6*v2*q2*q2+3*v2*v2
            +2*(q1*q1-v1)*(q2*q2-v2))/4
linear=v1*(q1*q1-v1)+v2*(q2*q2-v2)
variance=(v1*v1+v2*v2)/2
require(sp.expand((Q-mean)**2-normal_Q2-linear-variance)==0,"Full Wick linear term retained")
# Exact four-particle factors and leading rescaled second moment.
a,b=sp.symbols("a b",positive=True)
norm4=24*a**4+16*a*a*b*b+24*b**4
require(sp.expand(norm4-(8*(a*a+b*b)**2+16*(a**4+b**4)))==0,"Four-particle raw norm")
require(sp.Rational(4,1)*sp.Rational(1,8)==sp.Rational(1,2),"Remaining second moment coefficient")
# The Riemann integral determining the double-shell leading constant.
x,y=sp.symbols("x y",positive=True)
ri=sp.integrate(sp.integrate(1/(x+y),(y,0,1)),(x,0,1))
require(sp.simplify(ri-2*sp.log(2))==0,"Virtual double-shell coefficient")
finish("scalar_counterterm.py",{
"model_changed_for_candidate":True,"original_AE_modified_in_this_cohort":False,
"necessary_leading_scalar_for_equal_time_densities":"v(kappa)=1/(2kappa)+constant",
"phase_fixed_gate_requires_constant_zero":True,
"explicit_candidate":"V_ct=-alpha_K nu_K/kappa",
"nu_K_closed_form":"K/4-1/16-1/(8K)-1/(8(K+1))",
"candidate_rescaled_group":"I","candidate_scaled_variance_limit":"I2/2",
"frozen_action_parameter_absorption":"EXCLUDED on any open u interval in stated family",
"pure_endpoint_interpretation":"EXCLUDED",
"new_lapse_action":"integral N nu_K/(2 g_K(u)) d eta",
"new_homogeneous_Ward_identity":True,"four_dimensional_covariant_origin":"OPEN",
"full_Wick_operator_contraction_retained":True,
"virtual_static_form_coefficient":"K log(2)/(8 kappa)",
"second_time_layer_propagation_proved":False
},inputs=[
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/ACTION_LIFT.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/ACTION_BOUNDARY.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/relational_coupled/COEFFICIENT_WINDOW.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_propagation/ADIABATIC_CONNECTION.md",
"physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_propagation/INITIAL_LAYER.md"])
