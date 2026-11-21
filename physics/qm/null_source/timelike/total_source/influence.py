"""Exact matrix-element, characteristic-function and noise normalizations."""
import sympy as s
from common import *
y,c,q,alpha_bar=s.symbols("y c q alpha_bar",positive=True)
d=s.Integer(4)
cross=-d*y/(2*alpha_bar**(d+2))
delta=s.simplify(4*c*cross)
assert delta==-8*c*y/alpha_bar**6
amp=8*c*y/(1+y)**3
assert s.factor(s.diff(amp,y))==-8*c*(2*y-1)/(y+1)**4
assert amp.subs(y,s.Rational(1,2))==32*c/27
W,V,a=s.symbols("W V a",positive=True)
Dp=16*c*d*(W/(3*V*a**4))**2
assert s.simplify(-s.Rational(1,2)*(3*V*a**4)**2*Dp+8*c*d*W**2)==0
assert s.simplify(((1-q)**2/(1+q*q-2*q))**4)==1
bound=32*WEIGHT/27
finish("influence.py",{
 "proof":"INFLUENCE.md","delta_F_shell":"-8*c*abs(beta)^2/conj(alpha)^6",
 "all_orders_shell_expression":True,"quadratic_log_matches_complete_pressure_noise":True,
 "global_algebraic_contrast_upper_c_equals_w":outward(bound),
 "pure_rotation_contrast_zero":True,
 "algebraic_maximum_claimed_on_shell_attainable":False,
 "influence_interpreted_as_metric_probability":False
},("INFLUENCE.md","COHERENCE.md","PRESSURE_NOISE.md"))
