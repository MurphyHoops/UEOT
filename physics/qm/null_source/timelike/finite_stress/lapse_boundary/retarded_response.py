"""Exact WKB residual divisibility, frozen AE matching, and retained local contacts."""
import sympy as s
from common import require,finish
z,h=s.symbols("z h")
vs=s.symbols("v0:9"); V=vs[0]
def D(x):
    return s.expand(sum(s.diff(x,vs[j])*vs[j+1] for j in range(8)))
A1=-V/2;A3=(vs[2]-V**2)/8
A5=(-vs[4]+5*vs[1]**2+6*V*vs[2]-2*V**3)/32
F=1+A1*z+A3*z**2+A5*z**3
poly=s.Poly(s.expand(4*F**2*((1-F**2)/z-V)-2*F*D(D(F))+3*D(F)**2),z)
for j in range(3):
    require(s.expand(poly.nth(j))==0,"WKB residual low order not cancelled")
require(poly.nth(3)!=0,"Residual falsely exact at all orders")
co=h+D(F)/(2*F)
energy=(F**2+1+z*co**2)/(2*F)
pressure=(F**2-s.Rational(1,3)+z*co**2)/(2*F)
Ae=h*h/2;Ap=Ae-V/3
Ce=V*V/8+h*h*V/4-h*vs[1]/4
Cp=-V*V/8+h*h*V/4-h*vs[1]/4+vs[2]/12
for expr,b,A,C in ((energy,1,Ae,Ce),(pressure,s.Rational(1,3),Ap,Cp)):
    series=s.series(expr,z,0,3).removeO().expand()
    require(s.simplify(series-b-A*z-C*z*z)==0,"Frozen omega AE mismatch")
# Direct k conversion uses omega=k sqrt(1-1/k²).
b,A,C,d=s.symbols("b A C d")
conversion=b*s.sqrt(1-d)+A*d/s.sqrt(1-d)+C*d*d/(1-d)**s.Rational(3,2)
require(s.simplify(s.series(conversion,d,0,3).removeO()
          -(b+(A-b/2)*d+(C+A/2-b/8)*d*d))==0,"Frozen k AE mismatch")
a3,a4,ell,w0,w1,w2,w3,w4=s.symbols("a3 a4 ell w0 w1 w2 w3 w4")
H1=-36*a3*h+72*V*h*h+18*V*V+36*h*h-18
T1=-36*a4+144*a3*h-216*V*h*h+108*V*V+72*V-72*h*h
H3=3*h**4+6*h*h+3;T3=12*V*h*h-12*h**4+12*V-12*h*h
ran=(-H1/6+H3)/2880-H1/1728+(H1*(2+ell)/32-s.Rational(9,4)*(h*h*V+h*h))/36
tan=(-T1/6+T3)/2880-T1/1728+(T1*(2+ell)/32-s.Rational(9,8)*(4*a3*h-10*V*h*h+3*V*V+4*V-6*h*h+1))/36
pan=(ran-tan)/3
require(s.simplify(s.diff(ran,ell)*2*w0-H1*w0/576)==0,"Density log contact")
require(s.simplify(s.diff(pan,ell)*2*w0-(H1-T1)*w0/1728)==0,"Pressure log contact")
require(s.diff(ran,ell)!=0 and s.diff(pan,ell)!=0,"Dropping logs undetected")
# Direct jet variations of a'''/a and a''''/a.
u1,u2,u3,u4=s.symbols("u1 u2 u3 u4")
a3jet=u3+3*u1*u2+u1**3
a4jet=u4+4*u1*u3+3*u2*u2+6*u1*u1*u2+u1**4
for expr,target in ((a3jet,w3+3*u1*w2+3*(u2+u1*u1)*w1),
 (a4jet,w4+4*u1*w3+6*(u2+u1*u1)*w2+4*a3jet*w1)):
    variation=sum(s.diff(expr,u)*w for u,w in zip((u1,u2,u3,u4),(w1,w2,w3,w4)))
    require(s.expand(variation-target)==0,"Actual local metric contact chain")
finish("retarded_response.py",dict(
 residual_first_nonzero_inverse_omega_order=6,
 residual_polynomial_degree=poly.degree(),
 WKB_coefficients_and_both_frozen_AE_stress_subtractors_exact=True,
 fixed_log_contacts_retained=True, dropping_log_contact_negative_control=True,
 sufficient_scale_direction_derivatives=8,
 sufficient_lapse_direction_derivatives=7,
 all_time_high_jet_bounds_from_strict_analytic_margin=True,
 uniform_parameter_differentiated_mode_remainder="O(k^-5)",
 weighted_all_field_tail="C/(2*K^2), C depends on stated finite seminorms",
 numeric_remainder_constant_evaluated=False,
 actual_fixed_incoming_homogeneous_retarded_RSET_response_defined=True,
 arbitrary_tensor_retarded_Hessian_constructed=False,
 initial_slice_state_derivative_from_past=True),
 ["nonlinear_history/KERNELS.md","finite_stress/GEOMETRY_MATCHING.md"],
 proof="RETARDED_RESPONSE.md")
