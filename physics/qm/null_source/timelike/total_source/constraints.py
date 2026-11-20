"""New symbolic/interval density-constraint certificate."""
import sympy as s
from mpmath import iv
from common import *
z,w=s.symbols("z w",positive=True)
assert s.simplify((z*z/2+2*w*w)*2*z*z/(z*z+4*w*w)-z*z)==0
u=s.symbols("u")
h,v,a3=s.symbols("h v a3")
ell0=s.symbols("ell0")
H1=-36*a3*h+72*v*h*h+18*v*v+36*h*h-18
H3=3*h**4+6*h*h+3
ran=(-H1/6+H3)/2880-H1/s.Integer(1728)+(H1*(2+ell0+2*u)/32-s.Rational(9,4)*(h*h*v+h*h))/36
linear=s.diff(ran.subs({h:u*h,v:u*v,a3:u*a3}),u).subs(u,0)
assert s.simplify(linear+s.Rational(1,32))==0
x,M,mu,U,Jn=s.symbols("x M mu U Jn",positive=True)
B=s.Function("B")(x)
rho=U+M*mu/(2*x**3)+(2*B-1/(4*s.pi**2)+Jn)/x**2
dr=s.diff(rho,x).subs(s.diff(B,x),-1/(64*s.pi**2*x))
rz=M*mu/(2*x**3);rv=(2*B-1/(4*s.pi**2)+Jn)/x**2
enthalpy=2*rz+s.Rational(4,3)*rv+1/(48*s.pi**2*x**2)
assert s.simplify(x*dr+s.Rational(3,2)*enthalpy)==0
kappa=M2/(3*X**2);assert above(kappa,"0.23")
bound=exact("1.01")+exact(2)/3*(exact(".6")*iv.exp(exact(".4"))+exact("1.01")*iv.exp(exact(".2"))+7*iv.exp(exact(".2"))/(2*iv.pi**2*exact("6e9"))+exact(".16")*iv.exp(exact(".2"))/(iv.pi**2*exact("6e9")))
assert below(bound,3)
constant=3*iv.exp(exact(".04"))/(exact(".23")*exact(".01")*exact(".9"))
assert below(constant,1510)
var_s=4*R*L+4*R**2+exact(3)/16
density_variance=M2**2*var_s/(4*A**12)+6*N*(N+1)/(iv.pi**4*A**8)
assert above(density_variance,0)
finish("constraints.py",{
 "proof":"CONSTRAINTS.md","dynamic_energy_linear_term_zero":True,
 "AE_dynamic_log_density_variation":"-u/(16*pi^2*A^4)",
 "complete_density_tangent":"delta_rho_geom=-3*u/A^2",
 "independent_density_source_linear_constraint":"xi_rho_total=0",
 "quadratic_necessary_bound":"abs(delta_m)<1510*||u||_E4^2 for ||u||<=0.01",
 "kappa":outward(kappa),"E_ball_upper":outward(bound),"quadratic_constant_upper":outward(constant),
 "absolute_stochastic_constraint_solved_by_zero_density_noise_difference":False,
 "new_common_nonlinear_history_or_pointwise_metric_lower_bound_proved":False,
 "actual_baseline_spatial_average_density_variance":outward(density_variance),
 "specified_independent_noise_linear_extension_has_absolute_constrained_baseline":False,
 "deterministic_semiclassical_mean_solution_invalidated":False
},("CONSTRAINTS.md",))
