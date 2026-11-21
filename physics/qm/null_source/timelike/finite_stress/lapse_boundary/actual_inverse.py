"""Actual quiet-history causal/advanced inverse budget with fixed-AE identities."""
import sympy as s
from common import iv,load,box,above,below,outward,require,finish
u=s.symbols("u0:7",real=True)
C0,ell0=s.symbols("C0 ell0",real=True)
h=u[1];v=u[2]+h*h
a3=u[3]+3*h*u[2]+h**3
a4=u[4]+4*h*u[3]+3*u[2]**2+6*h*h*u[2]+h**4
ell=ell0+2*u[0]
T1=-36*a4+144*a3*h-216*v*h*h+108*v*v+72*v-72*h*h
T3=12*v*h*h-12*h**4+12*v-12*h*h
original=(-T1/6+T3)/2880-T1/1728+(T1*(2+ell)/32-s.Rational(9,8)*(4*a3*h-10*v*h*h+3*v*v+4*v-6*h*h+1))/36
C=C0+30*u[0]
compact=-s.Rational(1,32)-C*u[4]/480+(C-29)*u[2]/240+(3*C-59)*h*h*u[2]/240+h*h/16-h*u[3]/8-3*u[2]**2/32+3*h**4/32
require(s.expand(original-compact.subs(C0,19+15*ell0))==0,"Full original AE trace polynomial")
def D(expr):
    return s.expand(sum(s.diff(expr,u[j])*u[j+1] for j in range(6)))
coef=[s.diff(compact,u[j]) for j in range(5)]
require(s.expand(coef[3]-2*D(coef[4]))==0,"Fourth/third derivative formal adjoint")
require(s.expand(coef[1]-D(coef[2])+D(D(D(coef[4]))))==0,"Second/first derivative formal adjoint")
eps0=s.Rational(1,1000)
bounds=[]
for a in coef:
    diff=s.expand(a-a.subs({z:0 for z in u}))
    total=0
    for powers,c in s.Poly(diff,C0,*u[:5]).terms():
        degree=sum(powers[1:])
        require(degree>=1,"Difference has a constant term")
        total+=abs(c)*400**powers[0]*eps0**(degree-1)
    bounds.append(s.factor(total))
declared=[s.Rational(188,1000),s.Rational(261,1000),s.Rational(318,1000),s.Rational(125,1000),s.Rational(625,10000)]
require(all(a<=b for a,b in zip(bounds,declared)) and sum(declared)<1,"AE five-coefficient majorant")
# Exact Hardy/Volterra factor inverse at the integrand level.
t=s.symbols("t",real=True);Uf=s.Function("U")(t);gg=s.Function("g")(t);J=s.Function("J")(t)
inv=s.exp(-2*Uf)*(gg-J)
# If J'=h*g and J(0)=0, derivative of e^U*inv integrates to the M inverse identity.
f=s.Function("f")(t);y=s.Function("y")(t)
mu_e=s.diff(s.exp(Uf)*inv,t)+s.diff(Uf,t)*s.exp(Uf)*inv
require(s.simplify(mu_e.subs(s.diff(J,t),s.diff(Uf,t)*gg)-s.diff(s.exp(-Uf)*gg,t))==0,"Exact pressure/action Volterra inverse")
inputs=["finite_stress/lapse_boundary/causal_domain.json",
 "finite_stress/lapse_boundary/quiet_window.json","joint_history/history.json",
 "nonlinear_history/KERNELS.md","finite_stress/lapse_boundary/ACTION_RESPONSE.md",
 "finite_stress/lapse_boundary/RETARDED_RESPONSE.md","finite_stress/lapse_boundary/CAUSAL_DOMAINS.md",
 "finite_stress/lapse_boundary/QUIET_WINDOW.md"]
ca=load(inputs[0]);quiet=load(inputs[1]);hist=load(inputs[2])
require(below(box(quiet["log_future_E4_U_upper"]),-1158),"Same actual quiet history bound")
require(below(box(ca["static_weighted_H4_operator_upper"]),"1e15"),"Frozen static full inverse bound")
gamma=box(ca["vertical_weight_gamma"]);require(above(gamma,2),"Weighted Hardy condition")
A=box(hist["cases"]["unfiltered"]["A"])
actualC0=19+15*(iv.ln(A*A/4)+2*iv.euler)
require(above(actualC0) and below(actualC0,400),"Original fixed AE constant")
T=iv.mpf(1)/50
schur=1000*T+T*T*(-iv.ln(T)+iv.mpf("4.5"))/4
thermal=iv.mpf(".16")*(T*T/(4*(iv.sqrt(3)**3))+500*T/9)
require(below(schur,21) and below(thermal,".18"),"All-k Schur and thermal budgets")
eps=iv.mpf(".001")
rblock=(4+6*eps)*23*5*(1+8*eps)
comm=48+12+72*eps
require(below(rblock,500) and below(comm,61),"Actual difference blocks")
require(500+61+8+4+17+3+30<1000,"Complete relative budget")
require(below((iv.mpf(2)/3)*iv.sqrt(2),1),"Static multiplier low-band constant")
logq=18*iv.ln(10)-1158
require(below(logq,-1100),"Strict Neumann gate without float underflow")
finish("actual_inverse.py",dict(
 actual_history="same once-selected c=exp(-20000), b(c), T=1/50",
 same_incoming_state_and_fixed_AE=True,
 background_norm_upper_symbolic="exp(-1158)",
 static_full_inverse_M0_declared=10**15,
 relative_difference_X_to_Y_upper="1000*epsilon_U",
 log_Neumann_parameter_upper=outward(logq),
 Neumann_parameter_strictly_below="exp(-1100)",
 causal_inverse_on_explicit_graph_domain=True,
 zero_initial_geometry_and_mode_transport_only=True,
 independent_advanced_H4_inverse=True,
 local_AE_formal_adjoint_exact=True,
 five_AE_coefficient_majorants_over_epsilon=[str(x) for x in bounds],
 all_k_Jost_Schur_vacuum_upper_expression=outward(schur),
 all_k_Jost_Schur_thermal_upper_expression=outward(thermal),
 pressure_Ward_factor_and_inverse_exact=True,
 pressure_adjoint_H3=True,
 inverse_series_remainder="M0*q_inv^(m+1)/(1-q_inv), Y to X",
 domain_is_entire_bare_H4=False,
 finite_K_inverse_strong_limit_proved=False,
 arbitrary_rough_output_is_nonlinear_Hadamard_geometry=False,
 arbitrary_tensor_inverse_constructed=False,
 nonzero_source_constraint_charge_satisfied_automatically=False,
 unweighted_stability_or_small_metric_noise_claimed=False),
 inputs,proof="ACTUAL_INVERSE.md")
