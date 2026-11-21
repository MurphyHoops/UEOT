"""Independent exact identities for the new state and static total equations."""
import sympy as s
from common import finish
x,U,b,k,M,mu,n,J=s.symbols("x U b k M mu n J",positive=True)
G=4*U*x**3-3*x**2-k*x
N=3*x-3*U*x**2-2*b+s.Rational(9,2)*k
rho=U+(2*b-4*k+N)/x**2+G/(2*x**3)
pressure=-U+(2*b/3-k+N/3)/x**2+G/(2*x**3)
assert s.factor(rho-3/(2*x))==0
assert s.factor(pressure+1/(2*x))==0
assert s.factor(rho-3*pressure-3/x)==0
assert s.factor(s.diff(G,x)-(3*G/x+3*x+2*k))==0
# Independent trace removes both standard reference zero modes exactly.
assert s.factor((2*b-4*k)-3*(2*b/3-k)+k)==0
x0,h,u=s.symbols("x0 h u",positive=True)
difference=s.expand((G.subs(x,x0)-G.subs(x,x0-h)).subs(U,u/x0)/x0)
shift=(12*u-6-k/x0)*h-(12*u-3)*h**2/x0+4*u*h**3/x0**2
assert s.factor(difference-shift)==0
thermal_polynomial=3*(x0-h)-3*u*(x0-h)**2/x0-(3*x0-3*u*x0)
assert s.factor(thermal_polynomial-((6*u-3)*h-3*u*h**2/x0))==0
# Posterior derivatives use dc/dt=2/nu and dw/dt=-d*w*(1-w)/c^2.
c,nu,d,w=s.symbols("c nu d w",positive=True)
m1=(1+d*w)/c**2+2/(nu*c)
v1=d**2*w*(1-w)/c**4+4*(1+d*w)/(nu*c**3)+4/(nu**2*c**2)
dm=s.diff(m1,c)*2/nu+s.diff(m1,w)*(-d*w*(1-w)/c**2)
assert s.factor(dm+v1)==0
p,delta,m,v,vs=s.symbols("p delta m v vs")
pf=1-p
mf=m+p*delta/pf
vf=(v-p*vs-p*delta**2/pf)/pf
assert s.factor(p*(m-delta)+pf*mf-m)==0
assert s.factor(p*vs+pf*vf+p*pf*(mf-(m-delta))**2-v)==0
# Eight thermal real oscillators: first two number cumulants.
z,occupation=s.symbols("z occupation",real=True)
logpgf=-8*s.log(1+occupation*(1-s.exp(z)))
assert s.simplify(s.diff(logpgf,z).subs(z,0)-8*occupation)==0
assert s.simplify(s.diff(logpgf,z,2).subs(z,0)-8*occupation*(1+occupation))==0
# Full energy normalization, including both zero-mode reference subtractions.
A,pi,mu,zv,occupation=s.symbols("A pi mu zv occupation",positive=True)
V=2*pi**2*A**3
Es=pi**2*M/A**3
Omega=s.sqrt(3)/A
energy_variance=Es**2*zv+8*Omega**2*occupation*(1+occupation)
assert s.factor(energy_variance/V**2-(M**2*zv/(4*A**12)+6*occupation*(1+occupation)/(pi**4*A**8)))==0
# Thermal mode response (k=2, omega^2=3) and stiffness cancellation.
rate,Rt,Rz=s.symbols("rate Rt Rz",positive=True)
delta_pt=-s.Rational(4,3)*Rt*(1+rate**2/(rate**2+12))
thermal_bracket=3*s.Rational(4,3)*Rt+delta_pt
assert s.factor(thermal_bracket-s.Rational(4,3)*Rt*(rate**2+24)/(rate**2+12))==0
assert 3*(2*Rz)-6*Rz==0
# Global cap: N'=3-6Ux+k/(2x), using G>0.
epsilon=s.symbols("epsilon",positive=True)
Nprime=3-6*U*x+k/(2*x)
assert s.factor(Nprime.subs(U,((3+k/x)/4+epsilon)/x)+s.Rational(3,2)+k/x+6*epsilon)==0
ell,vR,nu0=s.symbols("ell vR nu0",positive=True)
mean=ell+1/nu0
variance=vR+2*ell/nu0+1/nu0**2
assert s.factor(variance-mean/nu0-(vR+ell/nu0))==0
finish("algebra.py",{
 "identities":{"both_static_Einstein_components":True,"independent_trace":True,
 "unique_positive_cubic_root_derivative":True,"correlated_shifted_cubic":True,
 "thermal_polynomial_shift":True,"posterior_mean_derivative_minus_variance":True,
 "complete_record_mean_and_variance":True,"eight_oscillator_cumulants":True,
 "full_energy_density_variance":True,"actual_thermal_response":True,
 "zero_momentum_stiffness_cancellation":True,"global_thermal_cap_derivative":True,
 "all_record_variance_floor":True},
 "mean_equations":"M2*mu=4*U0*x^3-3*x^2-x/(16*pi^2); J*n=3*x-3*U0*x^2-2*B(x)+3*D0",
 "AE_terms_deleted":False,"generic_dynamic_existence_theorem_used":False})
