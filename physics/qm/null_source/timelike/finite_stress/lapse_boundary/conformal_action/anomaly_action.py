"""Anomaly, R² linkage, Ward and closed de Sitter algebra."""
import sympy as s
from common import finish,require
u,k,c,j,l,n,lam,V,A,U=s.symbols('u k c j l n lam V A U',real=True)
def D(f):
    return s.diff(f,u)*k+s.diff(f,k)*c+s.diff(f,c)*j+s.diff(f,j)*l
def EL(f):return s.diff(f,u)-D(s.diff(f,k))+D(D(s.diff(f,c)))
def E(f):return k*(s.diff(f,k)-D(s.diff(f,c)))+c*s.diff(f,c)-f
checks={}
def zero(name,x):
    require(s.simplify(x)==0,name);checks[name]=True
Lan=-n*c*c/480-n*k**4/720
trace=n*(-6*l+12*c+36*k*k*c-12*c*(1+k*k))/1440
zero('anomaly_trace',EL(Lan)-trace)
Ean=-n*k**4/240-n*c*c/480+n*k*j/240
zero('anomaly_lapse_energy',E(Lan)-Ean)
zero('anomaly_offshell_Ward',D(E(Lan))+k*EL(Lan))
F=lam*(k+k**3/3)
Lr=lam*(c+k*k+1)**2/2
Lr0=lam*c*c/2+lam*(k*k+1)**2/2
zero('R2_endpoint',Lr-Lr0-D(F))
zero('R2_Euler_endpoint_invariance',EL(Lr)-EL(Lr0))
zero('R2_energy_endpoint_invariance',E(Lr)-E(Lr0))
a2=A*A*s.exp(2*u)
Lgeo=3*V*a2*(1-k*k)/2-V*U*a2*a2+Lan+Lr0
g=lam-n/240
zero('geometric_chi_hessian',s.diff(Lgeo,c,2)-g)
zero('complete_geometric_Ward',D(E(Lgeo))+k*EL(Lgeo))
pk=s.symbols('pk')
H=s.expand(pk*pk/(2*g)-Lgeo.subs(c,0))
d0=V*U*a2*a2-3*V*a2/2-lam/2
d1=3*V*a2/2-lam
d3=n/720-lam/2
zero('complete_constraint_coefficients',H-(pk*pk/(2*g)+d0+d1*k*k+d3*k**4))
des={c:1+k*k,j:2*k*(1+k*k)}
zero('deSitter_anomaly_plus_Casimir',(Ean+n/240).subs(des)-n*(1+k*k)**2/480)
zero('deSitter_R2_energy',E(Lr0).subs(des))
# The closed de Sitter chart obeys a²=A²(1+k²).
constraint=-3*V*A*A*(1+k*k)**2/2+V*U*A**4*(1+k*k)**2+n*(1+k*k)**2/480
zero('deSitter_mean_density',constraint.subs(U,s.Rational(3,2)/A**2-n/(480*V*A**4)))
zero('deSitter_trace_equation',trace.subs({c:1+k*k,l:2*(1+k*k)*(1+3*k*k)})+n*(1+k*k)**2/120)
finish('anomaly_action.py',{'identities':checks,'n_real_scalars_example':2,
 'Casimir_energy_example':'1/120','geometry_coefficient':'lambda-n_s/240',
 'fixed_background_anomaly_prescription':'canonical Box R coefficient',
 'full_quantum_gravity_renormalization':False,'old_mean_history_inherited':False})
