"""Independent critical reduction algebra and outward common-chart certificate."""
import sympy as s
from common import finish,require,iv,outward,above,below
from model import HISTORY,chart,extrema
B,c,k,E,D=s.symbols('B c k E D',real=True)
F=3*c*k**4+B*k*k+E-D
Pu=2*B*k+4*c*k**3
checks={}
def zero(name,x):
    require(s.simplify(x)==0,name);checks[name]=True
zero('Legendre_constraint',k*Pu-(B*k*k+c*k**4+D)+E-F)
zero('Legendre_hessian',s.diff(Pu,k)-2*(B+6*c*k*k))
# Implicit differentiation F_E+F_k*k_E=0.
ke=-1/s.diff(F,k)
zero('reduced_energy_derivative',-s.diff(Pu,k)*ke-1/k)
ac,m,a2,U,V,N,lam=s.symbols('ac m a2 U V N lam',real=True)
expr=F.subs({c:ac/3,B:2*ac-m*a2,D:m*a2-V*U*a2*a2+ac,E:2*ac+N})
zero('Casimir_screened_constraint',expr-(ac*(1+k*k)**2-m*a2*(1+k*k)+V*U*a2*a2+N))
# Exact statewise Ward with an arbitrary proper-rest sector energy fA.
Y,chi,rad,rest,aa=s.symbols('Y chi rad rest aa',real=True)
rho=(rad+rest+ac*Y*Y)/(V*aa**4)+U
p=rad/(3*V*aa**4)+(ac*Y*Y-4*ac*chi*Y)/(3*V*aa**4)-U
du_rho=(-4*rad-3*rest+4*ac*Y*chi-4*ac*Y*Y)/(V*aa**4)
zero('complete_projected_Ward',du_rho+3*(rho+p))
rows,du=chart()
kap=extrema(rows,'kappa');disc=extrema(rows,'disc')
ceiling=extrema(rows,'energy_ceiling')
proper=sum((du*r['a']/r['kappa'] for r in rows),iv.mpf(0))
require(above(kap,'0.9') and below(kap,'1.1'),'common expanding window')
require(above(disc) and above(ceiling,100),'admitted energy band')
finish('critical_branch.py',{'identities':checks,'clock_window':[0.54,0.56],
 'total_excitation_band':[0,100],'interval_cells':200,
 'kappa_bounds':outward(kap),'discriminant_bounds':outward(disc),
 'energy_ceiling_bounds':outward(ceiling),'proper_duration_model_units':outward(proper),
 'units_are_SI_seconds':False,'new_reduced_ordering_declared':True,
 'independent_geometry_tensor_factor':False,'unrestricted_field_CCR_claimed':False,
 'old_mean_history_inherited':False},inputs=[HISTORY])
