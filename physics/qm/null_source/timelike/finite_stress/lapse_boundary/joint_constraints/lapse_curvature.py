"""Exact lapse curvature contractions and the declared finite action contact."""
import sympy as sp
from common import require,finish
q=sp.symbols('q',real=True)
R=6*(1+q);Rm=12*(1+q*q);Rc=12*(1+q+q*q)
require(sp.expand(Rm-2*Rc+R*R/3)==0,'conformal flatness')
require(sp.expand(Rm-4*Rc+R*R-24*q)==0,'Euler density')
a=sp.symbols('a',real=True)
require(sp.simplify((1+a)*(6*(1+a/(1+a)))**2-36*(4*a+1/(1+a)))==0,'integrated R2 reduction')
f=sp.symbols('f',real=True)
L=(1-sp.sqrt(1-f*f))/(120*(1+sp.sqrt(1-f*f)))
expected=f/(60*sp.sqrt(1-f*f)*(1+sp.sqrt(1-f*f))**2)
require(sp.simplify(sp.diff(L,f)-expected)==0,'finite action lapse derivative')
require(sp.diff(L,f,2).subs(f,0)==sp.Rational(1,240),'explicit finite action contact')
finish('lapse_curvature.py',{
 'weyl_squared':'0','Euler_density':'24 f Z/(1+f Z)',
 'relative_integrated_a0_a2_a4_zero_on_this_family':True,
 'finite_R2_action':'integral[(1-sqrt(1-f^2))/(1+sqrt(1-f^2))] /120',
 'explicit_R2_Hamiltonian_contact':'-delta(t-s)/240',
 'same_unit_radius_finite_alpha_datum_retained':True,
 'relative_UV_pole_zero_proves_finite_metric_phase_matching':False,
 'base_anomaly_phase_matching_completed_here':False,
 'general_metric_CTP_functional_or_Hessian_constructed':False
},inputs=['physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/GROUND_DATUM.md',
          'physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/LAPSE_HISTORY.md'])
