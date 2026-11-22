"""Three-field Hessian, local counterterm basis and lapse/endpoint algebra."""
import sympy as s
from common import finish,require
x,p,q,r,rp,rpp,m,R,xi,g,eta,N,Fdot,kappa=s.symbols('x p q r rp rpp m R xi g eta N Fdot kappa',real=True)
delta=s.Matrix([[rpp*p*q,rp*q,rp*p],[rp*q,0,r],[rp*p,r,0]])
F=rpp*p*q
half=s.trace(delta*delta)/2
wanted=r*r+rp*rp*(p*p+q*q)+rpp*rpp*p*p*q*q/2
require(s.expand(half-wanted)==0,'bounded r Hessian squared')
require(s.trace(delta)==F,'Hessian trace')
free=s.diag(m+xi*R,s.Symbol('m_p')+s.Symbol('xi_p')*R,s.Symbol('m_q')+s.Symbol('xi_q')*R)
difference=s.trace(free*delta)+half-R*s.trace(delta)/6
require(s.expand(difference-(wanted+(m+(xi-s.Rational(1,6))*R)*F))==0,'subtracted bulk heat polynomial')
endpoint=kappa*Fdot/(6*N)
require(s.diff(endpoint,N)==-kappa*Fdot/(6*N*N),'endpoint lapse first column')
require(s.diff(endpoint,N,2)==kappa*Fdot/(3*N**3),'endpoint lapse contact')
V=g*x*p*q+eta*x*x*(p*p+q*q)/2
D=s.hessian(V,(x,p,q))
stated=g*g*(x*x+p*p+q*q)+8*g*eta*x*p*q+4*eta*eta*x*x*(p*p+q*q)+eta*eta*x**4+eta*eta*(p*p+q*q)**2/2
require(s.expand(s.trace(D*D)/2-stated)==0,'stabilized action full Hessian polynomial')
require(s.expand(s.trace(D)-eta*(p*p+q*q+2*x*x))==0,'stabilized trace')
zz=s.symbols('z',nonnegative=True)
require(s.expand((m+eta*zz*zz-g*zz)-(eta*(zz-g/(2*eta))**2+m-g*g/(4*eta)))==0,'minimum quadratic stability bound')
finish('local_counterterms.py',{
 'approximation':'one-loop local background-field UV diagnostic',
 'Hessian_order':['chi','phi','psi'],
 'trace_delta_M':'r_second*phi*psi',
 'half_trace_delta_M_squared':'r^2+r_prime^2*(phi^2+psi^2)+(r_second^2/2)*phi^2*psi^2',
 'curvature_multiplier':'(xi_chi-1/6)*R*r_second*phi*psi',
 'total_derivative':'-box(r_second*phi*psi)/6',
 'vacuum_r_squared_counterterm_alone_sufficient_for_local_three_field_model':False,
 'bulk_lapse_column':'kappa*sqrt(h)*(P+a*(R_h*F-2*Delta_h*F))',
 'source_containing_mixed_lapse_columns_present':True,
 'restricted_static_h_bulk_second_lapse_column':'0',
 'endpoint_lapse_first':'-kappa/6*[integral sqrt(h)*F_dot*deltaN/N^2]',
 'endpoint_second_contact':'kappa/3*[integral sqrt(h)*F_dot*deltaN1*deltaN2/N^3]',
 'CTP_two_branch_lapses_retained':True,
 'RF_boundary_completion_automatically_fixed':False,
 'linear_cubic_bare_potential_semibounded':False,
 'classical_stabilizer_threshold':'eta>=g^2/(4*m_source^2)',
 'stabilizer_new_one_loop_quartics':['chi^4','(phi^2+psi^2)^2'],
 'single_finite_coefficient_for_every_counterterm_required':False,
 'positive_normal_quantum_continuum_state_constructed':False,
 'Einstein_constraint_charge_match_proved':False
})
