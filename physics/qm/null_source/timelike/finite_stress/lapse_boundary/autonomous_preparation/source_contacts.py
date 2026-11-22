"""Mass-source heat polynomial and direct lapse/contact bookkeeping."""
import sympy as s
from common import finish,require
P='physics/qm/null_source/timelike/finite_stress/lapse_boundary/autonomous_preparation/'
x,p,q,a,b,g,alpha,beta,kappa,eta,sc,ss,zc,zs,R,N,ct,Gdot=s.symbols('x p q a b g alpha beta kappa eta sc ss zc zs R N ct Gdot',real=True)
S=p*p+q*q
V=a*x*x/2+b*S/2+g*x*p*q+alpha*x**4/4+beta*(p**4+q**4)/4+kappa*p*p*q*q/2+eta*x*x*S/2
M=s.hessian(V,(x,p,q));shift=s.diag(sc,ss,ss)
Ps=sc*(a+3*alpha*x*x+eta*S)+ss*(2*b+2*eta*x*x+(3*beta+kappa)*S)+sc*sc/2+ss*ss
require(s.expand(s.trace((M+shift)*(M+shift)-M*M)/2-Ps)==0,'full local source heat polynomial')
require(s.hessian(Ps,(sc,ss))==s.diag(1,2),'direct source contact Hessian')
Fs=zc*sc+2*zs*ss;Gs=sc+2*ss
require(s.trace(shift)==Gs,'source total derivative')
require(s.trace(s.diag(zc,zs,zs)*shift)==Fs,'source curvature term')
H0,Oc,Os=s.symbols('H0 Oc Os')
HN=N*(H0+sc*Oc+ss*Os)
require(s.diff(HN,N,sc)==Oc and s.diff(HN,N,ss)==Os,'tree lapse-source contacts')
require(s.diff(HN,N,2)==0 and s.hessian(HN,(sc,ss))==s.zeros(2),'tree unmixed second columns')
end=ct*Gdot/(6*N)
require(s.diff(end,N,Gdot)==-ct/(6*N*N),'endpoint mixed derivative')
sr,sa=s.symbols('sr sa')
require(s.expand((sr+sa/2)**2-(sr-sa/2)**2)==2*sr*sa,'real source-square CTP has no aa noise')
finish('source_contacts.py',{
 'sources':'real smooth scalar mass-squared profiles s_chi,s_s with phi/psi exchange',
 'source_heat_polynomial':str(s.expand(Ps)),
 'source_curvature':'R*(zeta_chi*s_chi+2*zeta_s*s_s)',
 'source_total_derivative':'-box(s_chi+2*s_s)/6',
 'direct_bulk_source_Hessian':'c_ct*N*sqrt(h)*diag(1,2)*delta',
 'mixed_lapse_source_column':'c_ct*sqrt(h)*[(partial_i P_s)*sigma_i+zeta_i_eff*(R_h*sigma_i-2*Delta_h*sigma_i)]',
 'source_endpoint':'c_ct/6*[integral sqrt(h)*partial_t(s_chi+2*s_s)/N]',
 'tree_Hamiltonian_N_s_contacts':['O_chi','O_s'],
 'direct_local_CTP_counterterm_mixed_branch_bulk_Hessian':'0',
 'full_influence_mixed_branch_covariance_set_to_zero':False,
 'real_c_number_counterterm_history_Gram_positivity_preserved':True,
 'real_c_number_counterterm_cancels_symmetrized_noise':False,
 'operator_words_domain_required_for_CTP_second_derivatives':True,
 'external_source_Ward_work_terms_retained':True,
 'initial_density_and_metric_projector_variations_automatically_zero':False,
 'normal_joint_continuum_limit_constructed':False
},inputs=[P+'LOCAL_BASIS.md',P+'local_basis.json',P+'LOCAL_CTP.md',P+'local_ctp.json',P+'LOCAL_COUNTERTERMS.md',P+'local_counterterms.json'])
