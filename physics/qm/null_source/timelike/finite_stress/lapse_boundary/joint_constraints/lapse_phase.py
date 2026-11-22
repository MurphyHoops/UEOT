"""Exact restricted anomaly/contact algebra, moments and outward phase budget."""
import sympy as sp
from common import iv,require,below,outward,finish
q,z=sp.symbols('q z',real=True)
R=6*(1+q);Rnn=-3*q;Rij=2+q
Ric2=Rnn**2+3*Rij**2
H3=-Rnn**2-sp.Rational(2,3)*R*Rnn+Ric2/2-R**2/4
require(sp.simplify(H3+3)==0,'H3 normal contraction')
H1algebra=R**2/2+2*R*Rnn
require(sp.simplify(H1algebra-18*(1-q*q))==0,'H1 normal algebraic part')
f=sp.symbols('f',real=True)
Jnorm=2/(1+sp.sqrt(1-f*f))
series=sp.series(Jnorm,f,0,18).removeO()
for n in range(9):
    moment=sp.factorial(2*n)/(4**n*sp.factorial(n)*sp.factorial(n+1))
    require(sp.expand(series).coeff(f,2*n)==moment,'S3 dipole moment')
L=(1-sp.sqrt(1-f*f))/(240*(1+sp.sqrt(1-f*f)))
require(sp.simplify(L-(Jnorm-1)/240)==0,'phase integral')
require(sp.diff(-L,f,2).subs(f,0)==-sp.Rational(1,480),'complete Hamiltonian contact')
require(sp.simplify(sp.diff(-L,f)+f/(120*sp.sqrt(1-f*f)*(1+sp.sqrt(1-f*f))**2))==0,'covariant charge derivative')
require(sp.simplify((z/(1+z))**2-2*z/(1+z)-(1/(1+z)**2-1))==0,'dipole integrated tensor reduction')
fmax=iv.mpf(1)/20
s=iv.sqrt(1-fmax*fmax)
coef=500/(240*(1+s)**2)
require(below(coef,iv.mpf('.53')),'normalized pulse phase budget')
finish('lapse_phase.py',{
 'family':'unit S3; shift zero; N=1+f(t)Z; constant paired masses +/-1/5',
 'finite_datum':'same alpha=1/(4320 V0), same source-square subtraction',
 'mass_transfer':'same unit-normal Cauchy regulator and paired Hadamard subtraction',
 'Hamiltonian_scalar':'-(1-sqrt(1-f^2))/(240(1+sqrt(1-f^2)))',
 'total_Hamiltonian_contact':'-delta(t-s)/480',
 'explicit_R2_only_contact':'-delta(t-s)/240',
 'normalized_pulse_action_epsilon2_upper':outward(coef),
 'action_at_epsilon_1e_8_upper':outward(coef/10**16),
 'actual_restricted_covariant_two_branch_phase_limit':True,
 'same_normal_initial_density':True,
 'actual_metric_cutoff_one_energy_graph_convergence':True,
 'actual_metric_cutoff_all_energy_graphs_proved':False,
 'centered_noise_changed_by_scalar_phase':False,
 'general_metric_CTP_or_full_tensor_Hessian_constructed':False,
 'terminal_mean_Einstein_failure_repaired_by_phase':False
},inputs=['physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/LAPSE_HISTORY.md',
'physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/LAPSE_CURVATURE.md',
'physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/GROUND_DATUM.md'])
