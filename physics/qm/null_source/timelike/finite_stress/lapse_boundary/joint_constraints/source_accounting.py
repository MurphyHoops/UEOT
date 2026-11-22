"""Source matrix subtraction, instantaneous cross term and total Ward block."""
import sympy as sp
from common import require,finish
r,s=sp.symbols('r s',real=True)
sx=sp.Matrix([[0,1],[1,0]]);P=(sp.eye(2)+sx)/2;M=r*sx+s*P
require(sp.expand(sp.trace(M*M)-(2*r*r+2*r*s+s*s))==0,'matrix source-square polynomial')
require(sp.trace(M)==s,'source trace')
b,bd,e,z,H=sp.symbols('b bd epsilon zeta Hharm',real=True)
ct=H*(b*e+bd*z)**2/64
require(sp.diff(ct,e,z)==H*b*bd/32,'instantaneous mixed counterterm retained')
v=sp.symbols('v',positive=True)
N=v*sp.Matrix([[1,-1],[-1,1]])
require(N*sp.Matrix([1,1])==sp.zeros(2,1) and N.det()==0 and sp.trace(N)==2*v,'total transfer null and positive nonzero direction')
finish('source_accounting.py',{
 'matrix_mass_source':'r sigma_x + s P_plus',
 'source_square_polynomial':'2 r^2 + 2 r s + s^2',
 'local_log_counterterm':'Hharm_K integral(2rs+s^2)/(16 V0)',
 'dipole_profile_counterterm':'Hharm_K |b epsilon+bprime zeta|^2 / 64',
 'linear_source_term_retained_before_local_variation':True,
 'instantaneous_epsilon_zeta_cross_counterterm_retained':True,
 'finite_R_s_datum_declared_zero':True,
 'actual_net_work_cutoff_limit_equals_final_excitation_energy':True,
 'instantaneous_power_dominated_cutoff_limit_proved':False,
 'nonzero_smeared_external_Ward_transfer_noise_exists':True,
 'required_total_transfer_noise_block':'v [[1,-1],[-1,1]], v>0 for selected tests',
 'apparatus_mean_only_compensation_sufficient':False,
 'independent_apparatus_noise_sufficient':False,
 'quantum_actuator_joint_state_and_source_constructed':False,
 'absolute_phase_sensitive_CTP_completion':False
},inputs=['physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/JOINT_PREPARATION.md',
          'physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/LOCAL_PREPARATION.md'])
