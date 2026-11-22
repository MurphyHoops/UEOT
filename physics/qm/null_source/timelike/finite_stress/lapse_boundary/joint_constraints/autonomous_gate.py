"""Exact covariance contradiction for the specified pure-history contract."""
import sympy as sp
from common import require,finish
k,r=sp.symbols('k r',positive=True)
V=sp.diag(1/(2*k),k/2)
for sign in [-1,1]:
    A=sp.Matrix([[0,1],[-(k*k+sign*r),0]])
    dot=A*V+V*A.T
    require(sp.simplify(dot[0,1]+sign*r/(2*k))==0,'nonconstant ramp covariance')
    require(dot[0,0]==0 and dot[1,1]==0,'initial diagonal covariance rates')
a,b,c=sp.symbols('a b c',real=True)
G=sp.Matrix([[a,b],[b,c]]);J=sp.Matrix([[0,1],[-1,0]])
A=J*G
stationarity=A*V+V*A.T
require(sp.simplify(stationarity[0,0]-b/k)==0,'constant quadratic body stationarity')
finish('autonomous_gate.py',{
 'contract':'fixed autonomous quadratic total Hamiltonian; exact whole pure body history; finite tested second moments',
 'normal_pure_body_marginal_forces_product_extension':True,
 'cross_covariance_zero_at_each_time':True,
 'flat_initial_covariance_forces_constant_body_covariance_under_contract':True,
 'nontrivial_AQ_or_new_local_pulse_target_rejected_under_contract':True,
 'apparatus_Gaussianity_required':False,
 'all_autonomous_quantum_actuators_excluded':False,
 'mixed_intermediate_states_or_approximation_excluded':False,
 'nonquadratic_actuator_field_times_body_square_excluded':False,
 'full_field_extension_requires_tested_domains_and_flow_uniqueness':True
},inputs=['physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/LOCAL_PREPARATION.md',
          'physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/SOURCE_ACCOUNTING.md'])
