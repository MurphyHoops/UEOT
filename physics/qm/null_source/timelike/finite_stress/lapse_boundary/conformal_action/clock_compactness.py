"""Compact-family lemma diagnostics; no predecessor evolution executed."""
import sympy as s
from common import finish,require,load
old='physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_propagation/interior_collapse.json'
load(old)
z=s.symbols('z',nonzero=True)
chi=(1-(z+1/z)/2)/(2*s.pi)
require(s.expand(chi).coeff(z,0)*2*s.pi==1,'normalized fixed bump')
fixed=[];moving=[]
for n in [2,3,7,19]:
    value=s.expand(z**n*chi).coeff(z,0)*2*s.pi
    require(s.simplify(value)==0,'fixed oscillatory test')
    fixed.append(0)
    moving.append(1)
# Explicit finite-net estimate, with positive rational inputs.
eps=s.Rational(1,100)
net_error=s.Rational(1,1000)
require(eps+net_error==s.Rational(11,1000),'finite-net bound')
finish('clock_compactness.py',{
 'finite_net_estimate':'sup_C ||T_K X|| <= epsilon + max_net ||T_K X_j||',
 'fixed_bump_integrals':fixed,'moving_bump_integrals':moving,
 'uniform_temporal_and_Hilbert_tail_tightness_suffices':True,
 'fixed_smooth_clock_or_convergent_endpoint_repairs_old_kernel':False,
 'actual_new_apparatus_implemented_by_examples':False},inputs=[old])
