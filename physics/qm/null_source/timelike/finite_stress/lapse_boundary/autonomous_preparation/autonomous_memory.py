"""Exact harmonic-clock source-sign memory; finite-LO effect and scope."""
import sympy as s
from common import finish,require,iv,outward,above,below,load,box
P='physics/qm/null_source/timelike/finite_stress/lapse_boundary/autonomous_preparation/'
ab=load(P+'collision.json');ac=load(P+'resource_budget.json')
z=s.symbols('z',real=True)
F=35*z**4-84*z**5+70*z**6-20*z**7
require(F.subs(z,0)==0 and F.subs(z,1)==1,'clock plateaus')
for j in range(1,4):
 require(s.diff(F,z,j).subs(z,0)==s.diff(F,z,j).subs(z,1)==0,'C3 clock endpoint')
require(s.expand(s.diff(F,z)-140*z**3*(1-z)**3)==0,'monotone clock switch')
rot=s.Matrix([[1,1],[-1,1]])/s.sqrt(2)
require(s.simplify(rot.T*s.diag(1,-1)*rot)==s.Matrix([[0,1],[1,0]]),'beam splitter count sign and normalization')
I=iv.mpf(1)/25;sh=(iv.exp(I)-iv.exp(-I))/2
nref=(iv.exp(2*I)-1+sh**2)/2
require(below(nref,'.043'),'reference probe occupation')
B=iv.mpf(10)**4;kappa=iv.exp(-iv.mpf(1)/200)
dlo=(iv.sqrt(nref)/iv.sqrt(2)+iv.mpf(1)/4)/B
require(below(dlo,'.00004'),'finite local oscillator error')
eps=box(ac['final_vector_error_bound_interval'])
dcl=box(ab['classical_binary_contrast_lower_bound_interval'])
gap=dcl-2*eps-kappa*dlo
require(above(gap,'.00229'),'actual complete autonomous-memory contrast')
finish('autonomous_memory.py',{
 'actual_model':'Hext=WR(H_M+N_LO+h_R)WRdagger; all conjugated interactions retained',
 'fixed_collision_example':ac['final_fixed_example'],
 'reader_clock':{'m':'1','Omega':'2*pi','center':'-1/2','initial_support':['-2','-1'],'endpoint_support':['0','1'],'T':'1/2'},
 'local_oscillator':{'B':'1e4','initial_beta':'i*B*exp(i/2)','endpoint_beta':'i*B'},
 'clock_arrival_postselection':False,'clock_endpoint_exact':True,
 'reference_probe_occupation_upper_bound_interval':outward(nref),
 'finite_LO_characteristic_error_bound_interval':outward(dlo),
 'actual_register_probability_contrast_lower_bound_interval':outward(gap),
 'full_normal_CP_instrument':True,'intermediate_number_projection':False,
 'Gaussian_full_instrument_reproduced':False,
 'physical_register_projectors_passively_transformed':False,
 'actual_field_cutoff_limit':True,'original_total_H_code_laws_still_identical':True,
 'permanent_unitary_record':False,'unread_unitary_register_uncomputes_at_T':'1',
 'local_covariant_four_dimensional_action_constructed':False,
 'terminal_PVM_physical_mechanism_constructed':False
},inputs=[P+'collision.json',P+'resource_budget.json',P+'COLLISION.md',P+'RESOURCE_BUDGET.md'])
