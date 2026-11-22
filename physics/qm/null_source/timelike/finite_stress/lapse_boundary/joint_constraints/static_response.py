"""Exact response-range, two-mode preparation and passivity identities."""
import sympy as sp
from common import iv,require,above,below,outward,load,finish
r=iv.mpf(1)/5;V=2*iv.pi**2
w0=iv.sqrt(1+r);w1=iv.sqrt(4+r)
C=(2+r-w0*w1)/(2*iv.sqrt(w0*w1))
require(below(C,0) and above(-C,iv.mpf(4)/267),'nonzero independent state column')
mu=sp.symbols('mu',positive=True)
x=sp.sqrt(1+mu);y=sp.sqrt(4+mu)
require(sp.simplify((2+mu)**2-(x*y)**2+mu)==0,'rationalized squeeze column')
gn,rho,p=sp.symbols('G rho p',nonzero=True)
constant=(-2+8*sp.pi*gn*(rho+p)).subs(p,1/(4*sp.pi*gn)-rho)
require(sp.simplify(constant)==0,'actual constant cokernel at mean static solution')
s,omega=sp.symbols('s omega',real=True)
n=(sp.sqrt(1+s*s)-1)/2
require(sp.simplify(n*(n+1)-s*s/4)==0,'squeeze energy variance')
ground=load('physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/ground_datum.json')
require(ground['mean_static_equations_exact'],'signed common datum')
finish('static_response.py',{
 'minimum_missing_scalar_response_directions':5,
 'four_l1_conditions_derived_for_actual_natural_prepared_mean':True,
 'homogeneous_condition_uses_static_ground_Hellmann_Feynman':True,
 'complete_cokernel_or_complement_inverse_proved':False,
 'global_two_mode_density_column_C':outward(C),
 'global_preparation_energy_per_pair':outward(w0+w1),
 'global_two_mode_gate_is_local_autonomous_device':False,
 'common_two_code_average_energy_increase_lower':'eta^2 ||f||^2 / 2',
 'positive_cost_cancellable_by_O_eta_squared_metric_only_response':False,
 'second_order_geometric_response_retained_as_open_task':True,
 'static_l0_result_applied_to_actual_ramp_output':False,
 'full_quantum_constraint_solution':False
},inputs=['physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/ground_datum.json',
          'physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/GROUND_DATUM.md'])
