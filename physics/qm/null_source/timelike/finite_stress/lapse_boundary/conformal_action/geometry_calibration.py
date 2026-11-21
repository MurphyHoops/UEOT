"""Same-parameter geometry/stress gaps and information-disturbance bounds."""
import sympy as s
from common import finish,require,iv,interval,box,outward,above,below,load
from model import HISTORY,branch_box
local='physics/qm/null_source/timelike/finite_stress/lapse_boundary/conformal_action/local_autonomous.json'
data=load(local)['energy_record']
f=iv.exp(-iv.mpf(1)/50)
km=iv.mpf('49880072');kp=iv.mpf('50627122.5')
kl=iv.mpf('50126122.5');kh=iv.mpf('50379072.5');gap=kh-kl;theta=(kh+kl)/2
require(above(theta-kl) and above(kh-theta),'one fixed gap threshold')
row=branch_box('.56','.56',(f*km).a,(f*kp).b)
kap=row['kappa'];disc=row['sqrt_disc'];a=row['a']
theta_row=branch_box('.56','.56',(f*theta).a,(f*theta).b)
gapk=f*gap/(2*kap*disc);gapH=gapk/a
V=2*iv.pi**2
gapapp=f*gap/(V*a**4)
gaptotal=3*f*gap/(2*a*a*disc)
require(above(gapk) and above(gapH) and above(gaptotal),'strict geometry and stress gaps')
lowrow=branch_box('.56','.56',(f*km).a,(f*kl).b)
highrow=branch_box('.56','.56',(f*kh).a,(f*kp).b)
absolute_overlap=bool(lowrow['kappa'].b>=highrow['kappa'].a)
eps=box(data['total_effect_error_bound']).b;ein=box(data['incoming_norm_error_bound']).b
require(below(eps,'.5'),'nontrivial code calibration')
coherence=iv.mpf('.5')-iv.sqrt(eps*(1-eps))
actual=coherence-ein
require(above(actual,'.076'),'actual source marginal disturbance')
# Pressure and complete density derivative identities, using d_z=-2ac/d.
zz,dd,ac,aa,Y,ff=s.symbols('z d ac a Y f',positive=True)
rho=3*Y/(2*aa*aa);press=-rho+3*zz/(aa*aa*dd)
Dz=lambda expr:s.diff(expr,zz)+s.diff(expr,Y)/dd-2*ac*s.diff(expr,dd)/dd
require(s.simplify(ff*Dz(rho)-3*ff/(2*aa*aa*dd))==0,'complete density monotonicity')
require(s.simplify(ff*Dz(press)-ff*(3/(2*aa*aa*dd)+6*ac*zz/(aa*aa*dd**3)))==0,'complete pressure monotonicity')
finish('geometry_calibration.py',{'final_u':.56,'gap_K':252950,
 'K_gap_threshold':'50252597.5','K_phase_comparison_midpoint':'50253597.25',
 'parameter_dependent_kappa_threshold_bounds':outward(theta_row['kappa']),
 'same_parameter_kappa_gap_lower_bound':outward(gapk),
 'same_parameter_Hubble_gap_lower_bound':outward(gapH),
 'apparatus_density_pressure_gap_lower_bound':outward(gapapp),
 'total_density_pressure_gap_lower_bound':outward(gaptotal),
 'broad_absolute_parameter_enclosures_overlap':absolute_overlap,
 'universal_parameter_independent_numeric_threshold_claimed':False,
 'calibration_error_upper_bound':outward(eps),
 'coherent_seed_output_trace_distance_lower_bound':outward(coherence),
 'actual_incoming_output_source_trace_distance_lower_bound':outward(actual),
 'calibration_scope':'pre-read geometry/stress binary class on actual prepared range',
 'source_code_QND_used_for_disturbance':True,
 'continuous_geometry_precision_or_constraint_residual_measured':False,
 'terminal_reader_energy_conservation_proved':False,
 'SI_units_calibrated':False},inputs=[HISTORY,local])
