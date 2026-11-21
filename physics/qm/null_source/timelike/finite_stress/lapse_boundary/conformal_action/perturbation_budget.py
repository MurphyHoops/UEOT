"""Outward conditional noncommuting evolution/record budget."""
from common import finish,require,iv,interval,box,outward,above,below,load
from model import HISTORY,chart
local='physics/qm/null_source/timelike/finite_stress/lapse_boundary/conformal_action/local_autonomous.json'
data=load(local)['energy_record']
rows,du=chart(0,100000000);c=iv.mpf(2)/1440
budget=iv.mpf(0)
for row in rows:
 # Choose genuinely one-sided common operator margins in each cell.
 Bmax=(-row['B']).b
 kmin=row['kappa'].a;kmax=row['kappa'].b;dmin=row['sqrt_disc'].a
 Lip=(2*Bmax+12*c*kmax*kmax)/(2*kmin*dmin)
 budget+=du*Lip
upper=budget.b
allow01=iv.mpf('.01')/upper;allow05=iv.mpf('.05')/upper
band=box(data['common_energy_band']);fall=iv.exp(interval('-.02','.02'))
Tband=fall*band
margin=iv.mpf([min(Tband.a,iv.mpf(100000000).a-Tband.b)]*2)
require(above(margin,allow05),'perturbation remains in admitted slab')
eps=box(data['total_effect_error_bound']).b
require(below(eps+iv.mpf('.05'),'.5'),'nontrivial calibrated code after conditional change')
finish('perturbation_budget.py',{'same_reduction_space_preparation_effect_assumed':True,
 'completed_counterterms_proved_to_meet_assumptions':False,
 'noncommuting_perturbations_allowed':True,
 'integrated_operator_Lipschitz_budget':outward(budget),
 'sufficient_sup_deltaT_for_additional_error_0_01':outward(allow01),
 'sufficient_sup_deltaT_for_additional_error_0_05':outward(allow05),
 'energy_slab_margin':outward(margin),
 'conditional_record_error_with_0_05':outward(eps+iv.mpf('.05')),
 'conditional_record_contrast_with_0_05':outward(1-2*(eps+iv.mpf('.05'))),
 'old_geometry_projector_or_QND_automatically_inherited':False,
 'finite_EFT_coefficients_fitted_or_loop_error_measured':False},
 inputs=[HISTORY,local])
