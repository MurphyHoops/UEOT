"""Outward budgets and the complete scaled-reader contrast."""
from common import iv,box,load,require,above,below,outward,finish
p='physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/'
old=load(p+'prepared_record.json');load(p+'quantified_preparation.json')
eta=iv.mpf(1)/10**13
mu=box(old['receiver_mean_unit_strength_lower'])
control=10**6/(2*(1-iv.mpf('0.004096')))
xcoef=1600000*control
require(below(xcoef,iv.mpf('8.04e11')),'actual target-dependent control')
x=iv.mpf('8.04e11')*eta**2
qfactor=2*iv.exp(x)*(1+3*x+x*x)
require(below(qfactor,iv.mpf('2.1')),'small Gaussian graph majorant')
Ecoeff=(iv.mpf('2.1')*iv.mpf('8.04e11'))**2
Vcoeff=2*(1+Ecoeff*eta**4)*Ecoeff
require(below(Ecoeff,iv.mpf('3e24')) and below(Vcoeff,iv.mpf('7e24')),'quartic preparation budgets')
Pstar=iv.mpf(11)/20*iv.sqrt(1+(iv.mpf(22)/5)**2)
variancecoef=26*Pstar+iv.mpf('.07')+iv.mpf('337.5')*eta**2
require(below(variancecoef,65),'complete retained variance envelope')
den=iv.sqrt(2*(iv.mpf('.01')+eta**2*iv.mpf(9)/16))
xmax=eta**2*mu/iv.sqrt(iv.mpf('.02'))
contrastcoef=2*mu/den/iv.sqrt(iv.pi)*iv.exp(-xmax*xmax)
require(above(contrastcoef,iv.mpf('2.734e-4')),'uniform quadratic contrast')
finish('scaled_record.py',{
 'eta_range':'0 < eta <= 1e-13','sigma_eta':'1/(10 eta)',
 'actual_control_norm_coefficient_upper':outward(control),
 'preparation_energy_eta4_coefficient_upper':outward(Ecoeff),
 'preparation_variance_eta4_coefficient_upper':outward(Vcoeff),
 'complete_retained_energy_increment_upper':'13.03 eta^2',
 'complete_retained_variance_eta2_coefficient_upper':outward(variancecoef),
 'binary_contrast_eta2_coefficient_lower':outward(contrastcoef),
 'binary_contrast_at_eta_1e_13_lower':outward(contrastcoef*eta**2),
 'common_normal_output_coordinate':'y=eta z; limit N(0,.01) tensor identity',
 'all_outcomes_retained':True,'reader_energy_and_cross_noise_retained':True,
 'eight_conditions_preserved_after_encoding_and_reading':False,
 'autonomous_reader':False,'background_local_tensor_noise_eliminated':False,
 'SI_calibration':False
},inputs=[p+'PREPARED_RECORD.md',p+'prepared_record.json',p+'quantified_preparation.json'])
