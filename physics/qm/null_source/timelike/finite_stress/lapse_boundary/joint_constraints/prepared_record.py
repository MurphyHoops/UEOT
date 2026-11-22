"""Same-preparation record with independently bounded covariance and full costs."""
from common import iv,box,load,require,above,below,outward,finish
old=load('physics/qm/null_source/timelike/finite_stress/lapse_boundary/autonomous_preparation/local_record.json')
load('physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/quantified_preparation.json')
ground=load('physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/ground_datum.json')
r=iv.mpf(1)/5;eta=iv.mpf(1)/10**11;R=iv.mpf(1)/10**16
cap=2*iv.pi*(iv.mpf(1)/2-iv.sin(1)/2)
half=2*iv.pi*(iv.mpf(1)/4-iv.sin(iv.mpf(1)/2)/2)
mu=r*iv.exp(-iv.mpf(2)/3)*half**2/(8*iv.pi*cap)
omu=box(old['receiver_mean_magnitude_lower'])
require(omu.a<=mu.a and mu.b<=omu.b,'state-independent old signal bound independently recovered')
x0=30*R
nu=iv.exp(2*x0)*(1/iv.sqrt(1+r)+1/iv.sqrt(1-r))/4
require(below(nu,iv.mpf(9)/16) and below(iv.exp(2*x0)/2,iv.mpf(11)/20),'new covariance envelope')
x=1600000*R;P=x+3*x*x+x**3;Q=2*iv.exp(x)*P
Ep=Q*Q;Vp=2*(1+Ep)*Ep
require(below(Ep,iv.mpf('1.025e-19')) and below(Vp,iv.mpf('2.05e-19')),'full preparation budget')
xl=mu*iv.sqrt(iv.mpf(200)/229)
contrast_coeff=2*xl/iv.sqrt(iv.pi)*iv.exp(-xl*xl)
contrast=eta*contrast_coeff
require(above(contrast,iv.mpf('3.61418e-16')),'same-state positive complete record')
Pstar=iv.mpf(11)/20*iv.sqrt(1+(iv.mpf(22)/5)**2)
read_lower=iv.mpf(25)/2*iv.exp(-iv.mpf(2)/3)*half/cap
energy_upper=box(ground['energy'])+Ep+eta*eta/2+iv.mpf(25)/2
var_upper=Vp+(25+eta*eta)*Pstar+25*eta*eta+iv.mpf(625)/2
require(above(read_lower,iv.mpf(8)/10),'nonvanishing fixed-resolution reader cost')
finish('prepared_record.py',{
 'input':'new certified local eight-control preparation; not old AQ covariance',
 'absolute_encoding_time':'pi','elapsed_read_time':'3','absolute_read_time':'pi+3',
 'exact_continuum_no_signal_elapsed_window':'0<tau<1/2',
 'positive_kernel_elapsed_window':'5/2<tau<pi',
 'code_strength':'1e-11','receiver_mean_unit_strength_lower':outward(mu),
 'new_reference_variance_upper':outward(nu),
 'complete_binary_contrast_lower':outward(contrast),
 'uniform_preparation_energy_upper':outward(Ep),
 'uniform_preparation_energy_variance_upper':outward(Vp),
 'reader_energy_increase_lower':outward(read_lower),
 'reader_energy_increase_upper':'25/2',
 'postread_full_retained_mean_energy_upper_expression':outward(energy_upper),
 'postread_full_retained_energy_variance_upper':outward(var_upper),
 'all_outcomes_retained':True,'same_actual_preparation_through_record':True,
 'conditional_nonselective_binary_output_normal_Hadamard':True,
 'actual_all_outcome_instrument_limit':True,
 'source_species_instantaneous_marginal_unchanged':True,
 'complete_retained_gravitational_source_changed':True,
 'eight_initial_mean_conditions_proved_preserved_after_encoding':False,
 'autonomous_pointer_or_completed_classical_collection':False,
 'SI_or_experimental_accessibility':False
},inputs=['physics/qm/null_source/timelike/finite_stress/lapse_boundary/autonomous_preparation/local_record.json',
          'physics/qm/null_source/timelike/finite_stress/lapse_boundary/autonomous_preparation/LOCAL_RECORD.md',
          'physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/QUANTIFIED_PREPARATION.md',
          'physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/quantified_preparation.json',
          'physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/ground_datum.json'])
