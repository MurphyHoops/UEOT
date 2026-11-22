"""Exact form bounds, interpolation exponents and finite-K inverse margins."""
import sympy as sp
from common import iv,load,require,below,outward,finish
p='physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/'
load(p+'clock_actuator.json');load(p+'quantified_preparation.json')
y0,y1,v0,v1=sp.symbols('y0 y1 v0 v1',real=True)
A=y0*y0+y1*y1;B=v0*v0+v1*v1
complete=A/2+(y0*v0+y1*v1)/2+B/4
sq=3*((y0+2*v0/3)**2+(y1+2*v1/3)**2)/8
require(sp.expand(complete-A/8-B/12-sq)==0,'uniform interaction lower form bound')
N=sp.Integer(7)
meanexp=(N-3)/2;derivexp=(N-5)/2
require(meanexp==2 and derivexp==1,'energy-form interpolation exponents')
old=iv.mpf('.004096');extra=10**6*iv.mpf('1e-7');L=old+extra
require(below(L,iv.mpf(1)/2) and below(iv.mpf(1)/2+L,1),'actual mean map contraction and self-map')
eta=iv.mpf(1)/10**13;ymax=eta**2/2
require(below(ymax,iv.mpf('5e-23')),'common finite-K code target')
finish('actuator_means.py',{
 'cutoff_scope':'each fixed K>=2; K=1 excluded',
 'observable_split':'body plus entire interaction; free X/Y excluded from eight targets',
 'high_order_parametrix_order':int(N),
 'norm_error_order':'g^8','program_derivative_norm_error_order':'g^7',
 'form_mean_error_order':str(meanexp),'form_derivative_error_order':str(derivexp),
 'actual_C1_mean_convergence':True,
 'actual_SO4_zero_program_dipoles':True,
 'source_reference_inverse_bound':'1e6',
 'required_actual_Jacobian_difference':'<=1e-7 uniformly on ||u||<=1e-16',
 'actual_inverse_contraction_upper':outward(L),
 'actual_target_ball_radius':'5e-23',
 'combined_K64_record_and_mean_contract':'there exists 0<g<min(g_*(64),1e-40), one common u_g',
 'chosen_g_1e_40_proved_below_IFT_threshold':False,
 'g_star_numerically_bounded':False,
 'same_state_complete_binary_gap_lower':'2.69e-30 under the combined existence contract',
 'fixed_g_energy_upper_1_02e81_transferred_to_existence_contract':False,
 'total_source_or_free_controller_means_repaired':False,
 'finite_g_interaction_exactly_off':False,
 'uniform_K_C1_or_interacting_continuum_proved':False,
 'source_sign_is_a_fullstress_or_geometry_record':False
},inputs=[p+'CLOCK_ACTUATOR.md',p+'clock_actuator.json',p+'QUANTIFIED_PREPARATION.md',p+'quantified_preparation.json',p+'JOINT_PREPARATION.md'])
