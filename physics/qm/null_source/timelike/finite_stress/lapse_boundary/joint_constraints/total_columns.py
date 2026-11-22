"""Outward full-source Jacobian rank and exact leading exchange identity."""
import sympy as sp
from common import iv,load,require,above,below,outward,finish
p='physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/'
load(p+'actuator_means.json');load(p+'quantified_preparation.json')
a=iv.sqrt(3);S=iv.sin(a*iv.pi);C=iv.cos(a*iv.pi);d=iv.cos(iv.mpf(2)/5);m=iv.mpf(14)/1875
ul=1-(iv.mpf(3)/2+4/d)*m
ru=1+2*m/d
vl=7-(iv.mpf(21)/2+12/d)*m
vu=3+4/d**2
qu=1+(2/d+4/d**2)*m
positive=ul-C*ru;negative=C*ul-ru
require(above(positive) and below(negative,0),'determinant signs')
detlo=3*(positive*vl+negative*qu)
require(above(detlo,iv.mpf('4.5')),'strict controller determinant bound')
fro2=(abs(S)*a)**2+(C*vu+qu)**2+(3*(ru-C*ul))**2+(3*abs(S)*vu/a)**2
frob=iv.sqrt(fro2)
require(below(frob,13),'controller matrix Frobenius upper')
scale=130/iv.sqrt(iv.mpf(6)/5)
inv=frob/(detlo*scale)
require(below(inv,iv.mpf('.0245')) and below(inv*6,1),'retained controller dominates independent body norm')
totinv=inv/(1-6*inv)
require(below(totinv,iv.mpf('.03')),'full-source inverse bound')
K=64;V0=2*iv.pi**2
vK=sum(iv.mpf(k*k)/iv.sqrt(k*k+iv.mpf(1)/5) for k in range(1,K+1))/(2*V0)
require(above(V0*vK/8,scale.b),'actual finite-K scale')
c,cp,z,zp,x,xp,F,Fp,v,u=sp.symbols('c cp z zp x xp F Fp v u')
Rprime=(-3*x-v*c*Fp*u/2)+(-4*c*zp+cp*(-z-v*F/2)+cp*z+c*zp)*u
J=x+c*zp*u
require(sp.expand(Rprime+3*J+v*(cp*F+c*Fp)*u/2)==0,'retarded controller exchange Ward row')
r0=iv.mpf('1e-16');x=58*r0;C0=iv.mpf('1e8')
app_remainder=2*C0*x*x
coefficient_budget=20*55*(4143+iv.mpf(9)/4*144)
require(below(coefficient_budget,iv.mpf('5e6')),'full spatial leading controller majorant')
actual_L=iv.mpf('.03')*(iv.mpf('4.096e-9')+app_remainder+iv.mpf('1e-7'))
require(below(actual_L,iv.mpf('3.2e-9')),'actual total mean contraction')
target=iv.mpf('5e-23')
require(below(iv.mpf('.03')*target+actual_L*r0,r0.a),'actual total target self-map')
programcoef=iv.mpf('.03')/(2*(1-actual_L))
require(below(programcoef,iv.mpf('.016')),'common code program norm')
finish('total_columns.py',{
 'K':64,'b_second_moment_upper':'14/1875',
 'U_over_sqrt3_lower':outward(ul),'R_upper':outward(ru),
 'V_lower':outward(vl),'V_upper':outward(vu),'Q_upper':outward(qu),
 'controller_inner_matrix_determinant_lower':outward(detlo),
 'controller_inner_matrix_Frobenius_upper':outward(frob),
 'actual_controller_scale':outward(V0*vK/8),
 'controller_inverse_norm_upper':outward(inv),
 'full_total_source_inverse_norm_upper':outward(totinv),
 'raw_controller_first_harmonic_response_survives_g_to_zero':True,
 'raw_tadpole_normal_ordered_away':False,
 'actual_total_eight_mean_map_C1_limit':True,
 'actual_normal_total_eight_projection_inverse_exists':True,
 'target_ball_radius':'5e-23','control_ball_radius':'1e-16',
 'leading_app_coefficient_budget_upper':outward(coefficient_budget),
 'leading_app_Jacobian_remainder_upper':outward(app_remainder),
 'actual_total_inverse_contraction_upper':outward(actual_L),
 'program_norm_eta2_coefficient_upper':outward(programcoef),
 'coupling_threshold_numerically_bounded':False,
 'combined_same_state_positive_complete_record_exists':True,
 'fixed_g_1e_40_claimed_to_meet_stronger_inverse':False,
 'combined_eta_1e_13_exists_for_some_g_below_threshold_and_1e_40':True,
 'eight_projection_vanishing_propagated_to_read_time':False,
 'raw_tadpole_Jacobian_is_renormalization_scheme_independent':False,
 'homogeneous_or_all_higher_modes_solved':False,
 'operator_constraints_or_full_Einstein_solution':False,
 'finite_cutoff_local_Ward_residual_dropped':False,
 'continuum_device_or_autonomous_pointer':False
},inputs=[p+'ACTUATOR_MEANS.md',p+'actuator_means.json',p+'CLOCK_ACTUATOR.md',p+'QUANTIFIED_PREPARATION.md',p+'quantified_preparation.json'])
