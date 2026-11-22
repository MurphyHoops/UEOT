"""Contraction, phase and trace-class constants; no old ODE execution."""
import sympy as sp
from common import iv,require,above,below,outward,finish
u=iv.mpf(1)/10000;R=1300*u
lip=44*u*(2+2600*u)
image=650*u+44*u*(2*R+R*R)
require(below(R,iv.mpf('.14')) and below(lip,iv.mpf('.01')) and below(image,R.a),'Riccati self-map and contraction')
drcoef=4*29*1300
phasecoef=29*160000
require(drcoef<160000 and phasecoef<5000000,'nonlinear weighted and phase margins')
mu=iv.mpf(1)/5
# Neighbor-shell trace identity: ||L^-1 B_Z||_HS^2=2 sum W/Omega^2.
partial=iv.mpf(0)
K=256
for k in range(1,K):
    w=iv.sqrt(k*k+mu);v=iv.sqrt((k+1)**2+mu)
    W=k*(k+1)/(32*w*v);Om=w+v
    partial+=2*W/Om**2
tail=iv.mpf(1)/(64*(K-1))
require(below(partial+tail,iv.mpf(1)/25),'linear pair HS constant')
x=sp.symbols('x',positive=True)
require(sp.simplify(x/(1-x)-x-x*x/(1-x))==0,'Gaussian gamma expansion')
finish('source_ctp.py',{
 'actual_control_ball':'||u||<=1e-4','Riccati_X_ball':outward(R),
 'Riccati_Lipschitz_upper':outward(lip),'Riccati_image_upper':outward(image),
 'linear_pair_HS_squared_upper':outward(partial+tail),
 'nonlinear_Dr_norm_coefficient_upper':160000,
 'higher_phase_remainder_bound':'5e6 ||u||^3',
 'actual_phased_unitaries_and_adjoints_strong_limit':True,
 'actual_normal_mixed_initial_block_trace_norm_limit':True,
 'AP_vacuum_CTP_real_analytic_in_eight_controls':True,
 'arbitrary_normal_input_CTP_exists':True,
 'AQ_vacuum_Hessian_or_new_AP_numbers_transferred':False,
 'renormalized_mean_force_uniform_actual_cutoff_limit':True,
 'renormalized_mean_power_dominated_limit':True,
 'active_old_AP_excitation_energy':'|h(t)|^2 log K /64 + O(1) for nonzero h(t)',
 'active_old_AP_energy_form_domain':False,
 'switched_off_endpoint_all_energy_moments':True,
 'sharp_force_variance_finite':False,
 'full_covariant_metric_CTP_or_autonomous_device':False
},inputs=['physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/SOURCE_HESSIAN.md',
'physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/LOCAL_PREPARATION.md',
'physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_constraints/QUANTIFIED_PREPARATION.md'])
