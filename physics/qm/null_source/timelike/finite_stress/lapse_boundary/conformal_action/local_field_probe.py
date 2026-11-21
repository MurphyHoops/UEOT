"""Exact local action rows, finite-time gain bound and Gaussian calibration."""
import sympy as s
from common import finish,require,iv,outward,above,below
t=s.symbols('t',real=True)
rot=s.Matrix([[s.cos(t),s.sin(t)],[-s.sin(t),s.cos(t)]])
C=s.Matrix([[0,0],[-1,0]])
B=s.simplify(rot.T*C*rot)
target=s.Matrix([[s.sin(t)*s.cos(t),s.sin(t)**2],[-s.cos(t)**2,-s.sin(t)*s.cos(t)]])
require(s.simplify(B-target)==s.zeros(2),'actual demodulated interaction row')
require(s.simplify((B.T*B).trace())==1 and s.simplify(B.det())==0,'exact generator norm')
O=s.zeros(2);G=O.row_join(C).col_join(C.row_join(O))
par=s.diag(1,1,-1,-1)
require(par*G*par==-G,'source/probe exchange parity')
N,r,phi,psi,vol=s.symbols('N r phi psi vol')
Lint=-N*vol*r*phi*psi
require(s.diff(Lint,N)==-vol*r*phi*psi,'retained lapse interaction row')
require(s.diff(Lint,N,2)==0,'NN contact')
for var,value in [(r,-vol*phi*psi),(phi,-vol*r*psi),(psi,-vol*r*phi)]:
 require(s.diff(Lint,N,var)==value,'mixed interaction contact')
# Heat E convention and r-dependent a4.
curv=s.symbols('R')
sx=s.Matrix([[0,1],[1,0]]);E=-curv*s.eye(2)/6-r*sx;E0=-curv*s.eye(2)/6
require(s.expand(s.trace(E*E-E0*E0)/2)==r*r,'actual paired r^2 heat coefficient')
require(s.trace(E-E0)==0,'linear curvature/total derivative trace')
ct=s.symbols('c_r')
require(s.diff(ct*N*vol*r*r,r)==2*ct*N*vol*r,'same control counterterm row')
T=iv.mpf('.2');coupling=iv.mpf('.2');sigma=iv.mpf('.1')
L=coupling*T/2
odd=(iv.exp(L)-iv.exp(-L))/2-L
even=(iv.exp(L)+iv.exp(-L))/2-1
first_lower=coupling*T/4*iv.exp(-iv.mpf(4)/3)*iv.cos(T)**2
gain=first_lower-odd
noise_low=(1-even)**2/2+sigma*sigma
noise_high=(1+even)**2/2+sigma*sigma
require(above(gain) and below(even,1),'nonzero actual gain and positive probe margin')
reader_energy=1/(8*sigma*sigma)
# Effect characteristic functions: probe and reader variances add.
u,mu,v,sig=s.symbols('u mu v sigma',real=True)
require(s.expand(-u*u*v/2-u*u*sig**2/2+u*u*(v+sig**2)/2)==0,'exact added variance')
finish('local_field_probe.py',{'local_interaction':'-integral sqrt(-g) r phi psi',
 'normal_state_gate':'actual smooth coupled KG Cauchy map on compact S3',
 'actual_advanced_Green_pullback':'(f_g,h_g)=(0,g)-R_r E_r^adv(0,g)',
 'Gaussian_effect_is_not_source_Luders_instrument':True,
 'coupling_duration_model_time':'.2','coupling_amplitude':'.2',
 'terminal_reader_sigma':'.1','spatial_support':'entire compact S3 in the explicit example',
 'Dyson_L_upper_bound':outward(L),'odd_transfer_remainder_upper_bound':outward(odd),
 'even_probe_row_remainder_upper_bound':outward(even),
 'actual_source_q_transfer_absolute_lower_bound':outward(gain),
 'probe_and_reader_added_variance_interval':[outward(noise_low)[0],outward(noise_high)[1]],
 'terminal_reader_total_free_energy_increase':outward(reader_energy),
 'constant_spatial_actual_canonical_cutoff_channel_limit':True,
 'general_spatial_coupling_cutoff_limit_proved':False,
 'counterterm_heat_density_extra':'r^2/(16 pi^2)',
 'external_controller_work_retained':True,
 'physical_controller_and_terminal_reader_autonomous':False,
 'spatial_lapse_gravitational_feedback_solved':False},
 inputs=['physics/qm/null_source/timelike/finite_stress/lapse_boundary/conformal_action/SMOOTH_PREPARATION.md',
         'physics/qm/null_source/timelike/finite_stress/lapse_boundary/conformal_action/STATIC_NORMALITY.md'])
