"""Independent admitted slab and actual/reference spatial covariance bound."""
import sympy as s
from common import finish,require,iv,interval,outward,above,below,load,box
from model import HISTORY,chart,extrema,parameters
sp='physics/qm/null_source/timelike/finite_stress/lapse_boundary/conformal_action/spatial_noise.json'
local='physics/qm/null_source/timelike/finite_stress/lapse_boundary/conformal_action/local_autonomous.json'
ref=load(sp);app=load(local)
rows,du=chart(0,100000000)
require(above(extrema(rows,'kappa'),'.9') and below(extrema(rows,'kappa'),'1.1'),'whole 1e8 slab kappa')
require(above(extrema(rows,'sqrt_disc'),'4e11'),'whole slab discriminant margin')
A,U=parameters();V=2*iv.pi**2
for row in rows:
 require(above(U*row['a2'],'2.9') and below(U*row['a2'],'3.1'),'coarse curvature range')
 require(above(V*row['a2'],'3e11'),'coarse volume margin')
u,A0,y=s.symbols('u A0 y',positive=True)
kap=s.sqrt(A0*A0*s.exp(2*u)*y-1)
require(s.simplify(s.diff(s.atan(kap),u)-1/kap)==0,'explicit vacuum clock')
L=10000;M=L//2;C=iv.mpf(2)/(9*V);delta=iv.mpf(1)/600
gamma=iv.mpf('.01')/(4*iv.mpf('.9')**3*iv.mpf('4e11'))
S2=4*(M*(M+1)*(2*M+1)//6-1)
S3=8*((M*(M+1)//2)**2-1)
S4=16*(M*(M+1)*(2*M+1)*(3*M*M+3*M-1)//30-1)
tail=(2/delta)**12/(22*iv.mpf(L)**11)
phase=C*gamma**2*S4
eps=iv.sqrt(phase+C*tail)
require(below(eps,'1e-5'),'actual/reference fixed-smearing error')
var=box(ref['variance_bounds']);rms=iv.sqrt(var)
Smax=(iv.exp(iv.mpf('.02'))*box(app['energy_record']['common_energy_band'])).b
appeps=iv.sqrt(C*(gamma**2*(S4+4*Smax*S3+4*Smax**2*S2)+tail))
require(below(appeps,'.05'),'apparatus uniform covariance comparison')
require(below(Smax+L,100000000),'actual device and source rectangle admitted')
lower=C*iv.cos(iv.mpf(2)/45)**2
require(above(lower),'nonzero actual spatial fluctuation')
R=s.diag(2,3);kapmat=R*R;O=s.Matrix([[0,1],[1,0]])
Or=R.inv()*O*R
require(Or.T*kapmat==kapmat*Or,'weighted self adjoint observable')
require(O*R!=R*O,'energy-changing observable transport necessary')
finish('projected_noise.py',{'admitted_total_excitation_ceiling_for_test':100000000,
 'source_observable_energy_band':L,'retained_frequencies':M-1,
 'kappa_bounds':outward(extrema(rows,'kappa')),
 'sqrt_discriminant_bounds':outward(extrema(rows,'sqrt_disc')),
 'test':'a^4 g(tau0(u))/kappa0(u) applied to physical density',
 'center_u':.55,'field_reference_RMS_bounds':outward(rms),
 'actual_reference_GNS_error_upper_bound':outward(eps),
 'actual_RMS_enclosure':[outward(rms-eps)[0],outward(rms+eps)[1]],
 'actual_variance_difference_upper_bound':outward(eps*(2*rms+eps)),
 'nonzero_actual_variance_lower_bound':outward(lower),
 'apparatus_max_conformal_energy':outward(Smax),
 'apparatus_reference_GNS_error_upper_bound':outward(appeps),
 'apparatus_actual_RMS_enclosure':[outward(rms-appeps)[0],outward(rms+appeps)[1]],
 'observable_defined_by_stabilized_finite_matrices':True,
 'sharp_time_full_operator_assumed':False,'unrestricted_local_stress_identification':False,
 'inhomogeneous_lapse_derivation_completed':False,
 'same_chart_infinite_energy_limit_claimed':False},
 inputs=[HISTORY,sp,local])
