"""Positive local-action reduction and outward, uniform finite-time record bounds."""
import sympy as s
from common import finish,require,iv,interval,outward,above,below,load
from model import HISTORY,chart,extrema
old=['physics/qm/null_source/timelike/total_source/autonomous.json',
     'physics/qm/null_source/timelike/total_source/fieldspace.json']
for path in old:load(path)
x=s.symbols('x',real=True);k=s.Function('k')(x);J=(1-k*k)**s.Rational(1,4)
vg=-(s.diff(k,x)**2+k*s.diff(k,x,2))/(4*(1-k*k))-3*k*k*s.diff(k,x)**2/(8*(1-k*k)**2)
require(s.simplify(s.diff(J,x,2)/(2*J)-vg)==0,'half-density potential')
f,E,K,a=s.symbols('f E K a',positive=True)
rho=(E+f*K)/a**4;p=(E/3+f*K)/a**4
require(s.simplify(-2*f*s.diff(rho,f)+a*s.diff(rho,a)+3*(rho+p))==0,'full stiff Ward')
k0=iv.mpf('.01');d0=1-k0*k0
k1=k0*iv.pi/98;k2=k0*iv.pi**2/(2*49**2);k3=3*k2
Cg0=(k1*k1+k0*k2)/(4*d0)+3*k0*k0*k1*k1/(8*d0*d0)
Cg1=(3*k1*k2+k0*k3)/(4*d0)+(k1*k1+k0*k2)*k0*k1/(2*d0*d0)+3*(k0*k1**3+k0*k0*k1*k2)/(4*d0*d0)+3*k0**3*k1**3/(2*d0**3)
# ||r'||_1=2 r(0). A lower bound on normalizing integral:
# exp[-1/(1-x²)] >= exp[-4/3] on [-1/2,1/2].
# Hence 2 r(0) <= 2 exp(1/3) < 3.
require(below(2*iv.exp(iv.mpf(1)/3),3),'mollifier derivative')
def moments(center,width):
 v2=width**2*(iv.mpf(1)/12-1/(2*iv.pi**2))
 v4=width**4*(iv.mpf(1)/80-1/(4*iv.pi**2)+3/(2*iv.pi**4))
 return (center**2+v2)/2,center**2*v2+(v4-v2*v2)/4
def record(name,wc,wp,d,source_low,source_high,threshold):
 wc=iv.mpf(wc);wp=iv.mpf(wp);distance=iv.mpf(d)
 pm=10000-wc/2;pp=10000+wc/2;pr=wp/2;ps=iv.mpf(1001)
 lows=[];highs=[]
 for lo,hi in [source_low,source_high]:
  mn=iv.mpf(0) if lo<=0<=hi else min(iv.mpf(lo)**2,iv.mpf(hi)**2)
  mx=max(iv.mpf(lo)**2,iv.mpf(hi)**2)
  lows.append((pm**2+mn)/2);highs.append((pp**2+mx+pr**2)/2)
 km=min(t.a for t in lows);kp=max(t.b for t in highs)
 band=interval(km,kp);width=kp-km;mid=(kp+km)/2
 fall=iv.exp(interval('-.02','.02'))
 rows,du=chart((fall*band).a,(fall*band).b)
 tau=iv.mpf(0);bp=iv.mpf(0)
 # Whole-band tau encloses the ONE midpoint-defined tau_*.
 for row in rows:
  ff=iv.exp(-2*(row['u']-iv.mpf('.55')))
  tau+=du*ff/row['kappa']
  bp+=du*ff*ff/(2*row['kappa']**3*row['sqrt_disc'])
 geo=width**2*bp/8
 S=ps*ps+pr*pr;P=ps*pr
 C0=(k0*k0*S+2*k0*P)/(2*d0)+Cg0
 C1=k1*(k0*S+(1+k0*k0)*P)/(d0*d0)+Cg1
 B0=2*iv.sqrt(2*wc)/iv.pi;B1=2*iv.sqrt(2/wc);B2=4*iv.pi*iv.sqrt(2)/wc**iv.mpf('1.5')
 ein=C0*iv.sqrt(50/iv.pi)/50*(B2/pm+3*B1/(2*pm**2)+B0/pm**3)
 vc=wc*wc*(iv.mpf(1)/12-1/(2*iv.pi**2))
 dyn=tau*C1*iv.sqrt(iv.pi**2/wc**2+tau**2*vc)
 beta=16*iv.pi/(3*(wp*distance)**3)
 err=ein+dyn+geo+beta;gap=1-2*err
 require(above(tau,'.015'),'whole pulse passed')
 require(below(ein,'.003') and below(geo,'.003'),'controlled preparation and geometry')
 require(above(gap,'.4'),'uniform actual readout contrast')
 if name=='energy':
  require(above(lows[1]-highs[0]),'disjoint total energy classes')
  require(above(gap,'.48'),'energy-class contrast')
 # Exact packet energy moments; balanced mixture retains between-code term.
 mclock,vclock=moments(iv.mpf(10000),wc)
 mprobe,vprobe=moments(iv.mpf(0),wp)
 msource=[];vsource=[]
 for lo,hi in [source_low,source_high]:
  mm,vv=moments(iv.mpf(lo+hi)/2,iv.mpf(hi-lo));msource.append(mm);vsource.append(vv)
 mean=mclock+mprobe+(msource[0]+msource[1])/2
 var=vclock+vprobe+(vsource[0]+vsource[1])/2+(msource[1]-msource[0])**2/4
 return {'source_bands':[source_low,source_high],
 'controller_momentum_width':outward(wc),'probe_width':outward(wp),
 'threshold':threshold,'probe_threshold_distance':d,
 'class_energy_bands':[outward(interval(lo.a,hi.b)) for lo,hi in zip(lows,highs)],
 'common_energy_band':outward(band),'common_midpoint':outward(mid),
 'kappa_bounds':outward(extrema(rows,'kappa')),'tau_bounds':outward(tau),
 'potential_norm_bound':outward(C0),'potential_Lipschitz_bound':outward(C1),
 'incoming_norm_error_bound':outward(ein),'dynamics_norm_error_bound':outward(dyn),
 'geometry_phase_norm_error_bound':outward(geo),'probe_tail_bound':outward(beta),
 'total_effect_error_bound':outward(err),'readout_contrast_lower_bound':outward(gap),
 'initial_contrast_upper_bound':outward(2*ein),
 'balanced_total_K_mean':outward(mean),'balanced_total_K_variance':outward(var)}
sign=record('sign',10,100,'.048951',[-1001,-999],[999,1001],0)
energy=record('energy',24,220,'.02445',[-1,1],[999,1001],-.0245)
finish('local_autonomous.py',{'sign_record':sign,'energy_record':energy,
 'action_four_dimensional_classically_local':True,
 'quantization':'three homogeneous scalar degrees plus declared conformal sector',
 'full_interacting_four_dimensional_field_quantization':False,
 'controller_quantized_and_energy_retained':True,
 'input_uniform_over_source_code_and_normal_references':True,
 'complete_energy_class_calibration_before_readout':True,
 'initial_preparation_autonomous':False,'terminal_reader_autonomous':False,
 'terminal_reader_total_energy_conserving':False,
 'all_scattering_channels_and_records_retained':True},inputs=[HISTORY]+old)
