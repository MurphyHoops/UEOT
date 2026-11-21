"""Outward finite-flight certificate and exact positive delta scattering algebra."""
import sympy as s
from common import finish,require,iv,interval,outward,above,below
from model import HISTORY,chart,extrema
p,alpha=s.symbols('p alpha',positive=True)
r=-s.I*alpha/(p+s.I*alpha);t=p/(p+s.I*alpha)
require(s.simplify(t-1-r)==0,'continuity')
require(s.simplify(s.conjugate(r)*r+s.conjugate(t)*t-1)==0,'all channels')
require(s.simplify(s.I*p*t-s.I*p*(1-r)-2*alpha*t)==0,'delta jump')
p0=iv.mpf(10000);width=iv.mpf(10);pm=p0-width/2;pp=p0+width/2
em=pm**2/2;ep=pp**2/2
f_all=iv.exp(interval('-0.01','0.01'))
rows,du=chart((f_all*em).a,(1+f_all*ep).b)
tau=iv.mpf(0);bp=iv.mpf(0)
for row in rows:
    f=iv.exp(row['u']-iv.mpf('0.55'))
    tau+=du*f/row['kappa']
    bp+=du*f*f/(2*row['kappa']**3*row['sqrt_disc'])
eg=(ep-em)**2*bp/8
require(above(tau,'0.019') and below(tau,'0.023'),'finite flight time')
require(below(eg,'0.001'),'geometric spectral error')
D0=2*iv.sqrt(2*width)/iv.pi;D1=2*iv.sqrt(2/width)
D2=2*iv.pi*iv.sqrt(2)/width**iv.mpf('1.5')
B1=D1+D0/(2*pm);B2=2*D2+D1/pm+D0/pm**2
def tail(d,tt):
    return (B2/(iv.sqrt(3)*d**iv.mpf('1.5'))+
     3*tt*B1/(iv.sqrt(5)*d**iv.mpf('2.5'))+
     3*tt**2*D0/(iv.sqrt(7)*d**iv.mpf('3.5')))/iv.sqrt(2*iv.pi)
ein=iv.sqrt(2)*tail(iv.mpf(100),iv.mpf(0))
distance=tau*pm-100
require(above(distance),'controller has passed')
flight=iv.sqrt(2)*tail(distance,tau)
rmin=p0*p0/(pp*pp+p0*p0)
gap=rmin-eg-flight
require(above(gap,'0.49'),'actual positive reflection record')
v2=width**2*(iv.mpf(1)/12-1/(2*iv.pi**2))
v4=width**4*(iv.mpf(1)/80-1/(4*iv.pi**2)+3/(2*iv.pi**4))
mu=(p0*p0+v2)/2
var=p0*p0*v2+(v4-v2*v2)/4
finish('delta_scattering.py',{
 'apparatus_energy_band':outward(interval(em.a,ep.b)),
 'full_total_excitation_band':outward(interval((f_all*em).a,(1+f_all*ep).b)),
 'effective_flight_time_bounds':outward(tau),'distance_after_crossing_bounds':outward(distance),
 'incoming_product_norm_error_bound':outward(ein),
 'finite_flight_norm_error_bound':outward(flight),
 'geometry_phase_norm_error_bound':outward(eg),
 'source_reflection_probability_lower_bound':outward(gap),
 'apparatus_mean_energy_bounds':outward(mu),'apparatus_energy_variance_bounds':outward(var),
 'all_channels_retained':True,'initial_product_state_exact':False,
 'readout':'compressed joint momentum-sign effects with complete Lueders instrument',
 'reader_autonomous':False,'four_dimensional_smooth_action':False},inputs=[HISTORY])
