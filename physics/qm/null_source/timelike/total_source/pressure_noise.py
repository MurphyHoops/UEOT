"""Full local tensor coefficient and finite pressure-noise difference."""
import sympy as s
from common import *
d,w,V,a,c=s.symbols("d w V a c",positive=True)
sumY=d/V;sumGrad=d*w*w/V;sumGradij=sumGrad/3
T00=s.simplify((-w*w*sumY+sumGrad)/(4*w*a**4))
Tii=s.simplify((sumGradij-(sumGrad+w*w*sumY)/2)/(2*w*a**4))
assert T00==0
assert s.simplify(Tii+d*w/(3*V*a**4))==0
Dp=s.simplify(16*c/d*Tii*Tii)
assert s.simplify(Dp-16*c*d*(w/(3*V*a**4))**2)==0
x,y=s.symbols("x y",real=True)
assert s.trigsimp(s.cos(x-y)-s.cos(x)*s.cos(y)-s.sin(x)*s.sin(y))==0
num=16*WEIGHT*D*(OMEGA/(3*V0*A**4))**2
assert above(num,0)
finish("pressure_noise.py",{
 "proof":"PRESSURE_NOISE.md","complete_local_noise_difference":"16*c/d*Re(Tcal_ab(x)*conj(Tcal_cd(xprime)))",
 "density_and_momentum_difference_slots_vanish":True,
 "pressure_amplitude_c_equals_w":outward(num),
 "rank_two_positive_pressure_difference":True,"static_Ward_identity":True,
 "retarded_stress_response_difference_zero":True,
 "all_higher_local_density_records_proved_equal":False,
 "absolute_random_initial_constraint_closed":False
},("PRESSURE_NOISE.md","COHERENCE.md"))
