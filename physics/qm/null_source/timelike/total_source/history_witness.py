"""Rational/interval balanced-pulse and infinite-mode witness; no ODE."""
import sympy as s
from mpmath import iv
from common import *
z=s.symbols("z")
C=s.Poly(2*z**3-14*z**2+21*z-6,z)
assert C.count_roots(1,s.oo)==2
assert C.count_roots(s.Rational(159,100),s.Rational(8,5))==1
assert C.count_roots(s.Rational(503,100),s.Rational(126,25))==1
P=4*z**4-12*z**3+6*z**2
assert s.expand(s.diff(P,z)-P+2*z*C.as_expr())==0
def tay(t,n):return sum(t**j/s.factorial(j) for j in range(n+1))
assert tay(s.Rational(135,100),5)>s.Rational(50,13)
assert tay(s.Rational(59,100),4)>s.Rational(9,5)
assert tay(s.Rational(403,100),10)>56
assert 2*s.Rational(77,100)*s.Rational(237,100)**2*s.Rational(26,100)<s.Rational(9,4)
assert P.subs(z,s.Rational(8,5))>-s.Rational(38,5)
assert P.subs(z,s.Rational(126,25))<1198
assert 4*(s.Rational(599,28)+s.Rational(38,9))-4==s.Rational(6203,63)<100
eps=exact(1)/1000;h=1-eps;delta=iv.pi/(8*OMEGA)
K=iv.pi*eps/(2*h)
remainder=iv.pi*eps**2/(2*h)+K**2/(2*(1-K))
assert below(remainder,".000003")
beta_low=iv.pi/(6000*iv.sqrt(2))-exact(".000003")
assert above(beta_low,exact(33)/100000)
beta_upper=K/(1-K);assert below(beta_upper,exact(1)/600)
V_l1=9*eps/(h*delta)+27*eps**2/(4*h**2*delta)
Vp_l1=(100*eps/h+81*eps**2/h**2+243*eps**3/(8*h**3))/delta**2
assert below(V_l1,exact(1)/25) and below(Vp_l1,exact(39)/20)
B=iv.exp(V_l1/OMEGA)*(Vp_l1+V_l1**2)/4
assert below(B,exact(1)/2)
assert s.Rational(85,83)*(s.Rational(39,20)+s.Rational(1,625))/4<s.Rational(1,2)
rest=iv.exp(-exact(5)/54);assert above(rest,".9")
factor=exact(".9")*8*(exact(33)/100000)**2/(1+exact(1)/360000)**3
assert above(factor,".00000075")
contrast=exact(".00000075")*WEIGHT
finish("history_witness.py",{
 "proof":"HISTORY_WITNESS.md","epsilon":"1/1000",
 "zero_mode_relative_propagator_exact_identity":True,
 "beta2_strict_lower":"33/100000","beta2_strict_upper":"1/600",
 "Dyson_plus_generator_remainder_upper":outward(remainder),
 "V_L1_upper":outward(V_l1),"Vprime_L1_upper":outward(Vp_l1),
 "B_upper":outward(B),"rest_overlap_strict_lower":outward(rest),
 "full_field_contrast_strict_lower_c_equals_w":outward(contrast),
 "UV_beta_rapid_decay_and_Shale_HS_proved":True,
 "state_independent_infinite_vacuum_phase_claimed_unrenormalized":False,
 "prescribed_pair_claimed_on_shell_or_instrument_signal":False
},("HISTORY_WITNESS.md","INFLUENCE.md"))
