"""Discrete IMS algebra and polynomial propagation exponents."""
import sympy as s
from common import *
ur,ui,vr,vi,aa,bb,edge,d1,d2=s.symbols("ur ui vr vi aa bb edge d1 d2",real=True)
u=s.Matrix([ur+s.I*ui,vr+s.I*vi]);Aq=s.diag(aa,bb)
T=s.Matrix([[d1,-edge],[-edge,d2]])
lhs=(u.conjugate().T*Aq*T*Aq*u)[0]-s.re((u.conjugate().T*Aq**2*T*u)[0])
rhs=edge*(aa-bb)**2*(ur*vr+ui*vi)
assert s.simplify(s.expand(lhs-rhs))==0
x,y=s.symbols("x y",positive=True)
assert s.simplify((s.sqrt(x)+s.sqrt(y))**2-4*s.sqrt(x*y)-(s.sqrt(x)-s.sqrt(y))**2)==0
rows=[]
for q in range(1,7):
    beta=s.Rational(3*q,2)
    assert beta-1-s.Rational(3*(q-1),2)==s.Rational(1,2)
    assert s.simplify(beta*(1-s.Rational(2,3*q))-(beta-1))==0
    rows.append({"moment":q,"norm_time_power":str(beta),"moment_time_power":3*q})
finish("volume_moments.py",{
 "IMS_edge_identity_verified":True,"IMS_q2_constant":"1/4",
 "arbitrary_integer_q_induction":"beta=3q/2; K>=max(F0,2A/beta,(2B/beta)^beta)",
 "checked_exponent_instances":rows,
 "negative_mean_first_moment_C":outward(2*iv.sqrt(ALPHA*D)/3),
 "smooth_compact_energy_filter_preserves_all_polynomial_volume_moments":True,
 "mixed_volume_H_graph_norms_finite":True,
 "Gaussian_P_integration_finite":True,
 "finite_sections_are_proof_only":True,
 "weighted_energy_term_wrongly_assumed_nonpositive":False,
 "Schwartz_filter_integrated_against_exponential_bound":False,
 "semiclassical_narrowness_proved":False})
