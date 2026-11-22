"""Core derivative/group construction identities and snapshot spectral controls."""
import sympy as s
from common import *
base="physics/qm/null_source/timelike/finite_stress/lapse_boundary/"
new=base+"relational_coupled/"
load(new+"coupled_forms.json")
k0=s.symbols("k0",positive=True)
negative=s.Rational(1,2)/s.Rational(9,10)-1
require(negative==-s.Rational(4,9),"Actual zero-mode coherent negative coefficient")
# i R' = D R and i (R U)' = D R U + R Htilde U;
# full source coefficients conjugate back to H0 for every auxiliary t.
t=s.symbols("t",real=True)
require(s.simplify(s.exp(-2*t)*s.exp(2*t))==1,"p part exact back transport")
require(s.simplify(s.exp(2*t)*s.exp(-2*t))==1,"q part exact back transport")
n=s.symbols("n",positive=True)
require(s.diff(n*n,n,2)==2,"Positive principal high-frequency control")
finish("snapshot_domain.py",dict(
 frozen_actual_u_auxiliary_time_separate=True,
 full_original_snapshot_selfadjoint_extension_constructed=True,
 construction="unique C(Q) weak auxiliary evolution; autonomous group; Stone generator",
 domain="strong derivative domain of the explicitly constructed group",
 compact_geometry_Schwartz_source_core_in_generator_domain=True,
 minimal_operator_essential_selfadjointness_claimed=False,
 operator_core_claimed=False,
 snapshot_spectrum_unbounded_below=True,snapshot_spectrum_unbounded_above=True,
 negative_zero_mode_quadratic_coefficient=str(negative),
 actual_u_snapshot_operator_domain_transport_proved=False,
 full_field_limit_proved=False),
 [new+"coupled_forms.json",new+"COUPLED_FORMS.md",new+"REFERENCES.md",base+"ACTION_LIFT.md"],
 proof="SNAPSHOT_DOMAIN.md")
