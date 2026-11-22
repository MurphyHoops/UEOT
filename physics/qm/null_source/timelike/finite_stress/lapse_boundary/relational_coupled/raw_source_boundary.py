"""Source weighted-commutator and finite-mode raw-stress bounds."""
import sympy as s
from common import *
base="physics/qm/null_source/timelike/finite_stress/lapse_boundary/";new=base+"relational_coupled/"
load(new+"g_zero_boundary.json");load(new+"boundary_matching.json")
require(below(6*iv.mpf(5)**iv.mpf("1.5"),72),"p=3 source commutator agrees with old Schur budget")
require(below(iv.sqrt(3)+1/iv.sqrt(2),3),"Ladder source-energy norm bound")
require(below(3*iv.sqrt(2),5),"Quadratic source-energy norm bound")
x,y,R=s.symbols("x y R",positive=True)
fr=lambda z:z/(1+z/R)
require(s.simplify(fr(x)-fr(y)-(x-y)/((1+x/R)*(1+y/R)))==0,"Yosida commutator reduction")
t,t0=s.symbols("t t0",real=True)
require(s.diff(s.exp(t),t)==s.exp(t),"Integrable source-energy time coefficient")
p,d=s.symbols("p d",positive=True)
Cp=2*d*p*5**(p/2)
require(s.simplify(Cp.subs(p,2)-20*d)==0,"Second-moment commutator constant")
finish("raw_source_boundary.py",dict(
 scope="fixed finite K, selected homogeneous geometry, fixed p>=1, Friedrichs clock sector",
 source_energy_power_range="every fixed p>=1",source_commutator_constant="2*d*p*5^(p/2)",
 past_source_energy_bound="exp(C_p exp(tau0)); independent of geometry moments",
 scattering_complete_in_source_energy_weighted_Hilbert_spaces=True,
 moving_raw_source_energy_weighted_trace_limit=True,
 zero_mode_Q_moments_controlled=False,
 finite_K_raw_stress_essential_selfadjoint_realization=True,
 finite_K_raw_stress_absolute_first_moments_converge_if_p1_finite=True,
 finite_K_same_slice_raw_stress_sym_covariances_converge_if_p2_finite=True,
 covariance_requires_literal_unbounded_product_domain=False,
 arbitrary_fixed_raw_unbounded_observables_covered=False,
 AE_geometric_subtraction_terms_included_in_source_limit=False,
 uniform_in_K_estimates=False,two_time_CTP_or_fullfield_limit=False),
 [new+"g_zero_boundary.json",new+"boundary_matching.json",new+"all_sign_evolution.json",
 new+"REFERENCES.md",base+"ACTION_LIFT.md"],proof="RAW_SOURCE_BOUNDARY.md")
