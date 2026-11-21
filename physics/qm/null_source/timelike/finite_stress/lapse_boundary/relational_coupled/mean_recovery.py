"""Exact resource inequalities and actual coefficient/log margins."""
import sympy as s
from common import *
base="physics/qm/null_source/timelike/finite_stress/lapse_boundary/";new=base+"relational_coupled/"
co=load(new+"coefficient_window.json");load(new+"ordering_domain.json");load(new+"source_budgets.json")
g=box(co["g_on_patch"]);d3=box(co["d3_on_patch"])
require(below(g,".05") and above(g) and above(d3,".01") and above(box(co["d1_on_patch"])),"Actual positive confining branch")
history="physics/qm/null_source/timelike/joint_history/history.json"
A=box(load(history)["cases"]["unfiltered"]["A"]);J=interval("-.01",".01")
def harmonic(k):
 n=iv.mpf(k);return iv.ln(n)+iv.euler+1/(2*n)-1/(12*n*n)+1/(120*n**4)+interval(-1,0)/(252*n**6)
def g_at(k):
 return iv.mpf(19)/120+iv.ln(A*A/4)/8+iv.euler/4-harmonic(k)/4+J/4
require(below(g_at(2),3) and below(g_at(100000),0),"All positive-g K lie below 100000; g<3")
maxK=100000;hmax=iv.exp(-19980);M=iv.exp(50)
C=19+15*(iv.ln(A*A/4)+2*iv.euler)
can=(C-1)/240
rad=iv.mpf(maxK*(maxK+1)*(maxK*(maxK+1)-1))/4+13/8
U0=box(load(history)["fixed_U0"])
d0budget=20*(A*iv.exp(J))**4*U0+3*20*(A*iv.exp(J))**2/2+iv.mpf(".01")/8+abs(can)+rad
require(below(d0budget,M),"Full d0 including radiation subtraction")
require(above(3*19*(A*iv.exp(J))**2/2-3+iv.mpf(29)/120),"Uniform positive d1")
require(below(iv.mpf(59)/720+iv.mpf(3)/2,2),"Uniform |d3|<2")
a=1/(2*g);young=2/(3*iv.sqrt(3*d3))
require(below(young,4),"Cubic source Young constant")
require(below(M*hmax*hmax,2*a),"M2 inverse-moment condition")
# Multiply all mean inequalities by m^3: worst remainders increase with m.
scaled=a-M*hmax**2-young*iv.exp(90)*hmax**3
require(above(scaled,1) and above(iv.ln(scaled)+3*19980,59000),"Original and delta=1e-6 mean obstruction")
qthreshold=iv.mpf(1)/100
require(above(a-M*hmax**2-young*qthreshold**iv.mpf("1.5")-iv.exp(60)*hmax**3),"Necessary source q2 at least 1/(100m^2)")
tailmargin=iv.mpf(1)/6-M*hmax**2-2/(3*iv.sqrt(3))*iv.exp(90)*hmax**3-iv.exp(60)*hmax**3
require(above(tailmargin,iv.mpf(1)/12),"Third-moment necessary coefficient")
kap,Q,d=s.symbols("kap Q d",positive=True)
minimizer=s.sqrt(Q/(3*d))
require(s.simplify((d*kap**3-kap*Q).subs(kap,minimizer)+2*Q**s.Rational(3,2)/(3*s.sqrt(3*d)))==0,"Exact cubic Young optimization")
m,ii,aa,al,mm=s.symbols("m I a alpha M",positive=True)
poly=aa*al**2*ii**2/m-mm*ii
require(s.simplify(s.diff(poly,ii).subs(ii,1/m)-(2*aa*al**2/m**2-mm))==0,"Inverse-moment minimization boundary")
L,m0=s.symbols("L m0",positive=True);weight=(m-m0)/(L-m0)
require(s.simplify((1-weight)*m0+weight*L-m)==0,"Rare-tail exact mean")
require(s.limit(weight*L**3/L**2,L,s.oo)==m-m0,"Rare-tail cubic growth")
finish("mean_recovery.py",dict(
 original_frame_all_terms_retained=True,
 state_class="normal mixed/entangled; stated finite positive budgets and legitimate snapshot expectation",
 K65536_same_source_or_delta1e6_preparation_mean_recovery="REJECTED within declared budget class",
 same_mean_geometry_m="h_i < exp(-19980)",old_bulk_Pu_budget="abs(mean) < exp(60)",
 required_H_mean_strict_lower="exp(59000)",ordering_range="all eta>=-1/4, specified Friedrichs realization",
 source_Q2_sqrt_necessary_lower="1/(100*h_i^2)",
 all_positive_g_K_third_moment_necessary_lower="1/(36*h_i^3)",
 third_moment_relative_necessary_lower="1/(36*h_i^6)",
 low_K_inverted_potential_rare_tail_compensation_exists=True,
 bounded_relative_second_moment_controls_third_moment=False,
 old_mean_SCE_contradicted=False,all_quantum_gravity_or_all_preparations_excluded=False),
 [history,new+"coefficient_window.json",new+"ordering_domain.json",new+"source_budgets.json",
 new+"SNAPSHOT_DOMAIN.md",new+"LENS_EVOLUTION.md",base+"ACTION_LIFT.md"],proof="MEAN_RECOVERY.md")
