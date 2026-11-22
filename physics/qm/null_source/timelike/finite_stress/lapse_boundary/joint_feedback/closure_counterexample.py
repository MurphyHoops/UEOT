"""Exact phase-pair constants and actual-input resource margins."""
import sympy as s
from common import *
P="physics/qm/null_source/timelike/finite_stress/lapse_boundary/relational_coupled/"
n=load(P+"negative_recovery.json")
b0=box(n["kinetic_b0"])
require(above(b0,3) and below(b0,4),"Actual negative kinetic coefficient")
require(n["actual_K"]==131072 and n["old_log_h_upper"]==-19980,"Actual quiet preparation")
Z=s.symbols("Z",nonnegative=True)
G=(s.Rational(1,4)+Z)/(s.Rational(1,4)-Z)**2
require(s.simplify(s.diff(G,Z)-(s.Rational(3,4)+Z)/(s.Rational(1,4)-Z)**3)==0,"Evenized inverse-square derivative")
require(s.simplify(s.diff(G,Z).subs(Z,0))==48,"Minimum derivative at zero")
# Positive coefficients prove G' >= 48 on 0 <= Z < 1/64.
num=s.factor((s.diff(G,Z)-48)*(s.Rational(1,4)-Z)**3)
require(s.expand(num)==48*Z**3-36*Z**2+10*Z,"Exact derivative margin")
require(s.Rational(10)-36*s.Rational(1,64)>0,"Derivative margin nonnegative")
PA=iv.exp(-exact(2)/15)/4;PB=iv.exp(-exact(18)/7)/4
varX=PA*PB*(exact(3)/16)**2
ds=48*varX/4096
ds_formula=exact(27)*iv.exp(-exact(284)/105)/(2**20)
require(below(abs(ds-ds_formula),"1e-90"),"Variance bound normalization")
require(s.Rational(5,32768)<s.Rational(1,6000),"Extra kinetic budget")
cs=iv.sqrt(3)*iv.exp(-exact(2)/3)/800
jet=6*cs*ds
require(above(jet,"1e-9"),"Actual bounded second-jet coefficient")
hmax=iv.exp(-19980)
require(below(4*hmax**4/6000,1),"Shared root bracket survives added phase")
h,R=s.symbols("h R",positive=True);w=h/(2*R-h)
require(s.simplify((1-w)*h/2+w*R-h)==0,"Packet mean matched for all R")
# Ordinary product-current expansion, with noncommutative source matrices.
Hs,Hsp,sg=s.symbols("Hs Hsp sigma",commutative=False)
I1,I2,Jp,Jm=s.symbols("I1 I2 Jp Jm",commutative=True)
comm=lambda a,b:a*b-b*a
second=lambda J:-s.I*comm(I1*Hsp+J*Hs,sg)-I2*comm(Hs,comm(Hs,sg))
require(s.expand(second(Jp)-second(Jm)+s.I*(Jp-Jm)*comm(Hs,sg))==0,"Same first jet, different second jet")
finish("closure_counterexample.py",dict(
 actual_K=n["actual_K"],
 same_complete_raw_source=True,same_full_kappa_probability_law=True,
 same_sigma_tau_I2=True,same_initial_kappa_velocity=True,
 same_geometric_momentum_after_one_shared_root=True,
 extra_phase_kinetic_upper="5 h/32768 < h/6000",
 covariance_d_s_lower=outward(ds),
 bounded_source_second_jet_times_h_squared_lower=outward(jet),
 next_raw_pressure_coefficient_nonzero_requires_actual_pressure_witness=True,
 kinematic_means_are_sufficient_for_unique_feedback=False,
 joint_unitary_rejected=False,
 positive_time_bound_proof="POSITIVE_WINDOW.md",
 apparatus_constructed=False),
 [P+"negative_recovery.json",P+"NEGATIVE_RECOVERY.md",
 "physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_feedback/PRESSURE_WITNESS.md",
 "physics/qm/null_source/timelike/finite_stress/lapse_boundary/joint_feedback/POSITIVE_WINDOW.md"])
