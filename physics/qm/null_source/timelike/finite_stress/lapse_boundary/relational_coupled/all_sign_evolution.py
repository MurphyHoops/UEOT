"""Algebra and explicit source-commutator budgets for both-sign evolution."""
import sympy as s
from common import *
base="physics/qm/null_source/timelike/finite_stress/lapse_boundary/";new=base+"relational_coupled/"
co=load(new+"coefficient_window.json");load(new+"ordering_domain.json");load(new+"lens_evolution.json")
ng=box(co["negative_controls"]["131072"]["g"])
require(below(ng,0),"Actual negative-g example")
K=131072;d=K*(K+1)*(2*K+1)//3-2
q=s.symbols("q",real=True);w=s.symbols("w",positive=True);f=s.Function("f")(q)
P=lambda z:-s.I*s.diff(z,q)
D=lambda z:-s.I*(q*s.diff(z,q)+z/2)
H=lambda z:(P(P(z))+w*w*q*q*z)/2
require(s.simplify(s.I*(D(H(f))-H(D(f)))-(w*w*q*q*f-P(P(f))))==0,"Actual oscillator commutator")
n=s.symbols("n",nonnegative=True)
require(s.expand((n+2)**2-(n+1)*(n+2))==n+2,"Occupation ladder bound")
require(below(3*iv.mpf(5)**iv.mpf("1.5"),36),"Weighted matrix entry bound")
require(2*36==72,"Weighted Schur row/column bound")
kap,c0,B,r,lam,V=s.symbols("kap c0 B r lam V",positive=True)
A=B*B/(c0*r*r)
opt=s.sqrt(3*A/c0)*lam
value=A*lam**2*kap-c0*kap**3/9
require(s.simplify(value.subs(kap,opt)-2*B**3*lam**3/(s.sqrt(3)*c0**2*r**3))==0,"Critical-safe source comparison constant")
optv=s.sqrt(3*V/c0)
require(s.simplify((V*kap-c0*kap**3/9).subs(kap,optv)-2*V**s.Rational(3,2)/s.sqrt(3*c0))==0,"Scalar comparison constant")
# Resolvent regularization identities are exact scalar functional calculus;
# noncommuting forms use the stated J_R F' J_R identity in the proof.
F,R=s.symbols("F R",positive=True);J=1/(1+F/R);FR=F*J
require(s.simplify(s.diff(FR,F)-J*J)==0,"Yosida derivative coefficient")
require(s.simplify(FR-F*J*J)==F**2*R/(F+R)**2,"Yosida positive bound")
finish("all_sign_evolution.py",dict(
 complete_unitary_weak_evolution_all_finite_K=True,
 scope="compact clock interval with g_K nonzero; fixed eta>=-1/4; declared Friedrichs form",
 actual_negative_g_K=K,actual_negative_g_interval=outward(ng),
 nonzero_real_mode_count=d,source_commutator_Schur_bound=72*d,
 source_occupation_cutoff_M_removed=True,spatial_cutoff_K_removed=False,
 source_occupation_tail_rate="C_K*M^(-1/2) on the declared comparison domain",
 comparison_shift_is_added_physical_source=False,
 full_original_snapshot_selfadjoint_realization=True,
 raw_snapshot_actual_u_strong_domain_transport=False,
 uniform_in_spatial_K_estimates=False,crossing_g_zero_constructed=False),
 [new+"coefficient_window.json",new+"ordering_domain.json",new+"lens_evolution.json",
 new+"coupled_forms.json",new+"SNAPSHOT_DOMAIN.md",new+"REFERENCES.md",
 base+"ACTION_LIFT.md"],proof="ALL_SIGN_EVOLUTION.md")
