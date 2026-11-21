"""Combined static UV subtraction and explicit C2 tail bounds."""
import sympy as s
from common import *
base="physics/qm/null_source/timelike/finite_stress/lapse_boundary/";new=base+"relational_coupled/"
load(new+"coefficient_window.json")
k=s.symbols("k",positive=True);V,z=s.symbols("V z",real=True)
dBK=-k/2-1/(4*k);dCr=k**3-k/2-1/(8*k)
dL=s.expand(dBK*V-V**2/(8*k)+dCr)
target=k**3-(1+V)*k/2-(1+V)**2/(8*k)
require(s.simplify(dL-target)==0,"Exact same-action per-shell subtraction")
F=-s.sqrt(1-z)+1-z/2-z*z/8
for j in range(3):require(s.diff(F,z,j).subs(z,0)==0,"C2 Taylor cancellations")
require(s.simplify(s.diff(F,z,3)-s.Rational(3,8)*(1-z)**(-s.Rational(5,2)))==0,"Exact third derivative")
sup3=3/iv.sqrt(2)
require(below(sup3,3),"Uniform third derivative bound on |z|<=1/2")
E=k*k*s.sqrt(k*k-1-V)
require(s.simplify(s.diff(-E,V,2)-k*k/(4*(k*k-1-V)**s.Rational(3,2)))==0,"Vacuum Hessian")
require(s.simplify(s.diff(dL,V,2)+1/(4*k))==0,"Counterterm Hessian")
# Symbolic large-k comparison via e=1/k, with k positive.
e=s.symbols("e",positive=True)
series=s.series((-E+dL).subs(k,1/e),e,0,4).removeO()
require(s.simplify(series-(1+V)**3*e**3/16)==0,"Combined remainder starts at k^-3")
require(s.limit(k*(s.diff(-E,V,2)),k,s.oo)==s.Rational(1,4),"Harmonic divergence cancels only after combination")
M=iv.mpf(2);K=64
tails=[M**3/(2*K*K),M**2/(K*K),3*M/(2*K*K)]
kap=s.symbols("kap",positive=True)
# The overlap/log and variance asymptotics are a representation diagnostic,
# with the all-field rejection reused from the predecessor proof.
require(s.limit(k*k/(4*(k*k-1)),k,s.oo)==s.Rational(1,4),"Centered sharp Q variance per shell")
require(s.limit(-k*k*s.log(1+kap*kap/(4*(k*k-1)))/2,k,s.oo)==-kap*kap/8,"Shear overlap modulus per shell")
finish("cutoff_gate.py",dict(
 bare_g_sign_change_is_not_no_continuum_theorem=True,
 same_AE_per_shell_subtraction_combined=True,
 frozen_V_comparison_C2_tail_bounds=["M^3/(2K^2)","M^2/K^2","3M/(2K^2)"],
 demonstration_M=2,demonstration_K=64,demonstration_tail_bounds=[outward(x) for x in tails],
 static_high_frequency_Hessian_log_divergence_cancels=True,
 actual_nonstatic_incoming_CTP_limit_proved=False,
 isolated_W_fixed_Fock_limit_rejection_reused=True,
 normal_ordering_scalar_subtraction_makes_sharp_Q_L2=False,
 combined_full_propagator_limit_excluded=False,
 combined_full_propagator_limit_constructed=False),
 [new+"coefficient_window.json",base+"ACTION_LIFT.md",base+"QUANTUM_ENDPOINT.md",
 base+"quantum_endpoint.json",base+"RELATIONAL_DOMAIN.md",
 "physics/qm/null_source/timelike/finite_stress/FINITE_SLICE_UV.md"],proof="CUTOFF_GATE.md")
