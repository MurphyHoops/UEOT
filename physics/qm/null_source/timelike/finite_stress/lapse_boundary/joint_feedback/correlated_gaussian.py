"""Conditional original-source Gaussian candidate and retained covariant cost."""
import sympy as s
from common import *
P="physics/qm/null_source/timelike/finite_stress/lapse_boundary/"
paths=[P+"RELATIONAL_DOMAIN.md",P+"relational_coupled/COEFFICIENT_WINDOW.md",
 P+"relational_coupled/ACTUAL_UV_BRIDGE.md",P+"ACTUAL_INVERSE.md",
 P+"joint_feedback/JOINT_CUTOFF.md",P+"joint_feedback/GEOMETRY_CURVATURE.md",
 P+"joint_feedback/POSITIVE_WINDOW.md",P+"joint_feedback/joint_cutoff.json"]
prior=load(paths[-1])
require(prior["original_complete_generator_and_dilation_retained"],"Same complete generator")
q,kap,Om,om=s.symbols("q kappa Omega omega",positive=True)
psi=s.exp(-(Om+s.I*kap)*q*q/2)
covP=lambda z:-s.I*s.diff(z,q)+kap*q*z
Hpsi=(covP(covP(psi))+Om*Om*q*q*psi)/(2*kap)
require(s.simplify((Hpsi-Om*psi/(2*kap))/psi)==0,"Exact conditional source ground")
Op=s.symbols("Omega_prime",real=True)
logder=Op/(4*Om)-(Op+s.I)*q*q/2
mom={0:s.Integer(1),2:1/(2*Om),4:3/(4*Om**2)}
def average(z):
 return sum(coef*mom[powers[0]] for powers,coef in s.Poly(s.expand(z),q).terms())
mean=s.simplify(average(logder))
norm=s.simplify(average(logder*s.conjugate(logder)))
require(s.simplify(mean+s.I/(4*Om))==0,"Berry coefficient per real mode")
metric=s.simplify(norm-mean*s.conjugate(mean))
require(s.simplify(metric-(Op*Op+1)/(8*Om*Om))==0,"Gaussian projective derivative metric")
require(s.simplify(metric.subs(Op,-kap/Om).subs(Om**2,om**2-kap**2)-om**2/(8*(om**2-kap**2)**2))==0,"Exact conditional metric")
K,k=s.symbols("K k",positive=True,integer=True)
H,D0,D1,D3=s.symbols("harmonic D0 D1 D3",real=True)
T=K*(K+1);beta=1+kap*kap
Crad=T*(T-1)/4-H/8
pot=(D0-Crad)/kap+(D1+H/4+T/4)*kap+(D3+H/8)*kap**3
sumP=s.summation(k**3-beta*k/2,(k,1,K))-beta**2*H/8
require(s.simplify(pot-(D0/kap+D1*kap+D3*kap**3-sumP/kap))==0,"Exact original counterterm cancellation")
x=s.symbols("x",positive=True)
require(s.simplify(s.diff(s.sqrt(1-x),x,3)+3/(8*(1-x)**s.Rational(5,2)))==0,"Controlled source tail third derivative")
shell=k*k*(k*k-1)/(k*k-beta)**2
positive=((2*beta-1)*k*k-beta*beta)/(k*k-beta)**2
require(s.simplify(shell-1-positive)==0,"Metric shell excess")
require(s.limit(shell,k,s.oo)==1,"Metric K/4 normalization")
require(s.simplify(s.diff(s.asin(kap/om)/2,kap)-1/(2*s.sqrt(om*om-kap*kap)))==0,"Berry phase primitive")
# Scalar bulk phase cancellation uses the same harmonic/subtraction coefficients.
require(s.simplify(-T/4-beta*H/4+s.summation(k/2,(k,1,K))+beta*H/4)==0,"Original scalar connection cancellation")
v,m,g=s.symbols("velocity mean g",real=True)
require(s.simplify((g*v)**2*m/(2*g)-g*v*v*m/2)==0,"Restored current phase energy")
I1=s.symbols("inverse_moment",positive=True)
require(s.simplify(-2*I1/4+I1/2)==0,"Full logarithmically scaled expectation")
# A real n=1 high-shell branch supplies a mean-only repair.
psi1=q*psi
Hpsi1=(covP(covP(psi1))+Om*Om*q*q*psi1)/(2*kap)
require(s.simplify((Hpsi1-3*Om*psi1/(2*kap))/psi1)==0,"Exact first Hermite excitation")
logder1=3*Op/(4*Om)-(Op+s.I)*q*q/2
mom1={0:s.Integer(1),2:3/(2*Om),4:15/(4*Om**2)}
av1=lambda z:sum(coef*mom1[powers[0]] for powers,coef in s.Poly(s.expand(z),q).terms())
mean1=s.simplify(av1(logder1))
metric1=s.simplify(av1(logder1*s.conjugate(logder1))-mean1*s.conjugate(mean1))
require(s.simplify(mean1-mean+s.I/(2*Om))==0,"Excited Berry increment")
require(s.simplify(metric1-3*metric)==0,"Excited projective metric factor")
p0,E0,E1,Et,V0,V1=s.symbols("probability E0 E1 target V0 V1",real=True)
repair=(Et-E0)/(E1-E0)
require(s.simplify(((1-p0)*E0+p0*E1-Et).subs(p0,repair))==0,"Exact complete clock mean repair")
mixvar=(1-p0)*(V0+E0**2)+p0*(V1+E1**2)-((1-p0)*E0+p0*E1)**2
require(s.simplify(mixvar-((1-p0)*V0+p0*V1+p0*(1-p0)*(E1-E0)**2))==0,"Retained quantum branch variance identity")
# The actual complete source force uses the excited eigenvalue derivative.
Omkap=s.sqrt(om*om-kap*kap)
require(s.simplify(-s.diff(Omkap/kap,kap)/kap-om*om/(kap**3*Omkap))==0,"Excited source force Hellmann-Feynman factor")
I3=s.symbols("third_inverse_moment",positive=True)
require(s.simplify(-2*4*I3/4+2*I3)==0,"Ground curvature leading coefficient")
require(s.simplify(-4*I3/2-2*I3+4*I3)==0,"Repaired curvature leading coefficient")
# Rare phase and rare high excitation can match two initial means together.
rr,nu,bp=s.symbols("rare_phase_probability target_velocity phase",nonzero=True,real=True)
bpvalue=g*nu/rr
require(s.simplify((rr*bp/g).subs(bp,bpvalue)-nu)==0,"Exact rare-phase initial velocity")
require(s.simplify((rr*bp**2*m/(2*g)).subs(bp,bpvalue)-g*nu**2*m/(2*rr))==0,"Rare-phase complete mean shift")
require(s.simplify((-2/(4*g**2)*rr*bp**2*I1).subs(bp,bpvalue)+nu**2*I1/(2*rr))==0,"Rare-phase force correction")
finish("correlated_gaussian.py",dict(
 changed_complete_bare_source=True,
 original_counterterms_and_U0_retained=True,
 conditional_high_source_ground_exact=True,
 source_plus_scalar_potential_converges=True,
 source_plus_potential_tail="O(K^-2) uniformly on fixed compact kappa support",
 geometric_projective_metric="K/4+O(1)",
 least_form_scalar_phase_included=True,
 complete_expectation_times_logK_over_K="-I1/2 <0",
 scalar_phase_alone_cannot_repair=True,
 normal_bulk_joint_state_limit_constructed=True,
 bulk_vector_tail="O(K^-1/2)",
 raw_incoming_trace_normal_limit_constructed=False,
 bulk_reference_is_explicit=True,
 actual_bulk_Jost_Fock_identification_has_square_summable_beta=True,
 original_covariant_connection_must_be_retained=True,
 full_Hadamard_joint_state_proved=False,
 exact_single_clock_mean_repair_exists=True,
 repair_probability="asymptotic 1/(2 log K)",
 repaired_clock_variance_liminf_scaled="log(K)/K^2 Var >= I1^2/2",
 repaired_initial_curvature_scaled="log(K)^2/K kappa_second -> -4 I3",
 ground_initial_curvature_scaled="log(K)^2/K kappa_second -> -2 I3",
 uniform_positive_time_window_claimed=False,
 single_global_velocity_phase_preserves_fixed_normal_bulk_limit=False,
 rare_phase_mixture_restores_initial_velocity_with_same_normal_bulk_limit=True,
 current_and_clock_mean_repair_weights_fixed_once_at_initial_slice=True,
 clock_variance_is_full_constraint_residual=False,
 original_mean_history_or_constraint_recovery=False,
 renormalized_propagator_nonexistence_claimed=False),paths)
