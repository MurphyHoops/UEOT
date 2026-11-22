"""Endpoint Gaussian/Schur resource algebra and exact pure-target oscillator optimum."""
import sympy as s
from common import *
P="physics/qm/null_source/timelike/finite_stress/lapse_boundary/"
paths=[P+"quiet_window.json",P+"relational_coupled/actual_uv_bridge.json",
 P+"ENDPOINT_DOMAIN.md",P+"ACTION_BOUNDARY.md",P+"ACTUAL_INVERSE.md",
 P+"relational_coupled/ACTUAL_UV_BRIDGE.md",
 P+"relational_coupled/PHYSICAL_SLICE.md",
 P+"joint_feedback/NEAR_RECOVERY.md",P+"joint_feedback/MIXED_RESOURCE.md"]
quiet,uv=load(paths[0]),load(paths[1])
require(quiet["new_initial_slow_amplitude_exact"]=="exp(-20000)" and uv["same_actual_background_and_incoming_state"],"Actual incoming endpoint")
mu=exact(".1");om=iv.sqrt(8)
require(above((1-2*mu/om)**2/2,exact(1)/4),"Actual X lower coefficient")
require(below((1+2*mu/om)**2/2,2),"Actual X upper coefficient")
# Shell multiplicity: one q Gaussian char exponent -1/2, 2 k^2 real modes.
k=s.symbols("k",positive=True)
require(s.simplify(s.Rational(-1,2)*2*k**2+k**2)==0,"Two-field Gaussian shell exponent")
x=s.symbols("x",positive=True)
mon=s.log(1+x)-x/(1+x)
require(s.simplify(s.diff(mon,x)-x/(1+x)**2)==0,"Global band log monotonicity")
require(9*16==144,"Uniform band denominator")
# Exact square-root remainder, not a formal truncated asymptotic equality.
expr=s.sqrt(1+x)-1-x/2+x**2/(2*(s.sqrt(1+x)+1)**2)
require(s.simplify(expr)==0,"Global oscillator sqrt remainder")
Q=s.symbols("Q",real=True);X,v=s.symbols("X variance",positive=True);m=s.symbols("m",real=True)
Om=s.sqrt(1+4*v*X**2)
psi=s.exp(-Om*Q**2/2+s.I*m*X*Q**2)
covP=lambda f:-s.I*s.diff(f,Q)-2*m*X*Q*f
Apsi=(covP(covP(psi))+Om**2*Q**2*psi-psi)/2
require(s.simplify((Apsi-(Om-1)*psi/2)/psi)==0,"Actual averaged oscillator ground state")
require(s.simplify(2*k**2*(Om-1)/2-k**2*(Om-1))==0,"Pure target exact minimum degeneracy")
# M2=v+m^2 vs pure-output free-source minimum: mean shear is a genuine distinction.
d=s.symbols("d",real=True)
require(s.expand((d-m)**2+2*m*d-m**2)==d**2,"Centering moment identity")
# Safe omega inequalities used in the analytic sum bound, k>=3.
r=iv.mpf([0,exact(1)/9])
require(below((1-r)**(-exact(3)/2),2),"k^2/omega^3 <=2/k")
require(below(1/(iv.sqrt(1-r)*(1+iv.sqrt(1-r))),1),"k^2/omega-k <=1/k")
# General finite-rank Sylvester entry and the actual overlapping-packet leakage.
la,lb,Aij=s.symbols("lambda_a lambda_b Aij",positive=True)
Yij=2*s.sqrt(la*lb)*Aij/(la+lb)
require(s.simplify((la+lb)*Yij-2*s.sqrt(la*lb)*Aij)==0,"Universal Sylvester entry")
mix,mu2,mu4,ell=s.symbols("lambda mu2 mu4 ell",positive=True)
Cfull=ell**2*(mix*mu2+(1-mix)*mu4/mu2-4*mix*(1-mix)*mu2)
Cpositive=ell**2*(mu2*(2*mix-1)**2+(1-mix)*(mu4/mu2-mu2))
require(s.simplify(Cfull-Cpositive)==0,"Continuous packet mixed variance with leakage")
require(s.simplify(Cfull.subs(mix,s.Rational(1,2))-ell**2*(mu4/mu2-mu2)/2)==0,"Half-mixture does not lose full kappa-squared form")
hh,dd,RR=s.symbols("h delta R",positive=True)
mm=(1-dd)*hh;ww=dd*hh/(RR-mm)
require(s.simplify(ww*(1-ww)*(RR-mm)**2-dd*hh*(RR-hh))==0,"Near-recovery between-packet variance")
# Finite-rank leakage energy split uses an exact matrix-coefficient CCR shear.
t=s.symbols("t",real=True)
shear=s.Matrix([[1-s.I*t,-s.I*t],[s.I*t,1+s.I*t]])
inverse=s.Matrix([[1+s.I*t,s.I*t],[-s.I*t,1-s.I*t]])
require(s.simplify(shear*inverse)==s.eye(2),"Compressed annihilator inverse shear")
tt,ll=s.symbols("occupation leakage",positive=True)
require(s.simplify((tt+s.sqrt(tt*ll))**2-tt*(tt+ll)-2*tt*s.sqrt(tt*ll))==0,"Weighted leakage Cauchy margin")
leak=ell**2*(1-mix)*(mu4/mu2-mu2)
require(s.simplify(Cfull-leak-ell**2*mu2*(2*mix-1)**2)==0,"Noncommuting mixed-target upper-lower gap")
require(s.simplify(Cfull.subs(mix,s.Rational(1,2))-leak.subs(mix,s.Rational(1,2)))==0,"Commuting half-mixture globally sharp leading coefficient")
finish("endpoint_normality.py",dict(
 fixed_high_vacuum_output_distance_to_every_fixed_normal_target="tends to one uniformly over remaining normal inputs",
 arbitrary_varying_input_purity_zero_claimed=False,
 uniform_UV_tail_tight_preparations_excluded_for_fixed_normal_output=True,
 arbitrary_high_correlations_allowed_in_resource_theorem=True,
 resource_Hamiltonian="sum k=3..K, 2k^2 modes, omega_k a^dagger a",
 finite_band_error_bound="Dtr >= [Tr F gamma - a_L(F) - sqrt(E_K/S_KL)]_+",
 normal_output_necessary_resource="liminf E_K/K^2 >0, target-dependent coefficient",
 subquadratic_resource_output_distance="one from every fixed normal target",
 finite_K_normal_inverse_dressing_exists=True,
 fixed_joint_vacuum_output_exact_energy="2 M2 sum k^2 omega X_k^2",
 fixed_pure_geometry_free_high_output_exact_minimum="sum k^2 omega (sqrt(1+4 Var(kappa) X_k^2)-1)",
 actual_Jost_pure_target_leading_coefficient="Var(kappa)/4",
 optimal_growth_order="Theta(K^2) for fixed finite-M2 targets",
 cutoff_inputs_automatically_one_consistent_raw_state=False,
 disjoint_support_mixed_target_exact_minimum=True,
 general_finite_rank_mixed_attainable_leading_coefficient="F_Q(gamma,kappa)/16",
 general_mixed_arbitrary_entangled_optimality_proved=True,
 sharp_general_mixed_proof="MIXED_RESOURCE.md",
 normal_output_excludes_trace_normal_incoming_subsequence=True,
 exact_finite_rank_target_universal_leakage_lower=True,
 leakage_finite_K_bound="positive part of l S - 2 sqrt(l ||L|| R (C_A l+2||A0||^2) S)",
 commuting_compressed_position_mixed_target_globally_sharp_leading=True,
 approximate_targets_outside_support_covered_by_leakage_theorem=False,
 full_kappa_squared_form_leakage_retained=True,
 algebraic_Weyl_limit_positive=True,
 limiting_GNS_dilation_regular=False,
 original_L2_dilation_self_adjointness_destroyed=False,
 passive_frame_effect_is_physical_decoherence=False,
 total_conserved_energy_or_apparatus_work_theorem=False),paths)
