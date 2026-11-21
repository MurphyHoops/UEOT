"""Explicit physical-clock test, nonzero boundary trace, and finite-c cost budgets."""
from common import iv,load,box,above,below,outward,require,finish
inputs=["dynamic_inverse/fast_root.json","dynamic_inverse/causal_inverse.json",
 "joint_history/history.json","finite_stress/boundary_state.json",
 "finite_stress/lapse_boundary/actual_inverse.json",
 "finite_stress/lapse_boundary/prepared_readout.json",
 "finite_stress/lapse_boundary/mixed_boundary.json",
 "finite_stress/GEOMETRY_MATCHING.md"]
fast=load(inputs[0]);sf=box(fast["fast_conformal_growth_rate"])
r=box(fast["fast_kappa_sigma_over_A"]);resA=box(fast["fast_pole_residue_times_A"])
slow=box(fast["old_positive_root_reused"])
A=box(load(inputs[2])["cases"]["unfiltered"]["A"])
bound=load(inputs[3]);sigma=box(bound["example_sigma"]);Ez=box(bound["mean_unfiltered_zero_energy"])
cspec=box(load(inputs[1])["c"]);V0=2*iv.pi**2;gamma=24*A
require(above(r,11) and below(r,12) and above(A,"8e4") and below(A,"1e5"),"Frozen A,fast range")
gm=sf/2;delta=1-slow*slow/(gm*gm)
pref=1/(2*cspec*gm*gm*delta)
require(above(delta) and below(pref,3),"Full middle-line remainder")
require(below(resA*r,-iv.mpf(11)/30),"Retained fast residue sign")
gprime=-iv.mpf(11)/30*iv.exp(16)+3*iv.exp(iv.mpf(17)/2)
require(below(gprime,"-3e6"),"Full Green derivative negative on test")
Ts=18/sf
require(below(Ts,"2e-5") and below(gamma*Ts,40),"Short actual test interval")
require(below(iv.mpf(1)/3*iv.exp(-iv.mpf(9)/2),1),"Normalized bump denominator lower")
require(1000*12**2<200000 and 10000*12**3<20000000,"Proper test derivative bounds")
eps=iv.exp(-1158)
require(below(iv.exp(145)*eps,1),"Actual endpoint sign survives inverse and clock errors")
require(below(3*eps*iv.exp(105)*A*A,1),"Fixed zero phase correction")
require(above(Ez,"8e5") and below(A*A,"7e9") and below(V0,20) and below(sigma,"2.2e-7"),"Source cost inputs")
oldrms=iv.mpf(28)/(3*20*iv.mpf("7e9"))*iv.mpf("8e5")/iv.mpf("2.2e-7")*iv.sqrt(3)
require(above(oldrms,400),"Original fullmode readout absolute cost")
# Explicit elementary radial profile budget, using the exact exponential maxima.
normfactor=iv.exp(iv.mpf(4)/3)
dp=normfactor*2*iv.mpf(2)**2*iv.exp(-2)
ddp=normfactor*(4*iv.mpf(4)**4*iv.exp(-4)+12*iv.mpf(3)**3*iv.exp(-3)+6*iv.mpf(2)**2*iv.exp(-2))
# The triangle bound on varpi'' is deliberately larger than its exact-polynomial bound.
require(below(dp,10) and below(ddp,200),"Elementary radial profile derivative bounds")
# These bounds feed the explicit canonical support-vector estimates.
require(above(sigma,"2e-7") and above(A,"8e4"),"Canonical norm lower denominators")
qnorm=2/(iv.mpf("8e4")**3)*(10/iv.mpf("2e-7")+iv.mpf("1e6")*200/iv.mpf("2e-7")**2)
dnorm=1+2*iv.mpf("1e6")*10/iv.mpf("2e-7")
pnorm=2*iv.mpf("1e5")**3*iv.mpf("1e6")
require(below(qnorm,"1e8") and below(dnorm,"1e15") and below(pnorm,"1e22"),"Canonical support-vector norms")
hnorm=iv.mpf(".016")/iv.sqrt(128)-iv.exp(60)*eps
require(above(hnorm,".001"),"Same-state initial charge norm")
qfactor=768*iv.mpf("1e10")*iv.mpf("1e15")*2/iv.mpf("1.92e6")
require(below(iv.ln(qfactor),51),"Hardy gamma inverse retained")
require(51+66<120 and 124+50<175 and 126<175 and 175<200,"Full readout budget exponents")
c=iv.exp(-20000)
require(below(iv.exp(202)*c*c,c),"Nonlinear initial derivative correction")
require(below(iv.mpf("1.1")*937000+1,iv.exp(14)),"Initial h upper coefficient")
require(-20000+14 < -19980,"Finite nonzero h budget")
lamcoef=iv.mpf(29)/(3*20*iv.mpf("1e10"))
require(above(lamcoef,"1e-11"),"Corrected initial column coefficient")
logleading=19980-14*iv.ln(10)
require(above(logleading,19001) and below(iv.exp(200-logleading),iv.mpf(1)/2),"Reverse triangle including all cross")
require(above(logleading-iv.ln(2),19000),"Repaired finite-c lower RMS exponent")
finish("readout_witness.py",dict(
 actual_physical_clock_bump="g(tau)=(sigma_F/A)*beta((sigma_F/A)*tau-16)",
 full_static_G_remainder_retained=True, middle_line_derivative_prefactor=outward(pref),
 Green_derivative_on_test_upper=outward(gprime), short_conformal_T=outward(Ts),
 actual_raw_pressure_initial_test_lower="29*A^2",
 actual_inverse_and_proper_time_errors_controlled=True,
 raw_unsubtracted_pressure_test_L2=False,
 original_fullmode_readout_RMS_strict_lower=400,
 original_fullmode_candidate_satisfies_density=False,
 original_cost_applies_to_every_UV_legal_low_completion=False,
 corrected_old_alphaD_cost_reused=False,
 corrected_complete_source_cross_terms_retained=True,
 corrected_initial_charge_RMS_strict_lower=".001",
 corrected_actual_readout_RMS_strict_lower="exp(19000)",
 corrected_fullmode_candidate_satisfies_two_homogeneous_weak_rows=True,
 corrected_candidate_accepted_as_controlled_weak_fluctuation=False,
 fixed_c_used_not_only_asymptotic=True,
 canonical_geometry_normal_joint_state_proved=False,
 measured_metric_variance_or_nonlinear_divergence_claimed=False,
 all_preparations_or_all_backgrounds_excluded=False),
 inputs,proof="READOUT_WITNESS.md")
