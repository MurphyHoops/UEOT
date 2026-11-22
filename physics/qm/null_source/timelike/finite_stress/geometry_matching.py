"""Same-state residual exclusion and a corrected exact mean-history slice."""
import json
import sympy as sp
from common import *
seedpath=TIMELIKE/"dynamic_seed/bounds.json"
fastpath=TIMELIKE/"dynamic_inverse/fast_root.json"
normpath=TIMELIKE/"nonlinear_history/norm_bounds.json"
seed,fast,norm=[json.loads(p.read_text()) for p in [seedpath,fastpath,normpath]]
assert all(j["status"]=="PASS" for j in [seed,fast,norm])
assert norm["chosen_holomorphic_majorant"]==4 and norm["geometry_ball_radius"]=="0.1"
s=box(seed["positive_root_s"]); sf=box(fast["fast_conformal_growth_rate"])
P2=box(seed["D_at_twice_root"])
assert above(s,"1.9") and below(s,"2.1") and above(P2,11) and below(P2,13)
def w4(x):return (1+x)**4*iv.ln(iv.e+x)
R=iv.mpf("1.02");Z=iv.mpf("1.01");c=iv.mpf("1e-16")
N=c*(w4(s)*R+w4(2*s)*R**2)
assert below(N,"2e-13")
Serr=3200*N**2;Eerr=2000*N**3
assert below(Serr,"1.28e-22") and below(Eerr,"1.6e-35")
Elo=c**2*P2/3-Eerr
Ehi=c**2*P2*(Z**4-2*Z**3/3)+Eerr
Slo=c*P2-Serr;Shi=c*P2*Z**2+Serr
assert above(Elo,"3.6e-32") and below(Ehi,"4.7e-32")
assert above(Slo,"1.09e-15") and below(Shi,"1.33e-15")
umax=c*(Z**2-Z);hlo=c*s;hhi=c*s*(2*Z**2-Z)
assert above(hlo,"1.9e-16") and below(hhi,"2.164e-16")
rhod_lo=3*Elo/(2*iv.exp(2*umax));rhod_hi=3*Ehi/2
necd_lo=3*Elo/(2*iv.exp(2*umax))-Shi
necd_hi=3*Ehi/2-Slo/iv.exp(2*umax)
nd_lo=3*hlo*(-necd_hi)/iv.exp(umax);nd_hi=3*hhi*(-necd_lo)
assert above(rhod_lo,"5.3e-32") and below(rhod_hi,"7.1e-32")
assert above(necd_lo,"-1.34e-15") and below(necd_hi,"-1.06e-15")
assert above(nd_lo,"5.9e-31") and below(nd_hi,"8.8e-31")
hp_lo=3*c*s**2;hp_hi=c*s**2*(4*Z**2-Z)
matterB_lo=1-hp_hi+Slo-3*Ehi/2
matterB_hi=1+hhi**2-hp_lo+Shi-3*Elo/2
nm_lo=-3*hhi*matterB_hi
nm_hi=-3*hlo*matterB_lo/iv.exp(3*umax)
assert above(matterB_lo) and below(nm_hi,0)
Tp=iv.ln(Z)/s
# Ward coefficient and density-normalization identities.
z,cs,ss,ps=sp.symbols("z c s P",positive=True)
e2=cs**2*ps*(z**4-sp.Rational(2,3)*z**3)
hs=cs*ss*(2*z**2-z);s1=cs*ps*z**2
assert sp.simplify(ss*z*sp.diff(e2,z)-2*hs*s1)==0
ee,hh,aa,spatial=sp.symbols("E h a S",real=True,nonzero=True)
rhod=sp.Rational(3,2)*ee/aa**2;pd=-spatial/aa**2
drhod=sp.diff(rhod,ee)*(2*hh*spatial-hh*ee)+sp.diff(rhod,aa)*hh*aa
assert sp.simplify(drhod+3*hh*(rhod+pd))==0
# Exact corrected section: reuse the frozen contraction, do not rerun it.
cm=iv.mpf("1e-55");rho=iv.mpf("1e-25")
K=iv.mpf("2e20");H2=iv.mpf(6400);q=K*H2*rho
C0=K*H2/(2*(1-q));Lip=q/(1-q)
Ws,Wf,W2=w4(s),w4(sf),w4(2*s)
rmax=cm*(Ws+iv.mpf("1.1")*Wf)
assert below(rmax,rho.a/2) and below(Lip,"0.147")
slowNorm=C0*(Ws*cm)**2;fullNorm=C0*rmax**2
Delta=slowNorm/W2+fullNorm/Wf
DeltaH=2*s*slowNorm/W2+sf*fullNorm/Wf
assert below(Delta/cm,"0.001")
hm_lo=cm*(iv.mpf("0.9")*sf-s)-DeltaH
hm_hi=cm*(iv.mpf("1.1")*sf-s)+DeltaH
assert above(hm_lo)
Rz=iv.mpf("1e-28");Rw=iv.mpf("1e-51")
assert below(cm*iv.exp(s/sf),Rz.a)
assert below(iv.mpf("1.1")*cm*iv.e,Rw.a)
Tm=1/sf
# lambda/w4(lambda) decreases for lambda>=3:
# logarithmic derivative 1/lambda-4/(1+lambda)
# -1/[(e+lambda)log(e+lambda)] is strictly negative.
assert sp.simplify(1/z-4/(1+z)-(1-3*z)/(z*(z+1)))==0
finish("geometry_matching.py",{
 "probe_amplitude":"1e-16","probe_coefficient_radius":"1.02",
 "probe_z_window":["1","1.01"],"probe_norm_upper":outward(N),
 "probe_S_remainder_bound":outward(Serr),"probe_E_remainder_bound":outward(Eerr),
 "probe_E_lower":outward(Elo),"probe_E_upper":outward(Ehi),
 "probe_S_lower":outward(Slo),"probe_S_upper":outward(Shi),
 "probe_rho_device_times_A2_lower":outward(rhod_lo),
 "probe_rho_device_times_A2_upper":outward(rhod_hi),
 "probe_NEC_times_A2_lower":outward(necd_lo),
 "probe_NEC_times_A2_upper":outward(necd_hi),
 "probe_n_rho_device_times_A3_lower":outward(nd_lo),
 "probe_n_rho_device_times_A3_upper":outward(nd_hi),
 "probe_n_rho_original_matter_times_A3_lower":outward(nm_lo),
 "probe_n_rho_original_matter_times_A3_upper":outward(nm_hi),
 "probe_conformal_duration":outward(Tp),
 "probe_proper_duration_bounds":outward(A*Tp*iv.mpf([1,iv.exp(umax).b])),
 "probe_exact_mean_solution":False,
 "probe_additive_positive_canonical_classical_scalar_repair_excluded":True,
 "all_quantum_controllers_excluded":False,
 "required_device_stress_is_an_actual_device":False,
 "corrected_slow_initial_amplitude":"-1e-55",
 "corrected_fast_initial_amplitude_bracket":["0.9e-55","1.1e-55"],
 "corrected_seed_norm_upper":outward(rmax),
 "corrected_point_correction_upper":outward(Delta),
 "corrected_point_correction_over_c_upper":outward(Delta/cm),
 "corrected_root_iteration_Lipschitz_upper":outward(Lip),
 "corrected_h0_lower":outward(hm_lo),"corrected_h0_upper":outward(hm_hi),
 "corrected_conformal_duration":outward(Tm),
 "corrected_proper_duration_bounds":outward(A*Tm*iv.mpf([iv.exp(-rho).a,iv.exp(rho).b])),
 "corrected_initial_scale_equals_A_exactly":True,
 "corrected_h0_strictly_positive":True,
 "corrected_history_uses_same_fixed_incoming_source":True,
 "corrected_all_mean_residuals_and_finite_normal_derivatives_zero":True,
 "old_mean_existence_reproved_or_claimed_new":False,
 "finite_slice_selection_derived_from_unique_preparation_principle":False,
 "large_probe_amplitude_error_bound_to_corrected_solution_claimed":False,
 "full_nonstatic_CTP_noise_and_quantum_boundary_state_constructed":False,
 "SI_seconds_claimed":False,
 "whole_physical_unification":"OPEN"},
 extra=["../dynamic_seed/bounds.json","../dynamic_inverse/fast_root.json",
 "../nonlinear_history/norm_bounds.json","../nonlinear_history/EXISTENCE.md",
 "../nonlinear_history/KERNELS.md","FINITE_SLICE_UV.md","TOTAL_BOUNDARY_GATE.md"])
