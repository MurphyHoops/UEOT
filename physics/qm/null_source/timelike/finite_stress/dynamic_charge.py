"""Nonstatic Ward dependence and full-field smooth incoming charge."""
import json
import sympy as sp
from common import *
gate=json.loads((HERE/"original_ctp_gate.json").read_text())
match=json.loads((HERE/"geometry_matching.json").read_text())
seed=json.loads((TIMELIKE/"dynamic_seed/bounds.json").read_text())
assert all(j["status"]=="PASS" for j in [gate,match,seed])
assert match["corrected_all_mean_residuals_and_finite_normal_derivatives_zero"]
s=box(seed["positive_root_s"]);rho=iv.mpf("1e-25")
Jbound=2*iv.exp(2*rho)*rho/s
assert below(Jbound,"1.34e-25")
q=iv.mpf("0.128")
assert below(q,1)
N00=box(gate["frozen_absolute_density_variance"])
Cvar=4*A**4*N00/9;Crms=iv.sqrt(Cvar)
ResidualFloor=iv.exp(-rho)*Crms
assert above(ResidualFloor,"0.1007") and below(Crms,"0.1008")
# New thin source has the same transported total mean functional.
thinBound=1/(150*V0*A**2)
assert below(thinBound,"5.057e-14")
# Full Ward variation about E=S=0.
eps,e,ep,h,vp,sr=sp.symbols("epsilon e eprime h vprime s",real=True)
full=eps*ep+(h+eps*vp)*eps*e-2*(h+eps*vp)*eps*sr
assert sp.expand(full).coeff(eps,1)==ep+h*e-2*h*sr
# Same-background source conservation, with a'=a h.
aa,rr,pp=sp.symbols("a rho p",positive=True)
dd=sp.Rational(2,3)*aa**2*rr;bb=-aa**2*pp
dp=sp.diff(dd,aa)*aa*h+sp.diff(dd,rr)*(-3*h*(rr+pp))
assert sp.simplify(dp+h*dd-2*h*bb)==0
# Exact constant-charge normalization at the static incoming end.
V0s,As,Hs=sp.symbols("V0 A deltaH",positive=True)
assert sp.simplify(sp.Rational(2,3)*As**2*(Hs/(V0s*As**3))
                   -2*Hs/(3*V0s*As))==0
# Per-mode pair envelopes of kinetic +/- gradient quadratic forms.
omega,F,D=sp.symbols("omega F D",nonzero=True)
kin=(-sp.I*omega*F+D)**2
Brho=sp.expand((kin+omega**2*F**2)/(2*omega))
Bp=sp.expand((kin-omega**2*F**2/3)/(2*omega))
assert sp.simplify(Brho-(-sp.I*F*D+D**2/(2*omega)))==0
assert sp.simplify(Bp-(-2*omega*F**2/3-sp.I*F*D+D**2/(2*omega)))==0
# Sharp density: two fields times k^2 degeneracy, per-oscillator pair norm 2.
hs,vs,asym=sp.symbols("h V0 a",positive=True)
leading_pair=sp.I*hs/(2*vs*asym**4)
shell=4*sp.expand_complex(leading_pair*sp.conjugate(leading_pair))
assert sp.simplify(shell-hs**2/(vs**2*asym**8))==0
k,Ks=sp.symbols("k K",positive=True,integer=True)
assert sp.limit(sp.summation(k**2,(k,1,Ks))/Ks**3,Ks,sp.oo)==sp.Rational(1,3)
# k>=3 implies omega^2=k^2-1 >=(8/9)k^2.
# Vacuum pair norm 2, two-field degeneracy 2 k^2:
tail_factor=sp.Rational(4)*(sp.Rational(9,8))**2
assert tail_factor<8
finish("dynamic_charge.py",{
 "background":"GEOMETRY_MATCHING corrected exact original mean history",
 "full_same_state_Ward_linearized":True,
 "density_response_identically_zero_on_nonstatic_background":False,
 "density_response_is_retarded_image_of_pressure_response":True,
 "Wiener_J_operator_norm_upper":outward(Jbound),
 "Wiener_bound_applied_to_rough_noise_or_metric_variance":False,
 "source_rho_pressure_Ward_mapping_correct":True,
 "finite_window_mismatch_is_constant_distribution_after_exp_U":True,
 "cutoff_centered_KG_Ward_preserved":True,
 "exact_Jost_uniform_finite_derivative_estimates_used":True,
 "full_field_smooth_charge_constructed_in_declared_state_GNS_L2":True,
 "infinite_past_pressure_test_is_declared_state_L2_extension":True,
 "arbitrary_Hadamard_state_noncompact_test_claimed":False,
 "pair_coefficient_decay":"C_test/omega_k^2",
 "high_mode_L2_tail_squared_upper":"8*C_test^2/K for K>=2",
 "C_test_numeric_value_computed":False,
 "sharp_slice_nonstatic_stress_variance_claimed_finite":False,
 "declared_incoming_high_vacuum_sharp_density_variance_diverges_if_h_nonzero":True,
 "sharp_density_variance_divided_by_K_cubed_limit":"h^2/(3*V0^2*a^8)",
 "thin_source_same_mean_U_with_its_own_incoming_transport":True,
 "thin_source_charge_RMS_strict_upper":outward(thinBound),
 "thin_source_charge_variance_strictly_positive_each_sigma_positive":True,
 "thin_source_keeps_old_complete_bare_state":False,
 "incoming_charge_variance":outward(Cvar),
 "incoming_charge_RMS":outward(Crms),
 "positive_window_pressure_matched_dimensionless_density_residual_RMS_lower":outward(ResidualFloor),
 "old_static_N00_relabelled_as_nonstatic_instantaneous_noise":False,
 "full_nonstatic_tensor_noise_kernel_computed":False,
 "no_go_requires_whole_declared_past_pressure_matching_and_zero_geometry_charge":True,
 "deterministic_mean_history_invalidated":False,
 "finite_slice_new_charge_or_quantum_gravity_globally_excluded":False,
 "actual_joint_geometry_matter_device_boundary_density_constructed":False,
 "whole_physical_unification":"OPEN"},
 extra=["original_ctp_gate.json","geometry_matching.json","BOUNDARY_STATE.md",
 "../dynamic_seed/bounds.json","../nonlinear_history/KERNELS.md",
 "../nonlinear_history/EXISTENCE.md"])
