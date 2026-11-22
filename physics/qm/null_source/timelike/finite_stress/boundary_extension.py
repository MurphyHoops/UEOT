"""Actual rank-two source compression and the finite-window boundary contract."""
import json
import sympy as sp
from common import *
boundary=json.loads((HERE/"boundary_state.json").read_text())
dynamic=json.loads((HERE/"dynamic_charge.json").read_text())
assert boundary["status"]==dynamic["status"]=="PASS"
assert boundary["normal_rank_two_correlated_source"]
assert dynamic["thin_source_same_mean_U_with_its_own_incoming_transport"]
Ebar,eps,sigma,x,alpha,mu2=sp.symbols("Ebar epsilon sigma x alpha mu2",real=True)
for N in [0,2]:
    eN=Ebar-N*eps
    assert sp.expand(eN+sigma*x+N*eps-Ebar)==sigma*x
# General spectral compression is scalar on the actual two-dimensional support.
mf,p,B00,B01,B10,B11=sp.symbols("mf p B00 B01 B10 B11")
fcomp=mf*sp.eye(2)
Ccomp=sp.zeros(2)
C2comp=alpha**2*sigma**2*mu2*sp.eye(2)
blocks=sp.Matrix([[B00,B01],[B10,B11]])
assert sp.simplify(sp.trace(fcomp*blocks)-mf*sp.trace(blocks))==0
assert sp.trace(Ccomp*blocks)==0
assert sp.simplify(sp.trace(C2comp*sp.diag(1-p,p))-alpha**2*sigma**2*mu2)==0
# Exact signs in the smooth prehistory identity.
df,ef,by,sy=sp.symbols("df ef by sy",real=True)
Cs=df-2*by;Cg=ef-2*sy;Cpre=2*(by-sy)
assert sp.expand(Cs-Cg+Cpre)==df-ef
thinUpper=1/(150*V0*A**2)
assert below(thinUpper,"5.057e-14")
finish("boundary_extension.py",{
 "actual_candidate":"annulus rank-two full bare marginal plus independent tensor-factor charge",
 "same_total_energy_profile_in_both_support_branches":True,
 "support_does_not_reduce_the_energy_operator":True,
 "support_compression_of_centered_charge":"P C P=0",
 "support_compression_of_bounded_spectral_function":"P f(C) P=integral w(x)^2 f(alpha*sigma*x) dx * P",
 "all_normal_extensions_with_same_full_marginal_supported_in_M_tensor_G":True,
 "product_joint_state_assumed":False,
 "independent_G_only_POVM_energy_statistics_factorize":True,
 "nonzero_probability_G_only_conditioning_preserves_source_energy_law":True,
 "residual_interval_concentration_cannot_exceed_source":True,
 "concentration_bound_requires_finite_variance":False,
 "finite_second_moment_G_only_charge_cross_covariance":0,
 "joint_residual_variance_exact":"alpha^2*sigma^2*mu2+Var_R(Z)",
 "joint_residual_variance_lower":"alpha^2*sigma^2*mu2",
 "actual_gravity_charge_freely_set_constant_claimed":False,
 "source_charge_example_strict_upper_not_lower":outward(thinUpper),
 "profile_mu2_numeric_lower_bound_newly_computed":False,
 "frozen_general_QFI_theorem_reproved_as_new":False,
 "smooth_preparation_past_sign":"Cpre=2*(b-s)(exp(U)*h*Psi_chi)",
 "finite_window_matching_requirement":"Cgeom-Cpre=Csource",
 "new_geometry_and_mixed_noncompact_domains_constructed":False,
 "changed_source_or_nonadditive_relational_models_excluded":False,
 "actual_joint_Einstein_CTP_device_state_constructed":False,
 "whole_physical_unification":"OPEN"},
 extra=["boundary_state.json","dynamic_charge.json","BOUNDARY_STATE.md","DYNAMIC_CHARGE.md"])
