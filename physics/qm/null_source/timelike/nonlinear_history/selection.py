"""Exact-family selection consequences, curvature, and the remaining source obstruction."""
import sympy as sp
from common import *
def result():
    hist=json.loads((HERE/"history.json").read_text())
    assert hist["exact_nonlinear_mean_history_exists"]
    ratio=box(FAST["fast_to_slow_rate_ratio"])
    N=math.floor(float(ratio.a))
    assert N==468087 and above(ratio,N) and below(ratio,N+1)
    assert above(SIGMA,2*SLOW.b)
    z,s,x=sp.symbols("z s x",positive=True)
    curvature=6/x*sp.exp(-2*z)*(1+s*s*z+s*s*z*z)
    tangent=sp.diff(curvature,z).subs(z,0)
    assert sp.simplify(tangent-6*(s*s-2)/x)==0
    fast_curvature=6*(SIGMA**2-2)/X
    assert above(fast_curvature)
    variance=box(CASE["variance_S0"])
    assert above(variance)
    dm,aa=sp.symbols("delta_M A",real=True,nonzero=True)
    delta_rho=dm/(2*aa**6)
    delta_E=-sp.Rational(2,3)*aa*aa*delta_rho
    delta_C=sp.simplify(aa*aa*delta_E)
    delta_S=sp.simplify(aa*aa*delta_rho)
    assert sp.simplify(delta_C+dm/(3*aa*aa))==0
    assert sp.simplify(delta_S-dm/(2*aa**4))==0
    return {
      "exact_mean_family_existence_reused_from_new_history":True,
      "fixed_nonzero_slow_amplitude_remaining_fast_family":True,
      "distinct_exact_histories_share_slow_first_and_second_coefficients":True,
      "past_slow_expansion_orders_shared_before_fast_term":N,
      "fast_to_slow_ratio":outward(ratio),
      "difference_asymptotic":"(delta2-delta1)*exp(sigma*eta)*(1+O(exp(s*eta))) as eta -> -infinity",
      "common_normalized_slow_quadratic_coefficient_reused":SEED["beta"],
      "curvature_fast_tangent":outward(fast_curvature),
      "time_shift_invariant_for_positive_epsilon":"delta / epsilon^(sigma/s)",
      "all_smooth_or_Hadamard_histories_classified":False,
      "two_independent_observables_claimed":False,
      "same_slice_Cauchy_covariance_for_different_histories_claimed":False,
      "full_incoming_state_and_eta_ref_fixed":True,
      "source_S0_variance_reused":outward(variance),
      "sampled_delta_source_past_C_defect":"-delta_M/(3*A^2)",
      "sampled_delta_source_past_S_defect":"delta_M/(2*A^4)",
      "randomizing_growth_amplitudes_alone_carries_nonzero_sampled_source":False,
      "fluctuation_law_selected_by_mean_existence":False,
      "same_joint_twirl_covariant_selection_instrument_records_still_equal":True,
      "next_gate":"independent physical selection and source-geometry joint constraints, then instrument calibration",
      "whole_physical_unification_goal":"OPEN",
      "proof":"SELECTION.md"}
if __name__=="__main__":finish("selection.py",result(),["history.py","history.json"])
