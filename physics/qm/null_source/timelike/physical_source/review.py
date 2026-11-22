"""Independent certificate audit and explicit scope gates; no old checker imports."""
from fractions import Fraction
from common import *
def result():
    names=["static_source","budget","stability","records","constraint"]
    data={n:json.loads((HERE/(n+".json")).read_text()) for n in names}
    for n,d in data.items():
        assert d["status"]=="PASS" and d["old_checkers_executed"]==0
        assert d["source_sha256"]==source_manifest(n+".py")
    # Independent rational gap lower, using the much coarser |2E-1/(4*pi^2)|<1.
    x=3*LAM**2
    lower=Fraction(2*x-18*QR-1,x)
    assert lower>Fraction(1999997,1000000)
    assert data["static_source"]["old_static_lift_obstruction"]["A2_gap"][0]>float(lower)
    assert data["budget"]["minimum_equal_law_average_budget"]=="sqrt(3)/4"
    assert data["budget"]["minimum_budget_common_radial_variance"]=="3/16"
    assert data["stability"]["positive_growth_root_exists"]
    assert data["stability"]["absolute_s_minus_2_upper"]<6.21e-10
    assert not data["stability"]["nonlinear_instability_theorem_claimed"]
    assert data["constraint"]["fixed_state_homogeneous_linear_stochastic_completion_excluded"]
    assert not data["constraint"]["general_gravity_completion_excluded"]
    assert not data["records"]["local_detector_or_gravity_channel_constructed"]
    assert not data["records"]["nonzero_mode_local_stress_noise_deleted"]
    assert data["records"]["cases"]["zero"]["energy_TV_lower"]>0.999992
    cv=data["records"]["cases"]["minimum_equal_law"]["common_radial_CV"]
    assert 0.30216<cv[0]<cv[1]<0.30218
    for pair in data["constraint"]["strict_positive_variance_intervals"].values():
        assert pair[0]>0
    return {"independent_rational_old_gap_lower":str(lower),
        "native_review_agents":3,"external_models_used":False,"external_human_peer_review":False,
        "old_static_S3_lift_not_unknown_exterior":True,
        "replacement_mean_history_not_same_old_prepared_Cauchy_state":True,
        "new_constant_U_not_derived_from_Core":True,
        "radial_TV_and_actual_quantum_TV_distinguished":True,
        "mean_solution_not_small_fluctuation_certificate":True,
        "growth_mode_not_nonlinear_instability_theorem":True,
        "fixed_state_linear_obstruction_not_all_gravity_no_go":True,
        "joint_constraint_compatible_state_geometry_family":"OPEN",
        "real_local_gravitational_probe":"OPEN",
        "whole_physical_unification_goal":"OPEN",
        "certificate_sha256":{n:hashlib.sha256((HERE/(n+".json")).read_bytes()).hexdigest() for n in names},
        "primary_sources":["https://arxiv.org/pdf/gr-qc/9906055","https://arxiv.org/abs/1803.06836",
            "https://arxiv.org/abs/1201.3295","https://arxiv.org/abs/1810.06512",
            "https://arxiv.org/abs/gr-qc/0402029","https://arxiv.org/abs/gr-qc/0408011"]}
if __name__=="__main__":finish("review.py",result())
