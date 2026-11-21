"""Certify the old physical-S3 lift obstruction and a new complete mean history."""
from common import *
def result():
    xold=iv.mpf(3*LAM**2)
    eold=E(xold)
    enz=eold-1/(4*iv.pi**2)
    target=xold-M/xold-eold
    gap=enz-target
    normalized=gap/xold
    assert above(normalized,"1.999997") and above(gap,6442441799)
    global_x=iv.mpf([4*LAM**2,9*LAM**2])
    e3=E(iv.mpf(3))
    # E'(x)=-1/(48*pi^2*x), hence F_x=2x-2E+1/(24*pi^2).
    monotone_at_3=6-2*e3+1/(24*iv.pi**2)
    assert above(monotone_at_3,"5.98")
    assert below(abs(E(global_x)),"0.04")
    assert below(F(iv.mpf(4*LAM**2),iv.mpf(0)),0)
    assert above(F(iv.mpf(9*LAM**2),D))
    cases={}
    for name,b in [("zero",iv.mpf(0)),("half_minimum",D/4),("minimum_equal_law",D/2),
                   ("between_equal_and_zero_radial_noise",3*D/4),("zero_radial_noise",D)]:
        x=root_box(b);a=iv.sqrt(x)
        u=1/x-(2*B(x)/3-D0)/x**2
        nu=4*iv.pi**2*M/x
        assert above(u) and above(nu,10**11)
        cases[name]={"budget":outward(b),"A_squared":outward(x),"A":outward(a),
            "constant_matter_potential_U":outward(u),"nu":outward(nu),
            "single_reference_rho":outward(B(x)/x**2),
            "single_reference_pressure":outward((B(x)/3+D0)/x**2)}
    return {"prescription":{"lambda":LAM,"mu":1,"alpha_extra":0,"G_equals_2T":True},
        "reused_spectral_constant":outward(S),"fixed_original_M2":[MLO,MHI],
        "old_static_lift_obstruction":{"A_squared":3*LAM**2,
            "A4_device_NEC_target":outward(target),"A4_device_long_time_lower":outward(enz),
            "A4_gap":outward(gap),"A2_gap":outward(normalized),
            "scope":"entire old static S3 past plus one independent free minimal massless scalar",
            "Hadamard_mixed_nonGaussian_squeezed_allowed":True,
            "unknown_external_region_excluded_from_claim":True},
        "replacement_mean_history":{"fields":2,"budget_range":[0,outward(D)[1]],
            "radius_equation":"x^2-2*x*E(x)=(1+b)*M2",
            "unique_root_for_each_fixed_M2_and_budget":True,
            "global_A_bounds_in_lambda":[2,3],
            "global_monotonicity_lower_at_x3":outward(monotone_at_3),"cases":cases,
            "zero_mode":"Var(Q)=1/(2*A^2), Var(P)=A^2/2, [Q,P]=i",
            "matter_Lagrangian":"-sum_i (grad phi_i)^2/2 - U",
            "state_and_couplings_chosen_once":True,
            "both_Einstein_components_exact_for_all_times":True,
            "changes_old_geometry_and_prepared_Cauchy_state":True,
            "constant_U_is_new_physical_input_not_Core_derived":True}}
if __name__=="__main__":finish("static_source.py",result())
