"""Same exact static mean geometry and same positive window for the new radial pair."""
import json,sympy as sp
from fractions import Fraction as F
from common import *
def result():
    r=VP/C;L=1+iv.sqrt(3)/4;mean=L+2*r
    assert above(mean,MU.a) and below(mean,MU.b)
    Vmid=4*r*L+4*r*r
    coeff=M2/(3*X**2)
    assert above(coeff,"0.23") and below(coeff,"0.24")
    assert below(LAMBDA2*X,1)
    K=70
    low=sum(k**4 for k in range(2,K+1))
    assert low==348259330
    spectral=exact(low)+exact(300000)**2*16/(9*K)
    assert below(spectral,3000000000)
    vacuum_pressure=4*spectral/(81*iv.pi**4*X**2)
    thermal_density=8*NTHERMAL*(NTHERMAL+1)/(3*iv.pi**4*X**2)
    thermal_pressure=40*NTHERMAL*(NTHERMAL+1)/(27*iv.pi**4*X**2)
    source_mid_squared=2*coeff**2*Vmid
    total_mid=iv.sqrt(source_mid_squared+vacuum_pressure+thermal_density+thermal_pressure)
    old_lower=iv.sqrt(exact(3)/8)*coeff
    assert below(total_mid,"1.4e-6") and above(old_lower,"0.14")
    # Independent rational safety gate with deliberately coarse constants.
    spectral_q=F(18437815310,7)
    rational_joint=2*F(6,25)**2*F(39,2500000000000)+4*spectral_q/(81*81*(6*10**9)**2)+F(112,27)*F(51,2500)/(81*(6*10**9)**2)
    assert rational_joint < F(14,10**7)**2
    assert 2*F(23,100)**2*F(3,16)>F(14,100)**2
    return {
      "comparison":"new invariant radial pair before any readout",
      "geometry":"same already certified original exact static mean-SCE root",
      "same_fixed_M2_U0_AE_high_state_and_window":True,
      "state_two_point_functions_equal":True,
      "mean_residuals_for_both_preparations":0,
      "source_coefficient_M2_over_3A4":outward(coeff),
      "smooth_window_dimensionless_duration":0.1,
      "proper_window_duration":outward(exact("0.1")/iv.sqrt(LAMBDA2)),
      "third_weak_derivative_L1_cap_includes_endpoint_jumps":2400000,
      "full_pressure_spectral_sum_upper":outward(spectral),
      "independent_exact_rational_joint_RMS_gate_passed":True,
      "vacuum_density_variance":0,
      "vacuum_pressure_variance_upper":outward(vacuum_pressure),
      "thermal_density_variance":outward(thermal_density),
      "thermal_pressure_variance_upper":outward(thermal_pressure),
      "single_ring_source_vector_variance":outward(source_mid_squared),
      "single_ring_joint_projected_residual_RMS_upper":outward(total_mid),
      "two_ring_joint_projected_residual_RMS_strict_lower":outward(old_lower),
      "exact_joint_squared_RMS_difference":"(3/8)*(M2/(3*A^4))^2",
      "original_angular_preparation_relabelled_as_single_ring":False,
      "new_reader_applied_or_old_posterior_geometries_used":False,
      "source_moment_bound_claimed_metric_RMS_or_stability":False,
      "full_local_tensor_device_or_quantum_geometry_closed":False,
      "proof":"STATIC_PREPARATION.md"}
if __name__=="__main__":finish("static_preparation.py",result(),["STATIC_PREPARATION.md","invariant_preparation.json","fluctuations.json"])
