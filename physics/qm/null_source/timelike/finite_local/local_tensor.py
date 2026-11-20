"""A nonzero local anisotropic source and exact added stress-noise kernel."""
import sympy as sp
from common import *
def result():
    V=2*iv.pi**2;cap=5*iv.pi**2/4+iv.pi/iv.sqrt(2)
    assert below(cap,3*V/4)
    x,y,z=sp.symbols("x y z",real=True)
    v=sp.Matrix([x,y,z]);Q=v*v.T-sp.eye(3)*(v.dot(v))/3
    assert sp.expand(sp.trace(Q.T*Q)-sp.Rational(2,3)*(v.dot(v))**2)==0
    s,A0,w=sp.symbols("s A w",positive=True)
    before=s*s/(3*sp.pi**6*A0**9)
    assert sp.simplify(before.subs(s,sp.pi**2*A0**4/(2*w))-1/(12*sp.pi**2*A0*w*w))==0
    v0=sp.symbols("v0",real=True)
    rho=(v0*v0+v.dot(v))/2
    Tij=v*v.T+sp.eye(3)*(v0*v0-v.dot(v))/2
    assert sp.expand(rho*rho+2*v0*v0*v.dot(v)+sp.trace(Tij.T*Tij)-4*rho*rho)==0
    actual_w=C/2500
    energy_lower=A/(4*actual_w)
    assert above(energy_lower,"8.31e-14")
    Wlower=1/(12*iv.pi**2*A*actual_w**2)
    assert above(Wlower,"1.7e-42")
    return {
      "scope":"original static out Cauchy surface immediately after the short pulse",
      "out_test_solution":"u=E f, smooth real solution, same actual short filter",
      "out_support_cap_radius_upper":"5*pi/8 (deliberately wider than 7*pi/12)",
      "out_cap_volume_upper":outward(cap),
      "out_cap_fraction_strictly_less_than":0.75,
      "spatial_integral_u":"plus or minus A^-2",
      "nonselective_added_mean_tensor":"2*s*T[u], s=1/(4*v_m)",
      "actual_target_out_injected_energy_strict_lower":outward(energy_lower),
      "full_nonselective_mean_tensor_integrated_Frobenius_upper":outward(exact("3.76e-11")),
      "nonselective_anisotropic_mean_L2_squared_strict_lower":outward(Wlower),
      "complete_flags_weighted_anisotropic_mean_L2_squared_has_same_lower":True,
      "at_least_one_flag_has_nonzero_local_anisotropic_mean":True,
      "small_lower_bound_claimed_observably_large":False,
      "local_added_noise":"s*sum_i <{L_i(x),L_i(xprime)}/2> + 4*s^2*T[u](x)*T[u](xprime)",
      "raw_linear_moment_includes_actual_CQ_means":True,
      "nonselective_noise_increment_positive_semidefinite_on_real_smooth_tests":True,
      "nonselective_noise_increment_at_least_squared_mean_shift":True,
      "integrated_momentum_upper":outward(exact("1.88e-11")),
      "integrated_anisotropic_pressure_upper":outward(2*iv.sqrt(exact(2)/3)*exact("1.88e-11")),
      "original_cross_species_noise_retained":True,
      "conditional_noise_obtained_by_total_covariance":True,
      "position_SO4_twirl_applied":False,
      "all_future_times_claimed_anisotropic_by_this_slice_bound":False,
      "inhomogeneous_metric_response_solved":False,
      "proof":"LOCAL_TENSOR.md"}
if __name__=="__main__":finish("local_tensor.py",result(),["LOCAL_TENSOR.md","local_readout.json","smooth_binary.json"])
