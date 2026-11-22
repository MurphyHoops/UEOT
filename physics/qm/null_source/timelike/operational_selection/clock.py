"""Actual Gaussian-CQ clock resources and finite binary tests, without unbiasedness."""
from common import *
import sympy as sp
def result():
    assert above(P2) and below(JFLAG,"1.319e11") and above(JFLAG,"1.318e11")
    sd=1/iv.sqrt(JFLAG)
    assert above(sd,"2.75e-6") and below(sd,"2.76e-6")
    d=1/SIGMA
    r=VP*d/X
    b=P2*VP*d*d/X**2
    log_inv_F=iv.log(1+r*r)+b/(1+r*r)
    flow=iv.exp(-log_inv_F)
    D=iv.sqrt(1-flow)
    error=(1-D)/2
    assert above(flow,".963") and above(error,".403")
    # For equal priors and target error .05, D must be at least .9.
    threshold= -iv.log(exact("0.19"))/log_inv_F
    assert above(threshold,44) and below(threshold,45)
    varD=exact(".5")+2*KMEAN/X0
    varT=X**2*varD/(4*KMEAN**2)
    cr_gap=VP*(KMEAN-VP)/(2*KMEAN**2)
    assert above(cr_gap)  # Var(Tcal)*J = 1+gap; preserve correlated cancellation.
    geom=json.loads((HERE/"geometry.json").read_text())
    deta=exact(geom["same_eta_phase_difference_upper"])
    dproper=exact(geom["same_proper_time_phase_difference_upper"])
    trace_eta=deta*iv.sqrt(JFLAG)/2
    trace_proper=dproper*iv.sqrt(JFLAG)/2
    assert below(trace_eta,"4.08e-52") and below(trace_proper,"6.08e-52")
    # Stable tiny-phase formula: never evaluate 1-exp(-L) at insufficient precision.
    def testing(difference):
        rr=VP*difference/X
        L=iv.log(1+rr*rr)+P2*VP*difference**2/(X**2*(1+rr*rr))
        necessary=-iv.log(exact(".19"))/L
        return {"log_inverse_F_lower_bound":outward(L),
                "D_upper_from_sqrt_log":outward(iv.sqrt(L))[1],
                "necessary_independent_copies_for_error_0_05":outward(necessary)}
    eta_test=testing(deta);proper_test=testing(dproper)
    assert above(exact(eta_test["necessary_independent_copies_for_error_0_05"][0]),"9e102")
    assert above(exact(proper_test["necessary_independent_copies_for_error_0_05"][0]),"4e102")
    v,kappa,p2,xx=sp.symbols("v kappa p2 x",positive=True)
    assert sp.expand((v*v+v*p2).subs(p2,2*kappa-2*v)-(2*v*kappa-v*v))==0
    assert sp.simplify(1+(2*kappa-2*v)/(4*v)-(sp.Rational(1,2)+kappa/(2*v)))==0
    return {
      "actual_preparation":"two displaced pure Gaussians with vP=x0/4, vQ=1/x0; classical p-mixture",
      "optimistic_resource":"all theta-independent classical p flags; no coherent purification",
      "K_mean":outward(KMEAN),"mean_squared_displacement_P":outward(P2),
      "exact_flag_QFI_theta":outward(JFLAG),
      "single_copy_locally_unbiased_Cramer_Rao_sd":outward(sd),
      "proper_time_static_units_CR_sd":outward(A*sd),
      "calibrated_D_clock_seed_variance":outward(varT),
      "phase_test_separation":outward(d),
      "pure_block_overlap_squared":"(1+(vP*d/A^2)^2)^-1 * exp[-|p|^2*vP*d^2/(A^4*(1+(vP*d/A^2)^2))]",
      "F_lower_bound_from_mean_p_squared":outward(flow),
      "single_copy_trace_distance_upper":outward(D)[1],
      "single_copy_equal_prior_error_lower":outward(error)[0],
      "copy_threshold_interval":outward(threshold),
      "independent_repetitions_necessary_for_error_0_05":45,
      "repetitions_sufficient_claimed":False,
      "finite_binary_test_requires_unbiasedness":False,
      "same_eta_geometry_zero_readout_D_upper":outward(trace_eta)[1],
      "same_proper_time_geometry_zero_readout_D_upper":outward(trace_proper)[1],
      "tiny_phase_same_eta_test":eta_test,"tiny_phase_same_proper_time_test":proper_test,
      "covers_active_during_encoding_interventions":False,
      "covers_high_modes_extra_probes_or_coherent_reference":False,
      "extra_copies_free_in_fixed_two_field_geometry":False,"proof":"CLOCK.md"}
if __name__=="__main__":finish("clock.py",result(),["CLOCK.md","geometry.json"])
