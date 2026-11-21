"""Explicit nonlinear contraction, same-amplitude error, Ward and physical window."""
import sympy as sp
from common import *
def result():
    norm=json.loads((HERE/"norm_bounds.json").read_text())
    inv=json.loads((HERE/"inverse_bound.json").read_text())
    B=exact(norm["chosen_holomorphic_majorant"])
    r0=exact("0.1");H2=16*B/r0**2
    T=exact(inv["chosen_E4_inverse_upper"]);rho=exact("1e-25")
    q=T*H2*rho; image=T*H2*rho*rho/2
    first=T*H2*(rho/2)**2/2
    distance_gain=T/(1-q)
    assert below(q,exact(1)/2) and below(image,rho/2)
    assert below(distance_gain,"2.3e20")
    Rz=exact("1e-28");Rw=exact("1e-51")
    seed=weight(SLOW)*Rz+weight(SIGMA)*Rw
    assert below(seed,rho/2)
    refined_first=T*H2*seed**2/2
    correction=refined_first/(1-q)
    duration=1/SIGMA
    eps=Rz/(2*iv.exp(SLOW/SIGMA))
    delta=Rw/(2*iv.e)
    proper=1/KAPPA
    proper_enclosure=iv.mpf([(iv.exp(-rho)*proper).a,(iv.exp(rho)*proper).b])

    # Independent exact Ward identity with the full conserved rho,p.
    a,h,r,p=sp.symbols("a h r p",real=True)
    hp,rp=sp.symbols("hp rp",real=True)
    E=h*h+1-sp.Rational(2,3)*a*a*r
    S=hp+(h*h+1)/2+a*a*p
    Eprime=2*h*hp-sp.Rational(2,3)*a*a*(2*h*r+rp)
    assert sp.expand((Eprime+h*E-2*h*S).subs(rp,-3*h*(r+p)))==0
    # Canonical zero transports the original eta_ref; no reset of Q.
    eta,Q,P,A0,eta_ref,J,Jp=sp.symbols("eta Q P A eta_ref J Jp")
    zero=Q+P/A0**2*(eta-eta_ref+J)
    zero_prime=P/A0**2*(1+Jp)
    u=sp.symbols("u")
    assert sp.simplify((A0**2*sp.exp(2*u)*zero_prime).subs(Jp,sp.exp(-2*u)-1)-P)==0
    return {
      "holomorphic_ball_radius":"0.1","holomorphic_majorant":4,
      "D2_spatial_bound_on_half_ball":outward(H2),
      "total_geometry_E4_radius":"1e-25",
      "seed_and_correction_ball_each_radius":"5e-26",
      "contraction_factor":outward(q),
      "self_map_upper":outward(image),
      "first_Picard_increment_uniform_upper":outward(first),
      "Picard_error":"(2*rho/109)*(16/125)^j, v0=0",
      "residual_to_same_amplitude_solution_gain_upper":outward(distance_gain)[1],
      "chosen_bidisc_radii":["1e-28","1e-51"],
      "normalized_seed_E4_norm_enclosure":outward(seed),
      "normalized_solution_correction_E4_upper":outward(correction)[1],
      "explicit_conformal_positive_window":outward(duration),
      "slow_initial_amplitude_for_half_radius_endpoint":outward(eps),
      "fast_initial_amplitude_for_half_radius_endpoint":outward(delta),
      "proper_window_model_units":outward(proper_enclosure),
      "actual_endpoint_inside_each_radius_by_factor":2,
      "same_actual_Q_P_eta_ref_full_S0_occupations_and_fixed_M2_U0":True,
      "state_at_every_time_is_exact_incoming_Jost_and_canonical_zero":True,
      "Hadamard_scope":"strictly interior bidiscs; entire selected real positive window lies inside",
      "spatial_and_Hamiltonian_mean_defects":"identically zero on each constructed history",
      "all_normal_derivatives_of_mean_defects":"identically zero",
      "Ward_identity":"E'+hE=2h*S; E(-infinity)=0 implies E=0 when S=0",
      "exact_nonlinear_mean_history_exists":True,
      "unique_only_for_fixed_two_amplitudes_in_certified_ball":True,
      "covers_old_1e_minus_4_seed_window":False,
      "physical_maximal_amplitude_claimed":False,
      "sampled_source_constraint_or_gravity_instrument_constructed":False,
      "proof":"EXISTENCE.md"}
if __name__=="__main__":finish("history.py",result(),["norm_bounds.py","norm_bounds.json","inverse_bound.py","inverse_bound.json"])
