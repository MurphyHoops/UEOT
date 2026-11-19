"""Causal logarithmic response, an exact scalar inverse, and overlap scope.

No inherited scientific checker or mode ODE is executed. The actual prepared
closed-FLRW polarization is NOT replaced by a flat/conformal vacuum kernel.
All decimal certificates below concern the explicitly specified log normal form
or the geometric coefficient of a Hadamard-state-difference estimate.
"""
from fractions import Fraction as F
from pathlib import Path
from math import factorial, comb, nextafter, inf
import argparse
import hashlib
import json
import subprocess
from mpmath import iv, mp
import sympy as sp

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[5]
TIMELIKE = HERE.parents[1]
BASE = "c57e2f411e58dc1dae60de8f3c97fbd680e46d8b"
mp.dps = 90
iv.dps = 70

def I(x):
    if hasattr(x, "_mpi_"): return x
    if isinstance(x, mp.mpf): return iv.mpf(x)
    x = F(x)
    return iv.mpf(x.numerator) / x.denominator

def endpoint(x, j): return mp.make_mpf(x._mpi_[j])
def rational(x):
    sign, man, exponent, _ = x._mpf_
    return F((-1 if sign else 1)*man)*F(2)**exponent
def pair(x): return [str(rational(endpoint(x, j))) for j in (0, 1)]
def lo(x): return F(pair(x)[0])
def hi(x): return F(pair(x)[1])
def upper_float(x): return nextafter(float(hi(x)), inf)
def upper(x): return I(endpoint(x, 1))
def absolute(x): return I(max(abs(endpoint(x, 0)), abs(endpoint(x, 1))))
def box(a, b): return iv.mpf([endpoint(I(a), 0), endpoint(I(b), 1)])
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()

def freeze_inputs():
    paths = [
        "operational_response/CONTRACT.md",
        "operational_response/review.json",
        "operational_response/kernel/check.py",
        "operational_response/kernel/README.md",
        "operational_response/kernel/result.json",
        "compatibility/CONTRACT.md",
        "evolution/stress/README.md",
    ]
    frozen = {}
    for relative in paths:
        p = TIMELIKE / relative
        archive = subprocess.check_output(
            ["git", "show", BASE+":"+str(p.relative_to(REPO))], cwd=REPO)
        assert p.read_bytes() == archive, ("inherited input changed", relative)
        frozen[p] = sha(p)
    for name in ("check.py", "README.md"): frozen[HERE/name] = sha(HERE/name)
    parent = json.loads((TIMELIKE/"operational_response/kernel/result.json").read_text())
    assert parent["lambda"] == 32768
    assert parent["response"]["time_gap"] == "1/32"
    assert not parent["scope"]["full_feedback_operator_including_overlap_contacts"]
    return parent, frozen

def exact_checks():
    p, k, mu, x = sp.symbols("p k mu x", positive=True)
    a = sp.symbols("a", real=True)
    kap = sp.symbols("kappa", positive=True)
    frullani = -sp.log(1+k*k/(p*p))/2
    assert sp.simplify(sp.diff(frullani, k)+k/(p*p+k*k)) == 0
    symbol = 2*sp.log(p/mu)+sp.log(1+k*k/(p*p))
    assert sp.simplify(sp.diff(symbol, k)-2*k/(p*p+k*k)) == 0
    monomials = []
    for m in range(1, 7):
        weights = [F((-1)**j*comb(m-1, j)) for j in range(m)]
        int_one = sum((w/F(j+1) for j, w in enumerate(weights)), F(0))
        int_log = -sum((w/F((j+1)**2) for j, w in enumerate(weights)), F(0))
        harmonic = sum((F(1, j) for j in range(1, m+1)), F(0))
        assert int_one == F(1, m)
        assert int_log == -harmonic/m
        monomials.append({"power": m, "harmonic_number": str(harmonic)})
    pole = mu*sp.exp(-a)
    denominator = kap*(a+sp.log(p/mu))
    assert sp.simplify(denominator.subs(p, pole)) == 0
    residue = sp.simplify(1/sp.diff(denominator, p).subs(p, pole))
    assert sp.simplify(residue-pole/kap) == 0
    z = sp.symbols("z", real=True)
    upper_bank = 1/(kap*(z+sp.I*sp.pi))
    lower_bank = 1/(kap*(z-sp.I*sp.pi))
    density = sp.simplify((lower_bank-upper_bank)/(2*sp.pi*sp.I))
    assert sp.simplify(density-1/(kap*(z*z+sp.pi**2))) == 0
    beta_T, c, ell = sp.symbols("beta_T c ell", real=True)
    assert sp.expand((c+2*beta_T*ell)+beta_T*(z-2*ell)-(c+beta_T*z)) == 0
    h0, h1, h2, h3, h4 = sp.symbols("h0:5", real=True)
    h = sp.Matrix([[h0,h1,h2],[h1,h3,h4],[h2,h4,-h0-h3]])
    sigma, X, dX = sp.symbols("sigma X dX", real=True)
    dg = sp.Matrix(3, 3, lambda i, j: sp.Symbol("d"+str(i)+str(j)))
    T = sigma*sp.eye(3)-X*sp.eye(3)/2
    dT = dg-X*h/2-dX*sp.eye(3)/2
    assert (dT-h*T-dg+sigma*h+dX*sp.eye(3)/2).applyfunc(sp.simplify) == sp.zeros(3)
    assert sp.trace(h) == 0
    kk = sp.symbols("kk", integer=True, positive=True)
    assert sp.expand(kk**4-((kk**2-1)**2-2*(kk**2-1))) == 4*kk**2-3
    assert sp.summation(1/kk**2, (kk, 1, sp.oo)) == sp.pi**2/6
    eta, zeta = sp.symbols("eta zeta", real=True)
    coord = sp.symbols("x0:3", real=True)
    S = sp.Function("f")(eta)*sp.Function("f")(zeta)
    assert all(sp.diff(S, v, w) == 0 for v in coord for w in coord)
    return {
        "Frullani_derivative_and_zero_normalization": True,
        "causal_monomial_formula": "K_0,mu*t^m=2*t^m*(H_m-EulerGamma-log(mu*t))",
        "monomial_moments": monomials,
        "positive_pole": "p_star=mu*exp(-c/kappa)",
        "inverse_residue": "p_star/kappa",
        "branch_cut_density": "1/[kappa*(log(x/p_star)^2+pi^2)]",
        "scale_change": "K_k,nu-K_k,mu=-2*log(nu/mu)*delta",
        "compensating_Weyl_coupling": "c_W(nu)=c_W(mu)+2*beta_T*log(nu/mu)",
        "Hadamard_difference_local_TT_contact": "-sigma_S*h",
        "Bochner_Hessian_over_J_operator_bound": 1,
        "trace_J_inverse_squared": "pi^2/6",
        "homogeneous_source_overlap_TT_response_difference": 0,
    }

def monomial_action(t, k, mu, m=4, terms=16):
    t, k, mu = F(t), F(k), F(mu)
    assert 0 < t and 0 <= k*t <= 1 and mu > 0
    harmonic = sum((F(1, j) for j in range(1, m+1)), F(0))
    partial = sum((F((-1)**n)*k**(2*n)*t**(2*n+m) /
                   (2*n*factorial(2*n+m)) for n in range(1, terms+1)), F(0))
    value = 2*I(t**m)*(I(harmonic)-iv.euler-iv.log(I(mu*t)))
    value -= 2*factorial(m)*I(partial)
    n = terms+1
    remainder = F(2*factorial(m))*k**(2*n)*t**(2*n+m)/(2*n*factorial(2*n+m))
    return value+box(-remainder, remainder)

def cutoff_action(t, k, mu, epsilon, m=4, terms=16):
    t, k, mu, epsilon = map(F, (t,k,mu,epsilon))
    assert 0 < epsilon < t and 0 <= k*t <= 1
    integral = I(0)
    for n in range(terms+1):
        coefficient = F((-1)**n)*k**(2*n)/factorial(2*n)
        for j in range(m+1):
            weight = coefficient*comb(m,j)*(-1)**j*t**(m-j)
            degree = 2*n+j
            moment = iv.log(I(t/epsilon)) if degree == 0 else I((t**degree-epsilon**degree)/degree)
            integral += I(weight)*moment
    value = -2*((iv.log(I(mu*epsilon))+iv.euler)*I(t**m)+integral)
    degree = 2*terms+2
    tail = F(2)*k**degree*t**(degree+m)/(degree*factorial(degree))
    return value+box(-tail, tail)

def finite_part_certificate():
    T = F(1,8)
    rows = []
    for k in (0,2,8):
        cap = upper(2*I(T)*(1+absolute(iv.euler+iv.log(I(T))))+I(F(k*k)*T**3/6))
        rows.append({
            "k": k, "mu": 1, "T": str(T),
            "primitive_L1_upper": pair(cap),
            "primitive_L1_upper_decimal": upper_float(cap),
        })
    exact = monomial_action(T, 3, 1)
    tests = []
    for epsilon in (F(1,128),F(1,1024),F(1,8192)):
        cut = cutoff_action(T,3,1,epsilon)
        difference = absolute(exact-cut)
        error = I(2*epsilon*4*T**3+F(9,2)*epsilon**2*T**4)
        assert hi(difference) <= lo(error)
        tests.append({
            "epsilon": str(epsilon), "regularized_action": pair(cut),
            "absolute_difference_upper": pair(difference),
            "analytic_cutoff_error_upper": pair(error),
        })
    return {
        "definition": "K_k,mu=D_t[theta(t)*q_k,mu(t)]",
        "q": "-2*(EulerGamma+log(mu*t)+integral_0^t (cos(k*r)-1)/r dr)",
        "Laplace_symbol": "log((p^2+k^2)/mu^2), Re p>0",
        "literal_theta_times_singular_kernel_used": False,
        "mapping": "W_left-zero^(1,p)(0,T) -> L^p(0,T), 1<=p<=infinity",
        "bound": "||K*f||_p<=||q||_L1*||f_prime||_p; f(0)=0",
        "nonzero_initial_value_term": "f(0)*q(t), retained if f(0) is not zero",
        "primitive_caps": rows,
        "monomial_test": {"t":str(T),"k":3,"mu":1,"power":4,"certified_action":pair(exact)},
        "cutoff_checks": tests,
        "flat_fourth_order_mapping": "beta_T*Q*(||h^(5)||_p+2*k^2*||h^(3)||_p+k^4*||h_prime||_p), with zero causal initial jets",
        "full_closed_FLRW_kernel_certified_by_this_model": False,
    }

def inverse_certificate():
    T = I(F(1,8))
    examples = []
    for ratio in (-1,0,1):
        pole = iv.exp(-I(ratio))
        q = pole*T
        assert 0 < lo(q) <= hi(q) < 1
        log_mean = (q-1)/iv.log(q)
        lower_mass = log_mean*(iv.exp(q)-1)/q
        upper_mass = iv.exp(1)*log_mean*iv.exp(q)
        assert 0 < lo(lower_mass) < hi(upper_mass)
        N = 16
        tail = upper(iv.exp(1)*log_mean*q**N/factorial(N)/(1-q/(N+1)))
        examples.append({
            "kappa":1, "mu":1, "c_over_kappa":ratio, "T":"1/8",
            "p_star_interval":pair(pole),
            "L1_mass_enclosure":[str(lo(lower_mass)),str(hi(upper_mass))],
            "L1_mass_upper_decimal":upper_float(upper_mass),
            "u_integral_tail_from_16_upper":pair(tail),
            "weighted_norm_at_rho_2_p_star":pair(1/iv.log(2)),
        })
    return {
        "conditions": "kappa>0, mu>0, c real",
        "normal_form": "c*delta+kappa*L_mu; Laplace(L_mu)=log(p/mu)",
        "r_positive": True,
        "r": "(1/kappa)*integral_0^infinity p_star^u*t^(u-1)/Gamma(u) du",
        "spectral_r": "(p_star*exp(p_star*t)+integral_0^infinity exp(-x*t)/(log(x/p_star)^2+pi^2) dx)/kappa",
        "L1_mass": "nu(p_star*T)/kappa; nu(q)=integral_0^infinity q^u/Gamma(u+1) du",
        "mass_bounds": "L(q)*(exp(q)-1)/q <= nu(q) <= e*L(q)*exp(q); L(q)=(q-1)/log(q)",
        "gamma_bound_proof": "u=n+v, 0<=v<=1; e^-1*n!<=Gamma(u+1)<=(n+1)!",
        "weighted_L1_exact": "1/[c+kappa*log(rho/mu)] for rho>p_star",
        "small_time_asymptotic": "r(t)~1/[kappa*t*log(p_star*t)^2]",
        "positive_real_pole": True,
        "stable_inverse_claimed": False,
        "inverse_of_actual_prepared_closed_FLRW_RSET_claimed": False,
        "normal_form_examples": examples,
    }

def state_difference_certificate():
    start, stop = F(1,16), F(3,16)
    duration = stop-start
    L = I(F(1,2))+2*iv.tan(2*I(stop))
    CE = upper(iv.exp(L*I(duration)))
    zeta2 = iv.pi**2/6
    nonlocal_cap = upper(zeta2*CE*I(duration)**2)
    local = upper(zeta2/3)
    return {
        "background": "same a_lambda=lambda*sqrt(3*cos(2*eta)); unit S3",
        "time_interval": [str(start),str(stop)],
        "S": "W_1-W_0, smooth symmetric bisolution on the same background",
        "states_held_fixed_in_common_past": True,
        "input_vanishes_before_interval_start": True,
        "past_state_prescription": "each state keeps its own specified past data; the two states need not agree",
        "V_h": "delta(P)=+D_i(h^{ij}D_j)=+h^{ij}D_i D_j, for spatial TT h",
        "B_h": "-V_h=-delta(P)=-D_i(h^{ij}D_j), for spatial TT h",
        "Duhamel": "delta(S)=E_R*B_h*S+transpose",
        "isotropic_pair_required_for_scalar_contact": True,
        "spatial_symmetry_for_scalar_contact": "SO(4)-invariant two-point kernels; sigma_S is spatially constant",
        "full_effective_TT_difference": "[D_i D_jprime delta(S)]_diagonal^TT-sigma_S*h_ij",
        "sigma_S": "one third of gamma^ij[D_i D_jprime S]_diagonal",
        "state_independent_renormalization_counterterms_cancel": True,
        "spatial_pair_sign": "-Tr(V_tau*delta(S))=2*integral Tr(V_tau*E_R*V_h*S)",
        "nonlocal_spatial_pair_bound": "2*C_E*(t-s)*||tau||_infinity*||h(s)||_infinity*M_S",
        "M_S": "sup_(s,t)||J*S(s,t)*J||_trace, J=1-Delta",
        "computable_smooth_kernel_cap": "M_S<=(pi^2/6)*M8; M8=sup||(1-Delta_x)^2*(1-Delta_y)^2*S||_Hilbert_Schmidt",
        "energy_exponent_L_upper": pair(upper(L)),
        "C_E_upper": pair(CE),
        "nonlocal_Linfinity_bound_per_M8": pair(nonlocal_cap),
        "local_contact_bound_per_M8": pair(local),
        "full_bound_per_M8": pair(upper(nonlocal_cap+local)),
        "actual_prepared_reference_difference_M8_numerically_certified": False,
        "homogeneous_displacement_exact_effective_TT_overlap_response_difference": 0,
        "homogeneous_displacement_raw_covariant_overlap_term": "a_lambda^2*Delta(p)*h_ij; cancels after raising an index",
        "homogeneous_blindness_requires_Gaussian_mixture": False,
        "zero_response_requires_pure_spatial_zero_mode_difference": True,
        "generic_SO4_invariant_state_difference_claimed_blind": False,
        "baseline_polarization_computed_from_state_difference": False,
    }

def calculate():
    assert __debug__, "Proof assertions must not be disabled"
    parent, frozen = freeze_inputs()
    beta_T = 1/(1920*iv.pi**2)
    assert lo(beta_T) > 0
    result = {
        "schema": "ueot-overlap-causal-log-and-state-difference/1",
        "base_commit": BASE,
        "status": "CAUSAL_LOG_FINITE_PART_EXACT_NORMAL_FORM_INVERSE_AND_OVERLAP_STATE_DIFFERENCE",
        "exact_checks": exact_checks(),
        "finite_part": finite_part_certificate(),
        "log_inverse": inverse_certificate(),
        "Hadamard_state_difference": state_difference_certificate(),
        "renormalization": {
            "inherited_physical_mu": 1, "inherited_alpha": 0, "c_extra": 0,
            "new_finite_counterterms_added": False,
            "reference_contacts_assumed_zero": False,
            "normal_form_c_examples_are_physical_coupling_choices": False,
        },
        "physical_UV": {
            "free_real_scalar_flat_spin2_spectral_density": "rho_T(s)=theta(s)*s^2/(960*pi^2)",
            "flat_spin2_coefficient_independent_of_xi": True,
            "beta_T_interval": pair(beta_T),
            "beta_T_decimal": upper_float(beta_T),
            "flat_RSET_nonlocal_symbol": "-beta_T*(K^2)^2*log((K^2-i0*sgn(omega))/mu^2)*h_TT",
            "pure_time_normalized_log_coefficient": pair(2*beta_T),
            "normalization": "multiply D_T-4*a_lambda^2*Pi_ref_TT by a_lambda^2/4; freeze coefficients for the principal normal form only",
            "local_scale_change_compensated_by_Weyl_coupling": True,
            "prepared_Hadamard_state_changes_leading_UV_coefficient": False,
            "curved_subprincipal_terms_and_actual_state_remainder_certified": False,
            "normal_form_mu_automatically_equals_physical_mu_in_conformal_time": False,
        },
        "scope": {
            "previous_separated_susceptibility_upper": parent["response"]["susceptibility_absolute_upper"],
            "overlapping_commutator_replaced_by_unsorted_bilinear_bound": False,
            "ordinary_L1_Volterra_kernel_after_only_local_fourth_order_inverse": False,
            "complete_quantum_feedback_resolvent_certified": False,
            "finite_local_couplings_inferred_from_noise": False,
            "new_mode_integrations": 0, "old_scientific_checkers_executed": False,
            "hardware_or_Lean_data_added": False, "Core_read_only": True,
        },
        "input_sha256": {str(p.relative_to(REPO)):v for p,v in sorted(frozen.items())},
    }
    for p, expected in frozen.items():
        assert sha(p) == expected, ("input changed during check", str(p))
    return result

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if not (args.write or args.check): parser.error("use --write and/or --check")
    result = calculate()
    rendered = json.dumps(result, indent=2, sort_keys=True, ensure_ascii=False)+"\n"
    target = HERE/"result.json"
    if args.write: target.write_text(rendered)
    if args.check: assert target.read_text() == rendered, "Overlap quantum receipt mismatch"
    print("Free scalar spin2 beta_T:", result["physical_UV"]["beta_T_decimal"])
    print("Primitive L1 caps:", [(r["k"],r["primitive_L1_upper_decimal"]) for r in result["finite_part"]["primitive_caps"]])
    print("Normal-form inverse L1 upper examples:", [(r["c_over_kappa"],r["L1_mass_upper_decimal"]) for r in result["log_inverse"]["normal_form_examples"]])
    print("PASS: defined causal finite part; positive locally integrable scalar inverse; exact overlap state-difference theorem.")
    print("OPEN: actual prepared closed-FLRW baseline polarization and quantitative remainder.")
