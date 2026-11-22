"""Separated-window full TT RSET susceptibility with an all-mode norm bound.

This checker evaluates exact algebra and outward intervals only. It imports
frozen background/W2 jet helpers without invoking their mode-evolution code.
The resulting norm acts between explicitly separated test spaces; it is not
an overlapping semiclassical feedback or Einstein--Langevin resolvent bound.
"""
from fractions import Fraction as F
from pathlib import Path
from math import factorial
import argparse
import hashlib
import json
import subprocess
import sys
from mpmath import iv, mp
import sympy as sp

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[5]
TIMELIKE = HERE.parents[1]
BASE = "f2b09fb2b8fd2235bde7017b060fc07ecc44b441"
K = 256
LAMBDA = 32768
sys.path.insert(0, str(TIMELIKE / "evolution/propagation"))
sys.path.insert(0, str(TIMELIKE / "evolution/stress"))
import background as bg
import tail as old_tail
mp.dps = 90
iv.dps = 70
Jet = bg.Jet

def I(x):
    if hasattr(x, "_mpi_"):
        return x
    if isinstance(x, mp.mpf):
        return iv.mpf(x)
    x = F(x)
    return iv.mpf(x.numerator) / x.denominator

def endpoint(x, j):
    return mp.make_mpf(x._mpi_[j])

def rational(x):
    sign, man, power, _ = x._mpf_
    return F((-1 if sign else 1) * man) * F(2) ** power

def pair(x):
    return [str(rational(endpoint(x, j))) for j in (0, 1)]

def lo(x):
    return F(pair(x)[0])

def hi(x):
    return F(pair(x)[1])

def upper(x):
    return I(endpoint(x, 1))

def box(a, b):
    return iv.mpf([endpoint(I(a), 0), endpoint(I(b), 1)])

def parse(x):
    return box(F(x[0]), F(x[1]))

def absolute(x):
    return I(max(abs(endpoint(x, 0)), abs(endpoint(x, 1))))

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def trunc(j, n):
    return Jet(j.c[:n + 1])

def deriv(j):
    return Jet([(n + 1) * j.c[n + 1] for n in range(j.n)])

def frozen_inputs():
    tensor = json.loads((TIMELIKE / "metric_response/tensor/result.json").read_text())
    noise = json.loads((TIMELIKE / "stress_kernel/noise/result.json").read_text())
    relatives = set(tensor["input_sha256"]) | set(noise["input_sha256"])
    relatives |= {
        "physics/qm/null_source/timelike/metric_response/tensor/result.json",
        "physics/qm/null_source/timelike/stress_kernel/CONTRACT.md",
        "physics/qm/null_source/timelike/compatibility/CONTRACT.md",
        "physics/qm/null_source/timelike/metric_response/CONTRACT.md",
    }
    frozen = {}
    for relative in sorted(relatives):
        p = REPO / relative
        archived = subprocess.check_output(["git", "show", BASE + ":" + relative], cwd=REPO)
        assert p.read_bytes() == archived, ("inherited source changed", relative)
        frozen[p] = sha(p)
    for receipt in (tensor, noise):
        for relative, expected in receipt["input_sha256"].items():
            assert sha(REPO / relative) == expected, ("parent receipt hash mismatch", relative)
    for name in ("check.py", "README.md"):
        frozen[HERE / name] = sha(HERE / name)
    return tensor, noise, frozen

def symbolic_checks():
    eps, a2, momentum = sp.symbols("eps a2 momentum", real=True)
    aa, bb, cc, dd, ee = sp.symbols("aa bb cc dd ee", real=True)
    h = sp.Matrix([[aa, bb, cc], [bb, dd, ee], [cc, ee, -aa - dd]])
    q = sp.eye(3) + eps * h
    determinant = q.det()
    assert sp.diff(determinant, eps).subs(eps, 0) == 0
    # At eps=0 the exact inverse derivative is -h. The first-order inverse
    # suffices to compute the Hamiltonian derivative at fixed canonical data.
    assert (q * (sp.eye(3) - eps*h) - sp.eye(3)).diff(eps).subs(eps, 0) == sp.zeros(3)
    grad = sp.Matrix(sp.symbols("g0:3", real=True))
    H = momentum**2 / (2*a2*sp.sqrt(determinant))
    H += a2*sp.sqrt(determinant)*(grad.T*(sp.eye(3)-eps*h)*grad)[0]/2
    variation = sp.diff(H, eps).subs(eps, 0)
    assert sp.simplify(variation + a2*(grad.T*h*grad)[0]/2) == 0
    lam, OP, cov_re, cov_im = sp.symbols("lam OP cov_re cov_im", real=True)
    # O_P=4 int A^2 psi tau:T, whereas a_lambda^2=lambda^2 A^2.
    generator = -lam**2*OP/8
    assert sp.diff(generator, OP) == -lam**2/8
    kubo = -sp.I*lam**2*((cov_re+sp.I*cov_im)-(cov_re-sp.I*cov_im))/8
    assert sp.simplify(kubo-lam**2*cov_im/4) == 0
    vp, vf = sp.symbols("vp vf", positive=True)
    assert sp.simplify(lam**2*2*sp.sqrt(vp*vf)/8-lam**2*sp.sqrt(vp*vf)/4) == 0
    # Isotropic covariant pressure contains p*a^2*h, which cancels when
    # raising the first index. It must not be reinserted in the TT source.
    pressure = sp.symbols("pressure")
    mixed = (sp.eye(3)-eps*h)*(pressure*a2*(sp.eye(3)+eps*h))/a2
    assert mixed.diff(eps).subs(eps, 0).applyfunc(sp.simplify) == sp.zeros(3)
    # A compact homogeneous scalar has no first-order TT metric forcing:
    # the trace variation and the spatial gradient of its background vanish.
    trace_h = sp.trace(h)
    assert trace_h == 0
    # Time compression changes ||psi^(j)||_1 by 2^(j-1), not 2^j.
    compression = [F(2)**(j-1) for j in range(4)]
    assert compression == [F(1, 2), F(1), F(2), F(4)]
    # Nonzero causal time ordering is not the commutator of one smeared
    # observable with itself. This exact oscillator control is independent
    # of the UEOT numerical certificate.
    t, u = sp.symbols("t u", positive=True)
    control = sp.integrate((t-u)*sp.sin(2*u), (u, 0, t))
    assert sp.simplify(control-(2*t-sp.sin(2*t))/4) == 0
    assert sp.simplify(control.subs(t, sp.pi/4)-(sp.pi/8-sp.Rational(1,4))) == 0
    return {
        "Hamiltonian_spatial_TT_variation": "-a_lambda^2*h^{ij}*partial_i(Phi)*partial_j(Phi)/2",
        "generator": "G_h=-lambda^2*O_P/8, modulo a central constant",
        "retarded_convention": "d<O_F>/d_epsilon=i<[G_h,O_F]>",
        "Kubo_covariance_formula": "chi=lambda^2*Im(<O_P O_F>_connected)/4",
        "Cauchy_factor": "abs(chi)<=sqrt(C_P*C_F)/(4*lambda^2)",
        "pressure_metric_variation_cancels_in_mixed_anisotropic_source": True,
        "homogeneous_scalar_first_order_TT_forcing": 0,
        "time_derivative_L1_compression_factors": [str(x) for x in compression],
        "oscillator_unsorted_same_observable_commutator": 0,
        "oscillator_ordered_sine_integral_at_pi_over_4": "pi/8-1/4>0",
        "negative_control_scope": "Time ordering cannot be removed for overlapping supports; box profile admits smooth positive approximations.",
    }

def growth_bound(eta_end):
    # Aleft is the auxiliary A_phys(-1/8) lower bound on the smooth splice.
    # The actual prepared scale at eta=-1/8 is A0, not Aleft.
    A0 = iv.sqrt(3)
    Aleft = iv.sqrt(3*iv.cos(I(F(1,4))))
    Aright = iv.sqrt(3*iv.cos(I(F(1,8))))
    Aend = iv.sqrt(3*iv.cos(2*I(eta_end)))
    preparation = (A0+Aright-2*Aleft)/Aleft
    radius = preparation+iv.log(A0/Aright)+iv.log(A0/Aend)
    H = upper(iv.exp(2*radius)/2)
    assert lo(Aend) > 1 and lo(radius) > 0
    return H, {
        "eta_end": str(eta_end),
        "preparation_eta": ["-1/8", "-1/16"],
        "preparation_total_log_variation_upper": pair(preparation),
        "total_log_variation_upper": pair(radius),
        "all_nonzero_mode_field_factor_upper": pair(H),
        "bound": "|A*u_k|^2<=H/sqrt(k^2-1), k>=2",
        "derivation": "static alpha=1,beta=0; |alpha|+|beta|<=exp(integral|A_prime/A|)",
        "past_H_reused_outside_its_domain": False,
    }

def phase_constants(eta_lo, eta_hi):
    # Fresh uniform time jets for every k>K, on this window only.
    qv = bg.q_box(eta_lo, eta_hi, 7)
    q = [Jet([qv[j+n]/factorial(n) for n in range(4)]) for j in range(5)]
    delta = Jet.const(box(0, F(1, (K+1)**2)), 3)
    _, B, _, _, Rn = old_tail.normalized_defect(q, delta)
    Wscaled = B.sqrt()
    sigma = Wscaled + old_tail.power(delta, 3)*Rn/(2*Wscaled)
    assert lo(B.c[0]) > F(1,2) and hi(B.c[0]) < 2
    assert lo(sigma.c[0]) > F(1,2)
    cu = 1/(iv.sqrt(2)*I(lo(B.c[0]))**I(F(1,4)))
    assert hi(cu) < 1
    rec = B.sqrt().sqrt().inverse()
    # Interval copies are independent, so this encloses k and l separately.
    amplitude = rec*rec
    coefficients = []
    for j in range(4):
        h = Jet([I(F(1, factorial(j))) if n == j else I(0) for n in range(4)])
        f = h*amplitude
        for _ in range(3):
            f = deriv(f/trunc(sigma, f.n))
        coefficients.append(upper(absolute(f.c[0])))
    return coefficients, {
        "eta_interval": [str(eta_lo), str(eta_hi)],
        "IBP_order": 3,
        "phase": "phi_k_prime=k*sigma_k; pair phase derivative=k*sigma_k+l*sigma_l",
        "W2_B_interval": pair(B.c[0]),
        "sigma_interval": pair(sigma.c[0]),
        "field_W2_mode_factor_upper": pair(cu),
        "gradient_time_derivative_coefficients_abs_upper": [pair(x) for x in coefficients],
        "fresh_time_jets_not_transplanted_from_past": True,
        "pair_frequencies_independent": True,
        "boundary_terms": "zero for every C-infinity compact time test in its window",
    }

def window_certificate(name, bounds, L, E5):
    H, growth = growth_bound(bounds[1])
    coeffs, phase = phase_constants(*bounds)
    Lg = upper(sum((a*b for a, b in zip(coeffs, L)), I(0)))
    S4 = I(F(K*(K+1)*(2*K+1)*(3*K*K+3*K-1), 30))
    low = upper(H*L[0]*iv.sqrt(S4))
    main = upper(Lg/(2*iv.sqrt(K)))
    error = upper(4*L[0]*E5/iv.sqrt(5*K**5))
    C = upper(32*(2*low*low+(main+error)**2))
    # ||psi||_W31=sum_j ||psi^(j)||_1 gives a more familiar, coarser norm.
    max_g = I(max(hi(x) for x in coeffs))
    sobolev_cap = upper(iv.sqrt(32*(2*H*H*S4+
                        (max_g/(2*iv.sqrt(K))+4*E5/iv.sqrt(5*K**5))**2)))
    return C, {
        "name": name,
        "time_support_closure": [str(x) for x in bounds],
        "time_derivative_L1_upper": [pair(x) for x in L],
        "preparation_growth": growth,
        "positive_frequency_phase": phase,
        "gradient_IBP_L1_upper": pair(Lg),
        "complete_low_row_Hilbert_Schmidt_upper": pair(low),
        "high_positive_Hilbert_Schmidt_upper": pair(main),
        "high_preparation_remainder_Hilbert_Schmidt_upper": pair(error),
        "C_T_upper": pair(C),
        "C_T_upper_decimal": float(hi(C)),
        "raw_readout_variance_upper_at_lambda": pair(upper(C/LAMBDA**4)),
        "raw_readout_RMS_upper_at_lambda": pair(upper(iv.sqrt(C)/LAMBDA**2)),
        "noise_norm_value_upper": pair(upper(iv.sqrt(C))),
        "noise_norm_over_sum_W31_upper": pair(sobolev_cap),
        "noise_formula": "C_T<=32*(2*(H*L0)^2*S4+(sum_j g_j*L_j/(2*sqrt(K))+4*L0*E5/sqrt(5*K^5))^2)",
    }

def calculate():
    assert __debug__, "Proof assertions must not be disabled"
    tensor, old, frozen = frozen_inputs()
    assert tensor["compact_TT_test"]["normalizer_M_integer"] == 7640
    assert hi(parse(tensor["compact_TT_test"]["tau_frobenius_sup_upper"])) <= 1
    assert tensor["new_mode_integrations"] == 0
    assert old["block_bounds"]["K"] == K
    assert old["positive_frequency_high_block"]["IBP_order"] == 3
    uv = json.loads((TIMELIKE / "evolution/stress/tail_K256_M1024.json").read_text())
    assert uv["uniform_physical_UV_tail"]["eta_interval"] == ["0", "3/16"]
    assert uv["K"] == K
    E5 = upper(parse(old["block_bounds"]["preparation_remainder_E5"]))
    assert hi(E5/(K+1)**5) < 1
    past = (F(1,16), F(1,8))
    future = (F(5,32), F(3,16))
    gap = future[0]-past[1]
    assert gap == F(1,32) > 0
    Lp = [upper(parse(x)) for x in old["spacetime_constants"]["time_derivative_L1_upper"]]
    Lf = [upper(I(F(2)**(j-1))*x) for j, x in enumerate(Lp)]
    CP, P = window_certificate("past", past, Lp, E5)
    CF, Q = window_certificate("future", future, Lf, E5)
    # This only checks transcription consistency with the older certificate.
    old_CP = hi(parse(tensor["all_mode_noise"]["C_T_upper"]))
    assert abs(hi(CP)/old_CP-1) < F(1,10**12)
    assert hi(parse(Q["preparation_growth"]["all_nonzero_mode_field_factor_upper"])) > hi(parse(P["preparation_growth"]["all_nonzero_mode_field_factor_upper"]))
    susceptibility = upper(iv.sqrt(CP*CF)/(4*LAMBDA**2))
    retarded_norm = upper(I(F(1,4*LAMBDA**2)))
    W31_norm = upper(parse(P["noise_norm_over_sum_W31_upper"])*parse(Q["noise_norm_over_sum_W31_upper"])/(4*LAMBDA**2))
    result = {
        "schema": "ueot-separated-full-TT-RSET-response/1",
        "base_commit": BASE,
        "status": "FULL_SEPARATED_WINDOW_RETARDED_RSET_AND_CERTIFIED_TEST_SPACE_NORM",
        "lambda": LAMBDA,
        "symbolic_checks": symbolic_checks(),
        "windows": {"past": P, "future": Q},
        "reuse": {
            "K": K,
            "preparation_remainder_E5_upper": pair(E5),
            "preparation_remainder_valid_eta": ["0", "3/16"],
            "past_noise_reproduced_to_relative": "1e-12",
            "parent_C_T_upper": str(old_CP),
            "mean_stress_tail_substituted_for_noise": False,
        },
        "response": {
            "input_metric": "delta_g_ij=a_lambda^2*psi_P*tau_P, delta_g_0mu=0",
            "output": "O_F=4*integral A^2*psi_F*tau_F^{ij}*T_cov_ij d_eta dOmega",
            "past_profile": "b(32*(eta-3/32))",
            "future_profile": "b(64*(eta-11/64))",
            "time_gap": str(gap),
            "spatial_test": "frozen Cotton TT tensor, M=7640, support chi<1/8, sup_Frobenius<=1",
            "retarded_response": "-i*lambda^2*<[O_P,O_F]>/8",
            "susceptibility_absolute_upper": pair(susceptibility),
            "susceptibility_absolute_upper_decimal": float(hi(susceptibility)),
            "response_nonzero_certified": False,
            "full_smeared_RSET_derivative_for_these_windows": True,
            "retarded_theta_on_test_product": 1,
            "contact_distribution_pairing": 0,
            "all_input_metric_jets_on_output_neighborhood": 0,
            "explicit_output_metric_frame_volume_variation": 0,
            "pressure_times_h_term_on_output": 0,
            "homogeneous_displacement_first_order_response_difference": 0,
            "state_held_fixed_in_common_past": True,
            "same_local_covariant_renormalization_scheme": True,
            "finite_local_curvature_coefficients_inferred_from_this_bound": False,
            "FDT_or_stationarity_assumed": False,
        },
        "separated_test_space_bound": {
            "time_space": "C_c_infinity(I_P) and C_c_infinity(I_F)",
            "spatial_space": "smooth compact spatial TT tensors with sup_Frobenius norm",
            "elementary_test_norm": "||tau||_infinity*n_I(psi); n_I^2 is the noise_formula with actual derivative L1 norms",
            "finite_sum_completion": "projective norm inf sum_r ||tau_r||_infinity*n_I(psi_r), followed by completion",
            "bilinear_bound": "abs(chi(future,past))<=||future||_pi*||past||_pi/(4*lambda^2)",
            "operator_norm_upper": pair(retarded_norm),
            "operator_norm_upper_decimal": float(hi(retarded_norm)),
            "coarser_sum_W31_time_norm_bilinear_upper": pair(W31_norm),
            "coarser_sum_W31_time_norm_bilinear_upper_decimal": float(hi(W31_norm)),
            "arbitrary_overlapping_metric_function_space_bound": False,
        },
        "scope": {
            "new_mode_integrations": 0,
            "full_feedback_operator_including_overlap_contacts": False,
            "feedback_small_gain_certified": False,
            "Einstein_Langevin_resolvent_or_solution_claimed": False,
            "quantum_background_SCE_on_shell_claimed": False,
            "large_upper_bound_interpreted_as_actual_instability": False,
            "pointwise_or_instantaneous_stress_used": False,
            "new_hardware_or_Lean_data": False,
            "Core_read_only": True,
        },
        "input_sha256": {str(p.relative_to(REPO)): h for p, h in sorted(frozen.items())},
    }
    for p, expected in frozen.items():
        assert sha(p) == expected, ("input changed during check", str(p))
    return result

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = calculate()
    rendered = json.dumps(result, indent=2, sort_keys=True, ensure_ascii=False)+"\n"
    target = HERE / "result.json"
    if args.write:
        target.write_text(rendered)
    if args.check:
        assert target.read_text() == rendered, "Separated TT response receipt mismatch"
    print("C_P upper:", result["windows"]["past"]["C_T_upper_decimal"])
    print("C_F upper:", result["windows"]["future"]["C_T_upper_decimal"])
    print("Full separated RSET susceptibility upper:",
          result["response"]["susceptibility_absolute_upper_decimal"])
    print("Separated projective test-space norm upper:",
          result["separated_test_space_bound"]["operator_norm_upper_decimal"])
    print("PASS: separated full RSET, fresh future growth/phase bounds, zero new mode ODE.")
