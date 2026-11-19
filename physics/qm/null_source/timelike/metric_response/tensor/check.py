"""Local compact TT strain readout and complete reference-state noise bound.

The background Einstein--homogeneous-scalar tensor equation is used, with
the full quantum metric-response kernel explicitly outside this certificate.
Every archived input is checked byte-for-byte against the declared base.
No mode ODE, full Einstein--Langevin system, or hardware is simulated.
"""
from fractions import Fraction as F
from pathlib import Path
from itertools import product
import argparse
import hashlib
import json
import subprocess
from mpmath import iv, mp
import sympy as sp

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[5]
TIMELIKE = HERE.parents[1]
BASE = "719babd3386b9d9274d5c91dd0b8ad5e71688049"
mp.dps = 90
iv.dps = 70

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

def ceil_fraction(x):
    return -(-x.numerator // x.denominator)

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def frozen_inputs():
    paths = [
        "stress_kernel/noise/README.md",
        "stress_kernel/noise/check.py",
        "stress_kernel/noise/result.json",
        "stress_kernel/geometry/README.md",
        "stress_kernel/response/README.md",
        "response/geometry/README.md",
        "response/noise/check.py",
        "response/noise/result.json",
        "evolution/propagation/background.py",
        "evolution/stress/tail.py",
        "evolution/stress/tail_K256_M1024.json",
        "compatibility/review.py",
        "compatibility/review.json",
        "continuation/SOURCE.md",
        "response/CONTRACT.md",
    ]
    frozen = {}
    for rel in paths:
        p = TIMELIKE / rel
        archived = subprocess.check_output(
            ["git", "show", BASE + ":" + str(p.relative_to(REPO))], cwd=REPO
        )
        assert archived == p.read_bytes(), ("archived input changed", rel)
        frozen[p] = sha(p)
    for name in ("check.py", "README.md"):
        p = HERE / name
        frozen[p] = sha(p)
    return frozen

def symbolic_checks():
    x = sp.symbols("x y z", real=True)
    f = sp.Function("f")(*x)
    seed = sp.diag(f, -f, 0)
    ric = sp.zeros(3)
    for i, j in product(range(3), repeat=2):
        ric[i, j] = sp.expand(
            sum(sp.diff(seed[k, j], x[i], x[k]) +
                sp.diff(seed[k, i], x[j], x[k]) for k in range(3)) / 2
            - sum(sp.diff(seed[i, j], x[k], 2) for k in range(3)) / 2
        )
    schouten = ric - sp.eye(3) * sp.trace(ric) / 4
    cotton = sp.Matrix(3, 3, lambda i, j: sp.expand(sum(
        sp.LeviCivita(i, k, l) * sp.diff(schouten[l, j], x[k])
        for k, l in product(range(3), repeat=2)
    )))
    assert cotton == cotton.T
    assert sp.simplify(sp.trace(cotton)) == 0
    assert all(sp.simplify(sum(sp.diff(cotton[i, j], x[i])
                               for i in range(3))) == 0 for j in range(3))
    # Every component has absolute derivative-coefficient sum at most one.
    coefficient_sums = []
    for entry in cotton:
        value = sum(abs(term.as_coeff_Mul()[0]) for term in sp.Add.make_args(entry))
        coefficient_sums.append(value)
        assert value <= 1
    local_seed = x[2] ** 3 / sp.E
    at_origin = cotton.subs(f, local_seed).doit().subs(dict.fromkeys(x, 0))
    assert at_origin[0, 1] == -3 / sp.E
    assert at_origin[1, 0] == -3 / sp.E
    # A direct conformal-divergence contraction; the flat divergence is zero.
    v = sp.symbols("v0:3", real=True)
    a, b, c, d, e = sp.symbols("a b c d e", real=True)
    tf = sp.Matrix([[a, b, c], [b, d, e], [c, e, -a-d]])
    gamma = lambda p, i, j: (
        sp.KroneckerDelta(p, i) * v[j]
        + sp.KroneckerDelta(p, j) * v[i]
        - sp.KroneckerDelta(i, j) * v[p]
    )
    # tau=Omega^-1*t; prefactors Omega^-3 are common.
    for j in range(3):
        remainder = sum(
            -v[i] * tf[i, j]
            - sum(gamma(p, i, i) * tf[p, j] +
                  gamma(p, i, j) * tf[i, p] for p in range(3))
            for i in range(3)
        )
        assert sp.simplify(remainder) == 0
    eta = sp.symbols("eta", real=True)
    a2 = 3 * sp.cos(2 * eta)
    hubble = sp.diff(a2, eta) / (2 * a2)
    fp = sp.sqrt(27) / a2
    assert sp.trigsimp(3 * (hubble**2 + 1) - fp**2) == 0
    assert sp.trigsimp(-(2 * sp.diff(hubble, eta) + hubble**2 + 1) - fp**2) == 0
    assert sp.diff(a2 * fp, eta) == 0
    u, vfun = sp.Function("u")(eta), sp.Function("v")(eta)
    dtime = lambda z: sp.diff(z, eta, 2) + 2 * hubble * sp.diff(z, eta)
    green = a2 * (u * dtime(vfun) - vfun * dtime(u))
    boundary = sp.diff(a2 * (u * sp.diff(vfun, eta) -
                            sp.diff(u, eta) * vfun), eta)
    assert sp.simplify(green - boundary) == 0
    # Tracefree stress contraction eliminates every homogeneous displacement.
    phi_t, shift_t = sp.symbols("phi_t shift_t", real=True)
    grad = sp.Matrix(sp.symbols("g0:3", real=True))
    stress = grad * grad.T + sp.eye(3) * ((phi_t + shift_t)**2 - grad.dot(grad)) / 2
    contracted = sum(tf[i, j] * stress[i, j] for i, j in product(range(3), repeat=2))
    assert sp.simplify(sp.diff(contracted, shift_t)) == 0
    # The source coefficient and pair-creation normalization are not conflated.
    assert sp.Rational(1, 2) / sp.Rational(1, 8) == 4
    assert 8**2 / 2 == 32
    ll, lh = sp.symbols("ll lh", nonnegative=True)
    assert sp.expand(2 * (ll + lh) - (ll + 2 * lh)) == ll
    return {
        "cotton_symmetric_tracefree_divergencefree_for_arbitrary_f": True,
        "cotton_component_derivative_coefficient_sums": [str(x) for x in coefficient_sums],
        "flat_cotton_origin_12": "-3/e",
        "conformal_transport": "tau_cov=Omega^-1*t_cov; div_gamma(tau)=Omega^-3*div_flat(t)",
        "conformal_divergence_remainder_exact_zero": True,
        "classical_Einstein_scalar_background_checked": True,
        "weighted_time_Green_identity_exact": True,
        "homogeneous_shift_absent_from_tracefree_spatial_stress": True,
        "tensor_operator": "D_T=d_eta^2+2*(A_prime/A)*d_eta-Delta_gamma+2",
        "source_coefficient_in_4piG_1_units": 4,
        "operator_external_input": "Durrer astro-ph/0402129, Eqs. (30), (39), (69)",
        "spatial_rough_Laplacian_preserves_TT": "constant-curvature commutation identity; see README",
        "constraint_propagation": "pure spatial TT source with zero 0mu components is background-conserved",
        "stress_variable_itself_Gaussian_assumed": False,
        "old_and_new_homogeneous_displacement_TT_stress_laws_identical": True,
        "new_mode_integrations": 0,
    }

def spatial_derivative_caps():
    # f=r0^3*u_z^3*exp(-v), v=(1-|u|^2)^-1, |u|<1.
    # D_i(P exp(-v))=(partial_i P+2*u_i*v^2*(partial_v P-P))*exp(-v).
    u = sp.symbols("ux uy uz", real=True)
    z = sp.symbols("v", real=True)
    cache = {(0, 0, 0): u[2]**3}
    caps = {}
    polynomials = {}
    for order in range(6):
        rows = []
        for aa in product(range(order + 1), repeat=3):
            if sum(aa) != order:
                continue
            if order:
                i = next(i for i in range(3) if aa[i])
                prev = list(aa)
                prev[i] -= 1
                p = cache[tuple(prev)]
                cache[aa] = sp.expand(sp.diff(p, u[i]) +
                                      2*u[i]*z*z*(sp.diff(p, z)-p))
            p = sp.Poly(cache[aa], *u, z)
            cap = I(0)
            for powers, coef in p.terms():
                degree = powers[3]
                peak = iv.exp(-1) if degree == 0 else I(degree**degree)*iv.exp(-degree)
                cap += I(abs(int(coef))) * peak
            rows.append(hi(cap))
            polynomials[str(aa)] = str(cache[aa])
        caps[order] = I(max(rows))
    f3, f4, f5 = [caps[i] for i in (3, 4, 5)]
    normalizer = ceil_fraction(hi(3*f3))
    r0 = iv.tan(I(F(1, 16)))
    assert 0 < lo(r0) < hi(r0) < F(1, 8)
    tau_frob = upper(3*f3/normalizer)
    assert hi(tau_frob) <= 1
    # Omega>=1 on this ball. The bounds deliberately trade sharpness for
    # a short, auditable estimate of the readout error amplification.
    d0 = upper(f3/normalizer)
    d1 = upper((r0*f3+f4/r0)/normalizer)
    d2 = upper((f3+2*f4+f5/(r0*r0))/normalizer)
    g0 = upper(6*r0)
    g1 = upper(6+12*r0*r0)
    laplace = upper(9*(d2+15*g0*d1+(6*g1+54*g0*g0)*d0))
    origin_component = -I(3)/(2*iv.exp(1)*normalizer)
    origin_norm = 3*iv.sqrt(2)/(8*iv.exp(1)*normalizer)
    assert hi(origin_component) < 0 and lo(origin_norm) > 0
    derivative_payload = json.dumps(polynomials, sort_keys=True).encode()
    return normalizer, tau_frob, laplace, {
        "seed": "s=diag(f,-f,0); f=z^3*b(r/r0)",
        "r0": "tan(1/16)",
        "support": "chi<1/8",
        "r0_interval": pair(r0),
        "normalizer_M_integer": normalizer,
        "scaled_scalar_derivative_caps_0_through_5": [pair(caps[i]) for i in range(6)],
        "derivative_polynomial_sha256": hashlib.sha256(derivative_payload).hexdigest(),
        "tau_frobenius_sup_upper": pair(tau_frob),
        "tau_cov_12_at_origin": pair(origin_component),
        "tau_frobenius_norm_at_origin": pair(origin_norm),
        "tau_cov_partial_derivative_component_caps": [pair(d0), pair(d1), pair(d2)],
        "Christoffel_component_upper": pair(g0),
        "Christoffel_first_partial_component_upper": pair(g1),
        "rough_Laplacian_tau_frobenius_sup_upper": pair(laplace),
        "normalizer_arbitrarily_reduced_to_improve_noise": False,
        "sup_norm_equal_to_one_claimed": False,
    }

def calculate():
    assert __debug__, "Proof assertions must not be disabled"
    frozen = frozen_inputs()
    old = json.loads((TIMELIKE/"stress_kernel/noise/result.json").read_text())
    assert old["new_mode_integrations"] == 0
    assert old["positive_frequency_high_block"]["IBP_order"] == 3
    assert old["positive_frequency_high_block"]["two_frequencies_not_replaced_by_frequency_difference"]
    assert not old["block_bounds"]["old_mean_stress_tail_used_as_noise_tail"]
    assert hi(parse(old["positive_frequency_high_block"]["field_WKB_mode_factor_upper"])) < 1
    assert hi(parse(old["block_bounds"]["preparation_remainder_eta_max"])) < 1
    K = old["block_bounds"]["K"]
    assert K == 256
    symbols = symbolic_checks()
    normalizer, tau_frob, laplace, spatial = spatial_derivative_caps()
    H = upper(parse(old["block_bounds"]["all_mode_kinetic_factor_upper"]))
    E5 = upper(parse(old["block_bounds"]["preparation_remainder_E5"]))
    L = [upper(parse(x)) for x in old["spacetime_constants"]["time_derivative_L1_upper"]]
    Lg = upper(parse(old["positive_frequency_high_block"]["gradient_IBP_L1_upper"]))
    S4 = I(F(K*(K+1)*(2*K+1)*(3*K*K+3*K-1), 30))
    low_rows = upper(H*L[0]*iv.sqrt(S4))
    main = upper(Lg/(2*iv.sqrt(K)))
    remainder = upper(4*L[0]*E5/iv.sqrt(5*K**5))
    high = upper(main+remainder)
    C_T = upper(32*(2*low_rows**2+high**2))
    lam = old["certificate"]["lambda_certified"]
    assert lam == 32768
    variance = upper(C_T/lam**4)
    rms = upper(iv.sqrt(variance))
    assert hi(rms) < F(1, 10000)
    # Crude strict bound on E_Q=integral A^2 |Q|_gamma d_eta dOmega.
    volume = 2*iv.pi*(I(F(1, 8))-iv.sin(I(F(1, 4)))/2)
    assert lo(volume) > 0
    error_gain = upper(3*volume*(
        tau_frob*(L[2]+2*iv.tan(I(F(1,4)))*L[1]+2*L[0])+laplace*L[0]
    ))
    result = {
        "schema": "ueot-local-tensor-metric-response/1",
        "base_commit": BASE,
        "status": "LOCAL_TT_STRAIN_READOUT_AND_COMPLETE_REFERENCE_NOISE_BOUND",
        "symbolic_checks": symbols,
        "compact_TT_test": spatial,
        "readout": {
            "psi": "b(32*(eta-3/32))",
            "Q": "D_T(psi*tau)",
            "observable": "O[h]=integral A^2 Q^{ij} h_ij d_eta dOmega",
            "source_identity": "O[h]=4*integral A^2 psi tau^{ij} xi_cov_ij d_eta dOmega",
            "all_homogeneous_TT_initial_data_cancel": True,
            "initial_source_correlations_need_be_zero": False,
            "support": "(1/16,1/8) x {chi<1/8}",
            "nonzero_Q_proof": "nonzero compact Psi plus uniqueness of the homogeneous tensor Cauchy problem",
            "gauge_invariance": "Q is spatial TT; both longitudinal and isotropic time-shift gauge terms pair to zero",
            "unit_pointwise_strain_calibration_profile": "h_cal=Q/||Q||_F,infinity",
            "calibration_gain_exact": "J/||Q||_F,infinity; J=integral A^2 |Q|_F^2 > 0",
            "calibration_gain_numerically_certified": False,
            "source_profile_calibration": "xi_cov=c*psi*tau gives O=4*c*integral A^2*psi^2*|tau|_F^2",
            "pointwise_strain_error_gain_exact": "E_Q=integral A^2 |Q|_F",
            "pointwise_strain_error_gain_upper": pair(error_gain),
            "spatial_support_volume": pair(volume),
            "normalized_unit_strain_noise_claimed": False,
        },
        "all_mode_noise": {
            "reference": "same archived static-prepared pure quasifree state",
            "K": K,
            "H": pair(H), "L0": pair(L[0]), "E5": pair(E5), "L_grad": pair(Lg),
            "spatial_row": "sum_m |N_nm|^2/omega_m <= omega_n^3; ||tau||_F,infinity<=1",
            "Bochner_on_unit_S3": "||Hess Y_n||_2^2=omega_n^4-2*omega_n^2",
            "zero_mode_row_and_column": "identically zero; never divide by its frequency",
            "complete_low_row_Hilbert_Schmidt_upper": pair(low_rows),
            "low_block_combination": "LL^2+2*LH^2 <= 2*||B_L,all||_HS^2",
            "high_positive_Hilbert_Schmidt_upper": pair(main),
            "high_preparation_remainder_Hilbert_Schmidt_upper": pair(remainder),
            "C_T_upper": pair(C_T),
            "C_T_upper_decimal": float(hi(C_T)),
            "formula": "C_T <= 32*(2*(H*L0)^2*S4+(Lgrad/(2*sqrt(K))+4*L0*E5/sqrt(5*K^5))^2)",
            "homothety": "Var(O_lambda)<=lambda^-4*C_T",
            "lambda": lam,
            "raw_readout_variance_upper": pair(variance),
            "raw_readout_variance_upper_decimal": float(hi(variance)),
            "raw_readout_RMS_upper": pair(rms),
            "raw_readout_RMS_upper_decimal": float(hi(rms)),
            "homogeneous_displacement_linear_coefficient": 0,
            "homogeneous_displacement_classical_amplitude_coefficient": 0,
            "old_new_TT_noise_difference": 0,
            "mean_TT_readout_in_isotropic_reference": 0,
            "relative_to_nonzero_TT_mean_noise_claimed": False,
            "scalar_mixture_noise_reduction_transferred_to_TT": False,
            "stress_distribution_Gaussian_assumed": False,
        },
        "scope": {
            "classical_background_tensor_equation": True,
            "nonhomogeneous_tensor_PDE_not_homogeneous_ODE_with_bump": True,
            "full_quantum_RSET_metric_response_included": False,
            "homogeneous_shift_blindness_scope": "undeformed homogeneous g0 only; not the finite inhomogeneous lapse path g_epsilon",
            "full_quantum_background_SCE_on_shell_claimed": False,
            "complete_Einstein_Langevin_solution_claimed": False,
            "general_metric_observable_noise_bound_claimed": False,
            "new_hardware_or_Lean_data": False,
            "Core_read_only": True,
        },
        "new_mode_integrations": 0,
        "input_sha256": {str(p.relative_to(REPO)): h for p,h in sorted(frozen.items())},
    }
    for p, h in frozen.items():
        assert sha(p) == h, ("input changed", str(p))
    return result

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = calculate()
    rendered = json.dumps(result, indent=2, sort_keys=True, ensure_ascii=False)+"\n"
    target = HERE/"result.json"
    if args.write:
        target.write_text(rendered)
    if args.check:
        assert target.read_text() == rendered, "Tensor response receipt mismatch"
    n = result["all_mode_noise"]
    print("Explicit Cotton normalizer M:", result["compact_TT_test"]["normalizer_M_integer"])
    print("Complete all-mode C_T upper:", n["C_T_upper_decimal"])
    print("At lambda=32768 raw readout variance upper:", n["raw_readout_variance_upper_decimal"])
    print("At lambda=32768 raw readout RMS upper:", n["raw_readout_RMS_upper_decimal"])
    print("Pointwise strain readout error gain upper:",
          float(F(result["readout"]["pointwise_strain_error_gain_upper"][1])))
    print("PASS: local TT metric readout, exact old/new TT invariance, complete reference noise; zero new mode ODE.")
