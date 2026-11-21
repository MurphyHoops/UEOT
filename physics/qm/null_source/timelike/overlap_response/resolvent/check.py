"""Exact local TT retarded resolvent and a same-space feedback obstruction.

This inverts Einstein plus an explicit R2/C2 parameter family on the archived
FLRW background. The inherited extra coefficients remain zero. It does not
collect or invert all fixed contact terms of the reference quantum RSET.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sympy as sp

HERE = Path(__file__).resolve().parent
TL = HERE.parents[1]
REPO = HERE.parents[5]
BASE = "c57e2f411e58dc1dae60de8f3c97fbd680e46d8b"
T = F(3, 16)
LAMBDA = 32768

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def freeze_inputs():
    old = [TL / "operational_response" / name for name in
           ["CONTRACT.md", "review.py", "review.json"]]
    frozen = {}
    for path in old:
        relative = str(path.relative_to(REPO))
        assert path.read_bytes() == subprocess.check_output(
            ["git", "show", BASE + ":" + relative], cwd=REPO)
        frozen[path] = sha(path)
    current = [HERE.parent / "local" / name for name in
               ["check.py", "README.md", "result.json"]]
    current += [HERE / "check.py", HERE / "README.md"]
    for path in current:
        frozen[path] = sha(path)
    local = json.loads((HERE.parent / "local" / "result.json").read_text())
    assert local["status"] == "EXACT_GENERAL_TT_WEYL_BACH_OPERATOR_VERIFIED"
    return frozen, local

def symbolic_local_identities():
    eta, u = sp.symbols("eta u", real=True)
    nu = sp.symbols("nu", integer=True, positive=True)
    lam = sp.symbols("lam", positive=True)
    b, z = sp.symbols("b z", real=True)
    c = sp.symbols("c", real=True, nonzero=True)
    k = nu**2 - 1
    G = (sp.sin(nu*u)*sp.cos(u) - nu*sp.cos(nu*u)*sp.sin(u)) / (2*nu*k)
    assert [sp.simplify(sp.diff(G, u, j).subs(u, 0)) for j in range(4)] == [0, 0, 0, 1]
    assert sp.simplify(sp.diff(G, u, 4) + (2*k+4)*sp.diff(G, u, 2) + k*k*G) == 0
    assert sp.simplify(sp.diff(G, u) - sp.sin(nu*u)*sp.sin(u)/(2*nu)) == 0
    assert sp.simplify(sp.diff(G, u, 2) + k*G - sp.sin(nu*u)*sp.cos(u)/nu) == 0
    m0, m1 = sp.symbols("m0 m1", real=True)
    K = -m0*(sp.diff(G, u, 2) + k*G) + m1*sp.diff(G, u)
    target = sp.sin(nu*u)/nu * (-m0*sp.cos(u) + m1*sp.sin(u)/2)
    assert sp.simplify(K-target) == 0
    a2 = 3*lam**2*sp.cos(2*eta)
    H = -sp.tan(2*eta)
    R = -2/(lam**2*sp.cos(2*eta)**3)
    assert sp.trigsimp(sp.diff(a2, eta)/(2*a2)-H) == 0
    assert sp.trigsimp(6/a2*(sp.diff(H, eta)+H**2+1)-R) == 0
    assert sp.trigsimp(sp.diff(R, eta)-6*sp.tan(2*eta)*R) == 0
    q = z-4*b*R
    gamma = a2/(4*c)
    m = sp.simplify(gamma*q)
    expected_m = 3*lam**2*z*sp.cos(2*eta)/(4*c) + 6*b/(c*sp.cos(2*eta)**2)
    expected_mp = -3*lam**2*z*sp.sin(2*eta)/(2*c) + 24*b*sp.sin(2*eta)/(c*sp.cos(2*eta)**3)
    assert sp.simplify(m-expected_m) == 0
    assert sp.simplify(sp.diff(m, eta)-expected_mp) == 0
    assert sp.trigsimp(sp.diff(m, eta)-gamma*(2*H*q+sp.diff(q, eta))) == 0
    h, hp, Rp = sp.symbols("h hp Rp", real=True)
    delta_hessian = (-(H*h+hp/2)*Rp + h*H*Rp)/a2
    assert sp.simplify(delta_hessian + Rp*hp/(2*a2)) == 0
    A = sp.symbols("A", positive=True)
    majorant = (sp.cosh(sp.sqrt(A)*u)-1-A*u*u/2)/(A*A)
    assert sp.simplify(sp.diff(majorant, u, 2)-A*majorant-u*u/2) == 0
    assert sp.simplify(majorant.subs(u, 0)) == 0
    assert sp.simplify(sp.diff(majorant, u).subs(u, 0)) == 0
    x = sp.symbols("x")
    wrong_l2 = (x+8)**2
    correct_l2 = (x+4)*(x+16)
    assert wrong_l2.subs(x, -4) == 16 and correct_l2.subs(x, -4) == 0
    omitted_data = sp.cos((nu-1)*u)-sp.cos((nu+1)*u)
    assert omitted_data.subs(u, 0) == 0
    assert sp.diff(omitted_data, u).subs(u, 0) == 0
    assert sp.simplify(sp.diff(omitted_data, u, 2).subs(u, 0)-4*nu) == 0
    mm = sp.symbols("m", real=True)
    rr = sp.symbols("r")
    frequency_polynomial = rr**2-(2*k+4+mm)*rr+k*(k+mm)
    assert sp.expand(sp.discriminant(frequency_polynomial, rr)-((mm+4)**2+16*k)) == 0
    return {
        "S3_TT_l_min": 2,
        "kappa_l": "l*(l+2)=(l+1)^2-1",
        "W_l": "(d_eta^2+l^2)*(d_eta^2+(l+2)^2)",
        "retarded_G_initial_jets": [0, 0, 0, 1],
        "G_l": "[sin(l*u)/l-sin((l+2)*u)/(l+2)]/[4*(l+1)]",
        "G_first": "sin((l+1)*u)*sin(u)/(2*(l+1))",
        "G_second_plus_kappa_G": "sin((l+1)*u)*cos(u)/(l+1)",
        "local_equation": "(z-4*b*R)*D_T*h-4*b*R_prime*h_prime+(4*c/a^2)*W*h=F",
        "gamma": "a^2/(4*c)",
        "m": "3*lambda^2*z*cos(2*eta)/(4*c)+6*b/(c*cos(2*eta)^2)",
        "m_prime": "-3*lambda^2*z*sin(2*eta)/(2*c)+24*b*sin(2*eta)/(c*cos(2*eta)^3)",
        "self_adjoint_normal_form": "W*h+(m*h_prime)_prime+kappa*m*h=gamma*F",
        "local_Volterra_kernel": "sin((l+1)*(t-s))/(l+1)*[-m(s)*cos(t-s)+m_prime(s)*sin(t-s)/2]",
        "no_spurious_derivatives_of_c_over_a2_in_W_block": True,
        "mixed_index_pressure_cancellation_checked": True,
        "missing_S3_curvature_term_negative_control": "l=2,frequency=2: wrong=16, correct=0",
        "missing_two_initial_data_negative_control": "cos(l*t)-cos((l+2)*t): h(0)=h_prime(0)=0, h_second(0)=4*(l+1)",
        "constant_coefficient_frequency_polynomial": "r^2-(2*kappa+4+m)*r+kappa*(kappa+m)",
        "constant_coefficient_discriminant": "(m+4)^2+16*kappa",
        "constant_coefficient_instability_test": "m<-kappa gives one negative squared frequency; not used to claim actual FLRW instability",
    }

def exact_constants():
    cosine_lower = 1-F(3, 8)**2/2
    assert cosine_lower == F(119, 128)
    r = 1/cosine_lower
    assert F(3, 8)*r == F(48, 119) < F(1, 2)
    assert r < 2
    gamma_coefficient = F(3, 4)*LAMBDA**2
    A_z_general = F(3, 4) + T/2 * F(3, 2)*F(3, 8)
    A_b = 6*r**2 + T/2*24*F(3, 8)*r**3
    assert A_z_general == F(411, 512)
    assert A_b == F(13467648, 1685159)
    A_z = A_z_general*LAMBDA**2
    assert gamma_coefficient == 805306368
    assert A_z == 861929472
    u_cap = 48*F(2, 3)*F(1, 2)*(1+F(1, 4))
    w_cap = 12*F(2, 3)*(1+F(1, 4))*(8+8*F(1, 4))
    remainder_cap = T*F(4, 3)*(F(3, 2)*u_cap+w_cap/2)
    multiplication_cap = F(2, 3)*(8+8+8*F(1, 4))
    assert u_cap == 20 and w_cap == 100
    assert remainder_cap == 20 and multiplication_cap == 12
    assert 1/(1-T) <= F(4, 3)
    return {
        "T": str(T), "lambda": LAMBDA,
        "cos_2T_lower": str(cosine_lower),
        "sec_2T_upper": str(r), "tan_2T_upper": "48/119",
        "Gamma_cap": "805306368/abs(c)",
        "A_cap": "(861929472*abs(z)+(13467648/1685159)*abs(b))/abs(c)",
        "A_lambda_general": "((411/512)*lambda^2*abs(z)+(13467648/1685159)*abs(b))/abs(c)",
        "physical_coefficients_inherited_from_frozen_contract": True,
        "constants_apply_to_auxiliary_c_nonzero_family": True,
        "constants_evaluated_at_physical_workpoint": False,
        "high_frequency_residual_cap_times_lambda2": str(remainder_cap),
        "high_frequency_multiplication_cap_times_lambda2": str(multiplication_cap),
    }

def high_frequency_division():
    t, k = sp.symbols("t k", real=True)
    def derivative_coefficient(f):
        return sp.expand(2*(1+t*t)*sp.diff(f, t)+2*t*f)
    def derivative_operator(coefficients):
        out = [sp.Integer(0)]*(len(coefficients)+1)
        for j, value in enumerate(coefficients):
            out[j] += derivative_coefficient(value)
            out[j+1] += value
        return [sp.expand(value) for value in out]
    d1 = 2*t
    d2 = derivative_coefficient(d1)
    P = [d2+k+4, -d1, sp.Integer(1)]
    first = derivative_operator(P)
    second = derivative_operator(first)
    full = []
    for j in range(5):
        value = second[j]
        if j < len(first): value += -2*t*first[j]
        if j < len(P): value += k*P[j]
        full.append(sp.expand(value))
    u = 48*t*(1+t*t)
    v = 12*(1+t*t)*(k+8+24*t*t)
    target = [k*k+v, u, 2*k+4, 0, 1]
    assert all(sp.expand(a-b) == 0 for a, b in zip(full, target))
    assert sp.expand(v-derivative_coefficient(u)-12*(1+t*t)*(k-8*t*t)) == 0
    return {
        "actual_background_not_frozen_coefficients": True,
        "fixed_spatial_mode": "l=2, kappa=8, H^s-normalized TT harmonic",
        "test_sequence": "h_n=chi(eta)*cos(n*(eta-3/32))*Y_2; chi smooth, 0<=chi<=1, compact in (1/16,1/8), equals 1 near 3/32",
        "sequence_C_Hs_norm": "1",
        "d": "a^-2=sec(2*eta)/(3*lambda^2)",
        "P": "d*d_eta^2-d_prime*d_eta+d_second+(kappa+4)*d",
        "division_identity": "D_T*P=d*W+u*d_eta+v",
        "u": "48*d*tan(2*eta)*(1+tan(2*eta)^2)",
        "v_minus_u_prime": "12*d*(1+tan(2*eta)^2)*(kappa-8*tan(2*eta)^2)",
        "inverse_after_integration_by_parts": "D_T_ret^-1(d*W)=P-D_T_ret^-1(u*d_eta+v); the latter remainder is C-to-C bounded",
        "same_space_feedback_lower_bound": "||D_T_ret^-1(d*W*h_n)||_C_Hs >= (n^2/3-32)/lambda^2",
        "coupled_lower_bound": "4*abs(c)*(n^2/3-32)/lambda^2",
        "sufficient_frequency_to_exceed_one": "n^2>96+3*lambda^2/(4*abs(c))",
        "uniform_old_same_space_small_gain_for_nonzero_c": False,
        "applies_at_physical_workpoint": False,
        "proves_actual_Pi_ref_feedback_obstruction": False,
        "claim_that_this_high_frequency_sequence_is_within_a_separate_EFT_cutoff": False,
    }

def calculate():
    assert __debug__, "Do not disable scientific assertions"
    frozen, local = freeze_inputs()
    identities = symbolic_local_identities()
    constants = exact_constants()
    obstruction = high_frequency_division()
    result = {
        "schema": "ueot-local-overlap-retarded-resolvent/1",
        "status": "EXPLICIT_LOCAL_PARAMETER_FAMILY_RESOLVENT_AND_GAIN_OBSTRUCTION_CERTIFIED",
        "reviewed_base": BASE,
        "local_input_schema": local.get("schema"),
        "local_input_status": local.get("status"),
        "symbolic": identities,
        "constant_family": constants,
        "high_frequency_obstruction": obstruction,
        "retarded_inverse": {
            "operator_class": "explicit deformation geometric suboperator L_z_bextra_cextra",
            "auxiliary_F_symbol": "already normalized forcing f=4*a^2*external_mixed_stress; not Pi_ref[h]",
            "includes_reference_RSET_response": False,
            "domain": "C([0,3/16];H^s_TT(S3)), all l>=2 and all degeneracies",
            "regularity_interpretation": "modewise classical fourth-order equation; full equation as a distribution",
            "explicit_parameter_c_nonzero_required": True,
            "nondegeneracy_of_z_minus_4bR_required_when_c_nonzero": False,
            "four_initial_data": "h=h_prime=h_second=h_third=0 at eta=0; extend by zero to the past",
            "G_uniform_bound": "abs(G_l(u))<=u^3/6",
            "kernel_uniform_bound": "abs(K_l(t,s))<=A*(t-s), A=M0+T*M1/2",
            "solution": "sum_{j>=0} V^j[G*(gamma*F)]",
            "uniform_response_bound": "Gamma*||F||*sum_{j>=0} A^j*T^(2*j+4)/(2*j+4)!",
            "closed_majorant_A_positive": "Gamma*||F||*(cosh(sqrt(A)*T)-1-A*T^2/2)/A^2",
            "majorant_A_zero": "Gamma*||F||*T^4/24",
            "tail_after_j_0_through_N": "Gamma*||F||*A^(N+1)*T^(2*N+6)/(2*N+6)!*cosh(sqrt(A)*T)",
            "geometric_tail_when_rho_lt_1": "first_omitted_term/(1-rho), rho=A*T^2/((2*N+8)*(2*N+7))",
            "small_coupling_or_small_V_norm_required": False,
            "large_finite_majorant_proves_physical_stability": False,
        },
        "inherited_physical_point": {
            "physical_mu": 1, "alpha_AE": 0, "z": 1, "b_extra": 0, "c_extra": 0,
            "actual_equation": "D_T h - 4 a^2 Pi_ref_TT[h] = 4 a^2 F",
            "four_data_of_explicit_nonzero_c_family_imposed_here": False,
            "nonzero_c_obstruction_claimed_for_vanishing_extra_c": False},
        "c_zero_branch": {
            "physical_workpoint_q": 1,
            "physical_geometric_suboperator": "D_T",
            "reference_quantum_response_removed_when_c_extra_zero": False,
            "equation": "q*D_T*h+q_prime*h_prime=F, q=z-4*b*R",
            "sufficient_regular_case": "inf_abs_q>0; then h_second+(2H+q_prime/q)*h_prime+kappa*h=F/q",
            "number_of_initial_data": 2,
            "degenerate_q_crossing_included": False,
            "c_zero_same_model_as_nonzero_c": False,
            "order_reduction_same_exact_equation": False,
        },
        "scope": {
            "explicit_Einstein_plus_R2_C2_parameter_family_inverted": True,
            "all_fixed_reference_RSET_contacts_collected": False,
            "full_quantum_retarded_RSET_operator_inverted": False,
            "overlap_quantum_kernel_regular_remainder_bound_proved_here": False,
            "local_fourth_order_inverse_automatically_removes_logarithmic_quantum_loss": False,
            "nonlinear_SCE_constructed": False,
            "full_quantum_noise_propagated_through_response": False,
            "inherited_extra_coefficients_zero_preserved": True,
            "fixed_reference_contacts_assumed_zero": False,
            "Core_unique_physical_selection": False,
        },
        "new_mode_integrations": 0,
        "new_geometry_ODE_integrations": 0,
        "predecessor_checkers_executed": 0,
        "input_sha256": {str(p.relative_to(REPO)): h for p, h in sorted(frozen.items())},
    }
    for path, expected in frozen.items():
        assert sha(path) == expected, "Input changed during local resolvent check"
    return result

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if not (args.write or args.check):
        parser.error("use --write and/or --check")
    result = calculate()
    rendered = json.dumps(result, indent=2, sort_keys=True, ensure_ascii=False)+"\n"
    path = HERE / "result.json"
    if args.write: path.write_text(rendered)
    if args.check: assert path.read_text() == rendered, "Local resolvent receipt mismatch"
    print("Gamma cap:", result["constant_family"]["Gamma_cap"])
    print("A cap:", result["constant_family"]["A_cap"])
    print("High-frequency obstruction:", result["high_frequency_obstruction"]["coupled_lower_bound"])
    print("PASS: explicit local parameter-family inverse and its gain obstruction; fixed physical prescription preserved, quantum inverse remains open.")
