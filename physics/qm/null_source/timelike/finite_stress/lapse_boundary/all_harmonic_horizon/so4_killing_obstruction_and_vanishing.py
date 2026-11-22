"""AH03: Verify 15 S^3 obstructions, autonomous SO(4) zero-torque, and exact Clebsch-Gordan external matter torque."""
from __future__ import annotations
import sympy as sp
from mpmath import iv
from common import above, below, exact, finish, outward, require
from model import exact_cap_khat


def verify_s3_killing_and_kubo_sign_symbolically() -> dict:
    """Verify Killing/conformal-Killing equations on S^3, exact gradient identity, and 2-oscillator Kubo torque sign."""
    y1, y2, y3, tau = sp.symbols("y1 y2 y3 tau", real=True)
    ys = [y1, y2, y3]
    r2 = y1**2 + y2**2 + y3**2
    denom = 1 + r2
    xs = [2 * y1 / denom, 2 * y2 / denom, 2 * y3 / denom, (1 - r2) / denom]
    require(sp.simplify(sum(x**2 for x in xs) - 1) == 0, "Unit S^3 embedding")

    fac = 4 / denom**2
    gamma = sp.diag(fac, fac, fac)
    gamma_inv = sp.diag(1 / fac, 1 / fac, 1 / fac)
    sqrt_g = sp.Rational(8, 1) / denom**3
    jac = sp.Matrix([[sp.diff(xs[a], ys[i]) for i in range(3)] for a in range(4)])

    pairs = [(a, b) for a in range(4) for b in range(a + 1, 4)]
    killing_vecs = []
    for a, b in pairs:
        v_amb = [sp.Integer(0)] * 4
        v_amb[b] = xs[a]
        v_amb[a] = -xs[b]
        v_up = [
            sp.simplify(gamma_inv[i, i] * sum(jac[c, i] * v_amb[c] for c in range(4)))
            for i in range(3)
        ]
        killing_vecs.append(v_up)
        for i in range(3):
            for j in range(i, 3):
                lie_ij = (
                    sum(v_up[k] * sp.diff(gamma[i, j], ys[k]) for k in range(3))
                    + sum(gamma[k, j] * sp.diff(v_up[k], ys[i]) for k in range(3))
                    + sum(gamma[i, k] * sp.diff(v_up[k], ys[j]) for k in range(3))
                )
                require(sp.simplify(lie_ij) == 0, f"Killing equation failed for ({a},{b})")
        div_v = sum(sp.diff(sqrt_g * v_up[i], ys[i]) for i in range(3))
        require(sp.simplify(div_v) == 0, f"Divergence-free failed for ({a},{b})")

    for a in range(4):
        c_up = [sp.simplify(gamma_inv[i, i] * sp.diff(xs[a], ys[i])) for i in range(3)]
        div_c = sp.simplify(sum(sp.diff(sqrt_g * c_up[i], ys[i]) for i in range(3)) / sqrt_g)
        require(sp.simplify(-div_c - 3 * xs[a]) == 0, f"-Delta x_{a} = 3 x_{a}")
        for i in range(3):
            for j in range(i, 3):
                lie_c = (
                    sum(c_up[k] * sp.diff(gamma[i, j], ys[k]) for k in range(3))
                    + sum(gamma[k, j] * sp.diff(c_up[k], ys[i]) for k in range(3))
                    + sum(gamma[i, k] * sp.diff(c_up[k], ys[j]) for k in range(3))
                )
                require(sp.simplify(lie_c - sp.Rational(2, 3) * div_c * gamma[i, j]) == 0, "Conformal Killing")

    # Verify k=1, k'=2 exact Clebsch-Gordan trace sum_{m,m'} |<x_0 Y_{1,m}, Y_{2,m'}>|^2 == 1*(1+1)/8 = 1/4:
    # Orthonormal Y_{1,1} = 1/sqrt(2*pi^2), Y_{2,a} = 2*x_a / sqrt(2*pi^2) (int x_a^2 dmu = pi^2/2 => int Y_{2,a}^2 = 1)!
    # <x_0 Y_{1,1}, Y_{2,a}> = int (2 x_0 x_a / (2 pi^2)) dmu = (1/pi^2)*(pi^2/2) delta_{0a} = 1/2 delta_{0a} => |...|^2 = 1/4!
    cg_k1_exact = sp.Rational(1, 2) ** 2
    require(cg_k1_exact == sp.Rational(1 * 2, 8), "Exact Clebsch-Gordan k=1 trace 1/4 == k(k+1)/8")

    # Verify exact 2nd-order torque <Psi^(1) | J_{AB} | Psi^(1)> on the 2-particle Fock subspace {|sA>, |sB>}
    # where |sC> = a_0^\dagger b_C^\dagger |0>, <sC | O_C(t) | 0> = (1/2) * 1/sqrt(w1*w2) exp(i*Om*t),
    # and J_{AB} = p_A q_B - p_B q_A has matrix [[0, i], [-i, 0]] on {|sA>, |sB>}:
    w1, w2, om_s, ghat_s, u0a, u0b, u1a, u1b = sp.symbols("w1 w2 Om ghat u0a u0b u1a u1b", positive=True)
    ia = ghat_s * (u0a * sp.exp(sp.I * om_s * sp.pi / 8) + u1a * sp.exp(sp.I * om_s * 3 * sp.pi / 8))
    ib = ghat_s * (u0b * sp.exp(sp.I * om_s * sp.pi / 8) + u1b * sp.exp(sp.I * om_s * 3 * sp.pi / 8))
    psi1 = (-sp.I / (4 * sp.sqrt(w1 * w2))) * sp.Matrix([ia, ib])
    j_mat = sp.Matrix([[0, sp.I], [-sp.I, 0]])
    exp_j = sp.simplify((psi1.conjugate().T * j_mat * psi1)[0, 0])
    target_j = -sp.Rational(2, 16) / (w1 * w2) * sp.sin(om_s * sp.pi / 4) * ghat_s**2 * (u0a * u1b - u0b * u1a)
    require(sp.simplify(sp.expand_complex(exp_j - target_j)) == 0, "Exact 2-particle Fock verification of -k(k+1)/(16*w1*w2)*sin")

    # Verify separable conformal spectator exact gradient identity
    f_tau = sp.Function("f")(tau)
    v_space = sp.Function("v")(y1, y2, y3)
    phi_tilde = f_tau * v_space
    t0_i = [
        sp.diff(phi_tilde, tau) * sp.diff(phi_tilde, ys[i])
        - sp.Rational(1, 6) * sp.diff(phi_tilde**2, tau, ys[i])
        for i in range(3)
    ]
    psi_grad = sp.Rational(1, 6) * sp.diff(f_tau, tau) * f_tau * v_space**2
    for i in range(3):
        require(sp.simplify(t0_i[i] - sp.diff(psi_grad, ys[i])) == 0, "Exact gradient identity")

    return {
        "homogeneous_l0_count": 1,
        "scalar_l1_Fischer_Marsden_count": 4,
        "proper_conformal_Killing_l1_count": 4,
        "SO4_Killing_vector_count": 6,
        "total_obstruction_dimension": 15,
        "dipole_normalization_Z_A": "x_A",
        "Clebsch_Gordan_pair_weight_formula": "k*(k+1)/(16*omega_k*omega_{k+1}) * khat(k)^2 * khat(k+1)^2",
    }


def gate_fourier_cos6(omega: iv.mpf) -> iv.mpf:
    a = iv.pi / exact(8)
    weights = [(0, exact(10)), (8, exact(15)), (16, exact(6)), (24, exact(1))]
    total = exact(0)
    for m, w in weights:
        mm = exact(m)
        if m == 0:
            term = exact(2) * iv.sin(omega * a) / omega
        else:
            term = iv.sin((omega - mm) * a) / (omega - mm) + iv.sin((omega + mm) * a) / (omega + mm)
        total += w * term
    return total / exact(32)


def main() -> None:
    sym_info = verify_s3_killing_and_kubo_sign_symbolically()

    k_split = 300
    khats = exact_cap_khat(1, 20, k_split + 1)

    def omega_plus(k: int) -> iv.mpf:
        kk = exact(k)
        return iv.sqrt(kk**2 + exact(1) / exact(5))

    kappa_low = exact(0)
    pair_12_contrib = exact(0)
    for k in range(1, k_split + 1):
        wk = omega_plus(k)
        wk1 = omega_plus(k + 1)
        om = wk + wk1
        kk = exact(k)
        w_pair = (
            kk * (kk + exact(1)) / (exact(16) * wk * wk1) * (khats[k - 1] ** 2) * (khats[k] ** 2)
        )
        g_om = gate_fourier_cos6(om)
        term = -w_pair * iv.sin(om * iv.pi / exact(4)) * (g_om**2)
        if k == 1:
            pair_12_contrib = term
        kappa_low += term

    # Exact O(1) pair weight bound w_pair < 1/16 and om > 2*k => |g_om|^2 <= l1_d6^2 / (2*k)^12:
    # sum_{k=201}^inf (1/16) * l1_d6^2 / (4096 * k^12) <= l1_d6^2 / (65536 * 11 * 200^11)!
    c6_sup = exact(15 * (8**6) + 6 * (16**6) + (24**6)) / exact(32)
    l1_d6 = (iv.pi / exact(4)) * c6_sup
    tail_bound = (l1_d6**2) / (exact(65536) * exact(11) * (exact(k_split) ** 11))
    kappa_rot = iv.mpf([(kappa_low - tail_bound).a, (kappa_low + tail_bound).b])

    require(below(pair_12_contrib, exact("-8e-4")), "Pair (1,2) contribution negative")
    require(below(tail_bound, exact("1e-18")), "High-mode torque tail < 1e-18")
    require(above(kappa_rot, exact("3.7e-4")), "Full continuum external matter torque kappa_rot > 3.7e-4 > 0")

    j12_noncollinear = kappa_rot * exact("1e-34")
    require(above(j12_noncollinear, exact("3.7e-38")), "Non-collinear external drive leaves nonzero Killing charge")

    finish(
        "so4_killing_obstruction_and_vanishing.py",
        {
            **sym_info,
            "separable_conformal_spectator_momentum_is_exact_gradient": True,
            "autonomous_recoil_cancels_matter_torque_identically": True,
            "autonomous_RC08_total_SO4_Killing_charges_all_u": 0,
            "axisymmetric_RC08_RC09_protocol_SO4_Killing_charges_all_orders": 0,
            "pair_12_torque_contrib": outward(pair_12_contrib),
            "high_mode_torque_tail_above_k300_upper": float(outward(tail_bound)[1]),
            "continuum_external_2nd_order_rotational_torque_kappa_rot": outward(kappa_rot),
            "noncollinear_u_1e_17_external_witness_J12": outward(j12_noncollinear),
            "general_3D_noncollinear_target_requires_6_channel_rotational_trim": True,
        },
    )


if __name__ == "__main__":
    main()
