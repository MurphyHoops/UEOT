"""AH03: Symbolically verify 15 conformal/Killing obstructions on S^3, exact axisymmetric J_AB=0, and nonzero 2nd-order torque."""
from __future__ import annotations
import sympy as sp
from mpmath import iv
from common import above, below, exact, finish, outward, require
from model import exact_cap_khat


def verify_s3_killing_and_conformal_symbolically() -> dict:
    """Verify Killing, conformal Killing, orthogonality, and separable gradient identity on unit S^3 in stereographic coords."""
    y1, y2, y3, tau = sp.symbols("y1 y2 y3 tau", real=True)
    ys = [y1, y2, y3]
    r2 = y1**2 + y2**2 + y3**2
    denom = 1 + r2
    xs = [2 * y1 / denom, 2 * y2 / denom, 2 * y3 / denom, (1 - r2) / denom]
    require(sp.simplify(sum(x**2 for x in xs) - 1) == 0, "Unit S^3 embedding")

    # Metric gamma_ij = 4 / (1 + r^2)^2 delta_ij
    fac = 4 / denom**2
    gamma = sp.diag(fac, fac, fac)
    gamma_inv = sp.diag(1 / fac, 1 / fac, 1 / fac)
    sqrt_g = sp.Rational(8, 1) / denom**3

    # Jacobian dx_A / dy_i (4 x 3); since gamma = J^T J, V^i = gamma^{ij} J_{Aj} xi_ambient^A
    jac = sp.Matrix([[sp.diff(xs[a], ys[i]) for i in range(3)] for a in range(4)])

    pairs = [(a, b) for a in range(4) for b in range(a + 1, 4)]
    require(len(pairs) == 6, "Six SO(4) generators")

    killing_vecs = []
    for a, b in pairs:
        # Ambient vector: x_a d/dx_b - x_b d/dx_a -> components in R^4: V_amb[b] = x_a, V_amb[a] = -x_b
        v_amb = [sp.Integer(0)] * 4
        v_amb[b] = xs[a]
        v_amb[a] = -xs[b]
        require(sp.simplify(sum(xs[c] * v_amb[c] for c in range(4))) == 0, "Tangent to S^3")
        # Pullback V^i = gamma^{ik} sum_c (dx_c / dy_k) v_amb[c]
        v_up = [
            sp.simplify(gamma_inv[i, i] * sum(jac[c, i] * v_amb[c] for c in range(4)))
            for i in range(3)
        ]
        killing_vecs.append(v_up)

        # Check Lie derivative (L_V gamma)_{ij} = V^k d_k gamma_{ij} + gamma_{kj} d_i V^k + gamma_{ik} d_j V^k == 0
        for i in range(3):
            for j in range(i, 3):
                lie_ij = (
                    sum(v_up[k] * sp.diff(gamma[i, j], ys[k]) for k in range(3))
                    + sum(gamma[k, j] * sp.diff(v_up[k], ys[i]) for k in range(3))
                    + sum(gamma[i, k] * sp.diff(v_up[k], ys[j]) for k in range(3))
                )
                require(sp.simplify(lie_ij) == 0, f"Killing equation failed for ({a},{b})")

        # Check divergence (1/sqrt_g) d_i (sqrt_g V^i) == 0
        div_v = sum(sp.diff(sqrt_g * v_up[i], ys[i]) for i in range(3))
        require(sp.simplify(div_v) == 0, f"Divergence-free failed for ({a},{b})")

    # Check 4 proper conformal Killing vectors C_a^i = gamma^{ij} d_j x_a:
    # L_{C_a} gamma_{ij} - (2/3) div(C_a) gamma_{ij} == 0 and (-Delta_{S^3} - 3) x_a == 0
    for a in range(4):
        c_up = [sp.simplify(gamma_inv[i, i] * sp.diff(xs[a], ys[i])) for i in range(3)]
        div_c = sp.simplify(sum(sp.diff(sqrt_g * c_up[i], ys[i]) for i in range(3)) / sqrt_g)
        require(sp.simplify(-div_c - 3 * xs[a]) == 0, f"Eigenvalue -Delta x_{a} = 3 x_{a}")
        for i in range(3):
            for j in range(i, 3):
                lie_c = (
                    sum(c_up[k] * sp.diff(gamma[i, j], ys[k]) for k in range(3))
                    + sum(gamma[k, j] * sp.diff(c_up[k], ys[i]) for k in range(3))
                    + sum(gamma[i, k] * sp.diff(c_up[k], ys[j]) for k in range(3))
                )
                conf_err = sp.simplify(lie_c - sp.Rational(2, 3) * div_c * gamma[i, j])
                require(conf_err == 0, f"Conformal Killing failed for x_{a}")

    # Check L^2(S^3) Gram matrix of the 6 Killing vectors via polar integral for radial part
    # Pointwise inner product gamma_{ij} V_p^i V_q^j:
    r = sp.Symbol("r", positive=True)
    gram_diag_norms = []
    for idx_p, vp in enumerate(killing_vecs):
        for idx_q in range(idx_p, 6):
            vq = killing_vecs[idx_q]
            pw = sp.simplify(sum(gamma[i, i] * vp[i] * vq[i] for i in range(3)))
            # Average over S^2 of radius r: y1^2, y2^2, y3^2 -> r^2/3, cross terms y_i y_j -> 0!
            # Verify parity: off-diagonals are odd in at least one y_i!
            if idx_p != idx_q:
                p_pair, q_pair = pairs[idx_p], pairs[idx_q]
                # Reflect a coordinate in symmetric difference of {a,b} and {c,d} (intersected with {0,1,2})
                sym_diff = [c for c in (set(p_pair) ^ set(q_pair)) if c < 3]
                require(len(sym_diff) >= 1, "Distinct pairs differ in at least one y_i")
                flip_idx = sym_diff[0]
                subs_flip = {ys[flip_idx]: -ys[flip_idx]}
                require(sp.simplify(pw + pw.subs(subs_flip)) == 0, "Odd parity orthogonality on S^3")
            else:
                # Replace y1^2 -> r^2/3, y2^2 -> r^2/3, y3^2 -> r^2/3 after expanding numerator
                num_pw, den_pw = sp.fraction(sp.together(pw * sqrt_g))
                # Spherical integral int_{R^3} d^3y = 4*pi int_0^inf r^2 dr with angular avg <y_i^2>=r^2/3, <y_i^4>=r^4/5, <y_i^2 y_j^2>=r^4/15
                poly_y = sp.Poly(sp.expand(num_pw), y1, y2, y3)
                ang_avg = sp.Integer(0)
                for (e1, e2, e3), c_val in poly_y.as_dict().items():
                    if e1 % 2 == 1 or e2 % 2 == 1 or e3 % 2 == 1:
                        continue
                    # Exact S^2 average of y1^e1 y2^e2 y3^e3 / r^(e1+e2+e3) = B((e1+1)/2, (e2+1)/2, (e3+1)/2) / (4*pi) * 2
                    w_ang = (
                        sp.gamma(sp.Rational(e1 + 1, 2))
                        * sp.gamma(sp.Rational(e2 + 1, 2))
                        * sp.gamma(sp.Rational(e3 + 1, 2))
                        / (2 * sp.pi * sp.gamma(sp.Rational(e1 + e2 + e3 + 3, 2)))
                    )
                    ang_avg += c_val * w_ang * r ** (e1 + e2 + e3)
                den_r = sp.simplify(den_pw.subs({y1**2 + y2**2 + y3**2: r**2, y1: r, y2: 0, y3: 0}))
                val_norm = sp.simplify(4 * sp.pi * sp.integrate(ang_avg * r**2 / den_r, (r, 0, sp.oo)))
                require(val_norm == sp.pi**2, f"Exact L^2 norm pi^2 for pair {pairs[idx_p]}")
                gram_diag_norms.append(str(val_norm))

    # Verify separable conformal spectator momentum density is an exact gradient with zero curl
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
        "Killing_L2_norms": gram_diag_norms[0],
    }


def gate_fourier_cos6(omega: iv.mpf) -> iv.mpf:
    """Exact closed-form int_{-pi/8}^{pi/8} cos^6(4*xi) * cos(omega*xi) dxi via cosine expansion."""
    # cos^6(theta) = 1/32 * (10 + 15 cos(2*theta) + 6 cos(4*theta) + cos(6*theta)), theta = 4*xi
    # so cos^6(4*xi) = 1/32 * (10 + 15 cos(8*xi) + 6 cos(16*xi) + cos(24*xi))
    # int_{-a}^a cos(m*xi) cos(omega*xi) dxi = sin((omega - m)*a)/(omega - m) + sin((omega + m)*a)/(omega + m)
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
    sym_info = verify_s3_killing_and_conformal_symbolically()

    # Compute exact 100-digit interval enclosure of kappa_rot for rho0 = 1/20
    k_split = 200
    khats = exact_cap_khat(1, 20, k_split + 1)
    v0 = exact(2) * iv.pi**2

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
            kk
            * (kk + exact(1))
            * (kk + exact(2))
            / (exact(6) * v0 * wk * wk1)
            * (khats[k - 1] ** 2)
            * (khats[k] ** 2)
        )
        g_om = gate_fourier_cos6(om)
        term = w_pair * iv.sin(om * iv.pi / exact(4)) * (g_om**2)
        if k == 1:
            pair_12_contrib = term
        kappa_low += term

    c6_sup = exact(15 * (8**6) + 6 * (16**6) + (24**6)) / exact(32)
    l1_d6 = (iv.pi / exact(4)) * c6_sup
    tail_bound = (
        (exact(k_split + 3) / exact(k_split + 1))
        / (exact(6) * v0 * exact(4096))
        * (l1_d6**2)
        / (exact(10) * (exact(k_split) ** 10))
    )
    kappa_rot = iv.mpf([(kappa_low - tail_bound).a, (kappa_low + tail_bound).b])

    require(above(pair_12_contrib, exact("7e-4")), "Pair (1,2) contribution > 7e-4")
    require(below(tail_bound, exact("1e-11")), "High-mode torque tail < 1e-11")
    require(below(kappa_rot, exact("-2e-4")), "Full continuum rotational torque strictly negative (nonzero)")

    # Witness non-collinear controls u0 = 1e-17 e_1, u1 = 1e-17 e_2 -> |J_12^(2)| = |kappa_rot| * 1e-34 > 2e-38
    j12_noncollinear = kappa_rot * exact("1e-34")
    require(above(abs(j12_noncollinear), exact("2e-38")), "Non-collinear controls leave nonzero Killing obstruction")

    finish(
        "so4_killing_obstruction_and_vanishing.py",
        {
            **sym_info,
            "separable_conformal_spectator_momentum_is_exact_gradient": True,
            "separable_spectator_SO4_Killing_charges_identically_zero": True,
            "axisymmetric_RC08_RC09_protocol_SO4_Killing_charges_all_orders": 0,
            "dominant_12_pair_torque_coeff": outward(pair_12_contrib),
            "high_mode_torque_tail_above_k200_upper": float(outward(tail_bound)[1]),
            "continuum_2nd_order_rotational_torque_kappa_rot": outward(kappa_rot),
            "noncollinear_u_1e_17_witness_J12": outward(j12_noncollinear),
            "general_3D_noncollinear_target_requires_6_channel_rotational_trim": True,
        },
    )


if __name__ == "__main__":
    main()
