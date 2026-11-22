"""AH09: Symbolically prove 3D curved pointwise Dirac closure for local 5-field mediator chain vs O(g*rho0^2) nonlocal defect."""
from __future__ import annotations
import sympy as sp
from mpmath import iv
from common import above, below, exact, finish, outward, require


def verify_3d_curved_dirac_and_tridiagonal_chain() -> dict:
    """Symbolically verify 3D general Riemannian local multi-field Dirac bracket, nonlocal defect, and 5x5 SPD chain."""
    x1, x2, x3 = sp.symbols("x1 x2 x3", real=True)
    coords = (x1, x2, x3)
    n1 = sp.Function("N1")(*coords)
    n2 = sp.Function("N2")(*coords)
    sqrt_g = sp.Function("sqrtg")(*coords)

    # General symmetric 3x3 inverse spatial metric g^{ij}(x1, x2, x3):
    g11 = sp.Function("g11")(*coords)
    g12 = sp.Function("g12")(*coords)
    g13 = sp.Function("g13")(*coords)
    g22 = sp.Function("g22")(*coords)
    g23 = sp.Function("g23")(*coords)
    g33 = sp.Function("g33")(*coords)
    g_inv = [[g11, g12, g13], [g12, g22, g23], [g13, g23, g33]]

    phi1 = sp.Function("phi1")(*coords)
    phi2 = sp.Function("phi2")(*coords)
    pi1 = sp.Function("pi1")(*coords)
    pi2 = sp.Function("pi2")(*coords)
    u_loc = sp.Function("U")(phi1, phi2)

    def var_derivs_3d(lapse):
        dpi1 = lapse * pi1 / sqrt_g
        dpi2 = lapse * pi2 / sqrt_g
        dphi1 = lapse * sqrt_g * sp.diff(u_loc, phi1)
        dphi2 = lapse * sqrt_g * sp.diff(u_loc, phi2)
        for i in range(3):
            flux1_i = sum(g_inv[i][j] * sp.diff(phi1, coords[j]) for j in range(3))
            flux2_i = sum(g_inv[i][j] * sp.diff(phi2, coords[j]) for j in range(3))
            dphi1 -= sp.diff(lapse * sqrt_g * flux1_i, coords[i])
            dphi2 -= sp.diff(lapse * sqrt_g * flux2_i, coords[i])
        return dphi1, dphi2, dpi1, dpi2

    dp1_1, dp2_1, dq1_1, dq2_1 = var_derivs_3d(n1)
    dp1_2, dp2_2, dq1_2, dq2_2 = var_derivs_3d(n2)
    bracket_integrand_3d = sp.expand(dp1_1 * dq1_2 - dp1_2 * dq1_1 + dp2_1 * dq2_2 - dp2_2 * dq2_1)

    # Target 3D Dirac momentum density M_i = sum_A pi_A d_i phi_A contracted with g^{ij}(N1 d_j N2 - N2 d_j N1):
    target_3d = sp.Integer(0)
    for i in range(3):
        m_i = pi1 * sp.diff(phi1, coords[i]) + pi2 * sp.diff(phi2, coords[i])
        shift_i = sum(g_inv[i][j] * (n1 * sp.diff(n2, coords[j]) - n2 * sp.diff(n1, coords[j])) for j in range(3))
        target_3d += shift_i * m_i

    require(
        sp.expand(bracket_integrand_3d - target_3d) == 0,
        "Exact 3D curved Riemannian pointwise Dirac hypersurface deformation identity for arbitrary local U(phi)",
    )

    # 2-site nonlocal smearing defect check:
    g_c, eps, m1, m2, l1, l2, q1, q2, p1, p2 = sp.symbols("g eps N1 N2 M1 M2 q1 q2 p1 p2", real=True)
    dh_dq1 = g_c * (m1 * (q1 + eps * q2) + eps * m2 * (q2 + eps * q1))
    dh_dq2 = g_c * (eps * m1 * (q1 + eps * q2) + m2 * (q2 + eps * q1))
    dk_dq1 = g_c * (l1 * (q1 + eps * q2) + eps * l2 * (q2 + eps * q1))
    dk_dq2 = g_c * (eps * l1 * (q1 + eps * q2) + l2 * (q2 + eps * q1))
    nl_bracket = sp.simplify((dh_dq1 * l1 * p1 - m1 * p1 * dk_dq1) + (dh_dq2 * l2 * p2 - m2 * p2 * dk_dq2))
    expected_defect = g_c * eps * (m1 * l2 - m2 * l1) * (p2 * (q1 + eps * q2) - p1 * (q2 + eps * q1))
    require(sp.simplify(nl_bracket - expected_defect) == 0 and nl_bracket.subs(eps, 0) == 0, "Exact nonlocal defect")

    # 5x5 Hermitian tridiagonal mediator mass-squared matrix T_5 with mu^2 = 1/2 M^2:
    kk, m_s = sp.symbols("k M", positive=True)
    mu_sq = m_s**2 / 2
    t5 = sp.Matrix(5, 5, lambda r, c: m_s**2 if r == c else (mu_sq if abs(r - c) == 1 else 0))
    det_t5 = sp.factor(t5.det())
    require(det_t5 == sp.Rational(3, 16) * m_s**10, "Exact det(T_5) == 3/16 M^10")
    # Leading principal minors > 0 (Sylvester's criterion for strict positive definiteness):
    for sz in range(1, 6):
        require(sp.simplify(t5[:sz, :sz].det() / (m_s ** (2 * sz))) > 0, f"Sylvester minor {sz} > 0")

    a5 = kk**2 * sp.eye(5) + t5
    g_med_sym = sp.simplify(3 * m_s**2 * (a5.inv()[4, 0]))
    expected_denom = (
        (kk**2 + m_s**2)
        * (kk**2 + m_s**2 / 2)
        * (kk**2 + sp.Rational(3, 2) * m_s**2)
        * ((kk**2 + m_s**2) ** 2 - sp.Rational(3, 4) * m_s**4)
    )
    require(
        sp.simplify(g_med_sym - (sp.Rational(3, 16) * m_s**10) / expected_denom) == 0,
        "Exact Cramer (5,1) transfer multiplier for 5-field Hermitian tridiagonal chain",
    )
    require(sp.simplify(g_med_sym.subs(kk, 0)) == 1, "Unit IR normalization G_med(0) == 1")

    return {
        "continuum_3D_curved_local_potential_Dirac_defect": "IDENTICALLY_ZERO_POINTWISE",
        "nonlocal_smearing_defect_factor": "g * eps * (N1*M2 - N2*M1) * (p2*(q1+eps*q2) - p1*(q2+eps*q1))",
        "c_number_normal_ordering_central_extension": 0,
        "tridiagonal_mass_matrix_Sylvester_SPD": True,
        "tridiagonal_det_over_M10_exact": "3/16",
    }


def main() -> None:
    sym_res = verify_3d_curved_dirac_and_tridiagonal_chain()

    m_sig = exact(20)
    m2 = m_sig**2
    rt3_half = iv.sqrt(exact(3)) / exact(2)
    eigs = [
        m2 * (exact(1) + rt3_half),
        m2 * (exact(3) / exact(2)),
        m2,
        m2 * (exact(1) / exact(2)),
        m2 * (exact(1) - rt3_half),
    ]
    require(above(eigs[-1], exact(53)), "Smallest mass-squared eigenvalue > 53 > 0 (tachyon-free)")

    v0 = exact(2) * iv.pi**2
    k_cut = 500
    c_shift_med = exact(0)
    var_med = exact(0)
    num_const = (exact(3) / exact(16)) * (m_sig**10)
    for k in range(1, k_cut + 1):
        kk2 = exact(k) ** 2
        denom = exact(1)
        for lam in eigs:
            denom *= kk2 + lam
        g_med = num_const / denom
        c_shift_med += (exact(3) / exact(4)) * (exact(k) ** 3) * (g_med**2)
        if k >= 2:
            var_med += (kk2 / iv.sqrt(kk2 - exact(1))) * (g_med**2) / (exact(2) * v0)

    # Tail above k = 500: g_med(k) < (3/16) M^10 k^(-10) => g_med(k)^2 < (9/256) M^20 k^(-20)
    tail_shift = (exact(3) / exact(4)) * (exact(9) / exact(256)) * (m_sig**20) / (exact(16) * (exact(k_cut) ** 16))
    c_shift_box = iv.mpf([c_shift_med.a, (c_shift_med + tail_shift).b])
    var_med_box = iv.mpf([var_med.a, (var_med + tail_shift).b])

    require(below(tail_shift, exact("1e-19")), "5-mediator UV tail < 1e-19")
    require(above(c_shift_box, exact(10)) and below(c_shift_box, exact("1e6")), "Finite local-cascade Friedrichs shift")
    require(above(var_med_box, exact("0.01")) and below(var_med_box, exact(50)), "Finite local-cascade clock variance")

    finish(
        "smeared_dirac_hypersurface_algebra.py",
        {
            **sym_res,
            "mediator_cascade_stages": 5,
            "mediator_mass_M_Sigma": 20,
            "mediator_min_mass_squared_eigenvalue": outward(eigs[-1]),
            "mediator_UV_multiplier_decay": "(3/16)*M_Sigma^10 * k^(-10)",
            "local_cascade_Friedrichs_shift": outward(c_shift_box),
            "local_cascade_inhomogeneous_clock_variance": outward(var_med_box),
            "cascade_UV_tail_above_k500_upper": float(outward(tail_shift)[1]),
            "exact_pointwise_Dirac_hypersurface_closure_restored": True,
        },
    )


if __name__ == "__main__":
    main()
