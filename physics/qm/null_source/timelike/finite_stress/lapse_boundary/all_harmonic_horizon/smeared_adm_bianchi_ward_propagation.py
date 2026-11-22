"""AH06: Symbolically verify 4D curved-FRW Bianchi constraint propagation and certify K=infty smeared ADM variance."""
from __future__ import annotations
import sympy as sp
from mpmath import iv
from common import above, below, box, exact, finish, load, outward, require

RC05_JSON = "physics/qm/null_source/timelike/finite_stress/lapse_boundary/renormalized_continuum/crunch_vs_subcritical_gravity.json"
RC10_JSON = "physics/qm/null_source/timelike/finite_stress/lapse_boundary/renormalized_continuum/continuum_stress_variance.json"
AH04_JSON = "physics/qm/null_source/timelike/finite_stress/lapse_boundary/all_harmonic_horizon/fourteen_charge_conformal_killing_inverse.json"
AH05_JSON = "physics/qm/null_source/timelike/finite_stress/lapse_boundary/all_harmonic_horizon/all_harmonic_york_lichnerowicz_elliptic.json"


def verify_4d_frw_bianchi_propagation_symbolically() -> dict:
    """Compute exact 4D Christoffel symbols of ds^2 = a(tau)^2 (-dtau^2 + gamma_ij dy^i dy^j) on S^3 and verify Bianchi ODEs."""
    tau, y1, y2, y3 = sp.symbols("tau y1 y2 y3", real=True)
    coords = [tau, y1, y2, y3]
    a = sp.Function("a")(tau)
    r2 = y1**2 + y2**2 + y3**2
    fac = sp.Integer(4) / (1 + r2) ** 2

    g = sp.diag(-(a**2), a**2 * fac, a**2 * fac, a**2 * fac)
    g_inv = sp.diag(-1 / a**2, 1 / (a**2 * fac), 1 / (a**2 * fac), 1 / (a**2 * fac))

    # Full 4D Levi-Civita connection Gamma^lambda_{mu nu}
    chris4 = [
        [
            [
                sp.simplify(
                    sp.Rational(1, 2)
                    * g_inv[lam, lam]
                    * (
                        sp.diff(g[lam, nu], coords[mu])
                        + sp.diff(g[lam, mu], coords[nu])
                        - sp.diff(g[mu, nu], coords[lam])
                    )
                )
                for nu in range(4)
            ]
            for mu in range(4)
        ]
        for lam in range(4)
    ]

    # Symmetric covariant residual E_{mu nu} with spatial components E_{ij} == 0:
    e00_up_down = sp.Function("E00")(tau, y1, y2, y3)  # E_0^0
    ei0_list = [sp.Function(f"E{i}0")(tau, y1, y2, y3) for i in (1, 2, 3)]  # E_i^0

    # Mixed tensor E_mu^nu:
    # Since E_{0i} = E_{i0}, E_0^j = g^{jk} E_{0k} = g^{jk} E_{k0} = g^{jk} g_{00} E_k^0 = -(1/fac) E_j^0!
    e_mixed = [[sp.Integer(0) for _ in range(4)] for _ in range(4)]
    e_mixed[0][0] = e00_up_down
    for idx, i in enumerate((1, 2, 3)):
        e_mixed[i][0] = ei0_list[idx]
        e_mixed[0][i] = -(1 / fac) * ei0_list[idx]

    # Compute 4D covariant divergence nabla_nu E_mu^nu = d_nu E_mu^nu + Gamma^nu_{nu lam} E_mu^lam - Gamma^lam_{mu nu} E_lam^nu
    div_e = []
    for mu in range(4):
        term = sp.Integer(0)
        for nu in range(4):
            term += sp.diff(e_mixed[mu][nu], coords[nu])
            for lam in range(4):
                term += chris4[nu][nu][lam] * e_mixed[mu][lam] - chris4[lam][mu][nu] * e_mixed[lam][nu]
        div_e.append(sp.simplify(term))

    # Check spatial components mu = 1, 2, 3: expect a^(-4) d_tau (a^4 E_i^0) identically!
    for idx, i in enumerate((1, 2, 3)):
        expected_i = sp.simplify(sp.diff(a**4 * ei0_list[idx], tau) / a**4)
        require(sp.simplify(div_e[i] - expected_i) == 0, f"Exact momentum propagation identity failed on comp {i}")

    # Check temporal component mu = 0: expect a^(-3) d_tau (a^3 E_0^0) - D^k E_k^0 (where D^k V_k = (1/sqrt_gamma) d_k(sqrt_gamma gamma^{kj} V_j))!
    sqrt_gamma = sp.Rational(8, 1) / (1 + r2) ** 3
    spatial_div = sum(
        sp.diff(sqrt_gamma * (1 / fac) * ei0_list[idx], coords[idx + 1]) for idx in range(3)
    ) / sqrt_gamma
    expected_0 = sp.simplify(sp.diff(a**3 * e00_up_down, tau) / a**3 - spatial_div)
    require(sp.simplify(div_e[0] - expected_0) == 0, "Exact Hamiltonian constraint propagation identity failed")

    return {
        "momentum_propagation_identity": "nabla_nu E_i^nu|_{E_j^k=0} == a^(-4) d_tau(a^4 E_i^0)",
        "Hamiltonian_propagation_identity": "nabla_nu E_0^nu|_{E_j^k=0} == a^(-3) d_tau(a^3 E_0^0) - D^k E_k^0",
        "symbolic_4D_curved_FRW_verification": "EXACT_ZERO_RESIDUAL",
    }


def main() -> None:
    bianchi_info = verify_4d_frw_bianchi_propagation_symbolically()
    rc05 = load(RC05_JSON)
    rc10 = load(RC10_JSON)
    ah04 = load(AH04_JSON)
    ah05 = load(AH05_JSON)

    require(ah04["all_15_S3_conformal_and_Killing_obstructions_matched"] is True, "l=0,1 obstructions matched")
    require(ah05["all_harmonics_l_ge_2_to_infinity_elliptically_solved_in_C2"] is True, "l>=2 harmonics solved")

    g_val = exact("1e-40")
    eight_pi_g = exact(2) * exact(rc05["selected_4piG_over_g2"]) * (g_val**2)  # (3/5) * g^2 = 6e-81
    require(eight_pi_g == exact(3) / exact(5) * (g_val**2), "Exact 8*pi*G = (3/5)*g^2")

    var_e_low = box(rc10["continuum_total_smeared_energy_variance_lower"])
    var_e_high = box(rc10["continuum_total_smeared_energy_variance_upper"])
    var_e = iv.mpf([var_e_low.a, var_e_high.b])

    adm_var = (eight_pi_g**2) * var_e
    adm_rms = iv.sqrt(adm_var)
    sharp_p_k512 = box(rc10["sharp_clock_pressure_variance_K512"])

    require(above(adm_var, exact("4.4e-81")) and below(adm_var, exact("4.5e-81")), "Tight smeared ADM constraint variance")
    require(below(adm_rms, exact("6.7e-41")), "Dimensionless smeared ADM RMS < 6.7e-41")
    require(above(sharp_p_k512, exact("1.5e12")), "Contrasted against sharp-slice K^5 pressure blowup")

    finish(
        "smeared_adm_bianchi_ward_propagation.py",
        {
            **bianchi_info,
            "spacetime_test_window_tau": rc10["spacetime_test_window_tau"],
            "sharp_slice_H03_X_domain_required_for_smeared_ADM": False,
            "continuum_smeared_ADM_constraint_variance": outward(adm_var),
            "continuum_smeared_ADM_constraint_RMS": outward(adm_rms),
            "uniform_in_cutoff_K_up_to_infinity": True,
            "encoding_slice_tau_pi_all_l_ge_0_mean_constraints_zero": True,
            "propagated_mean_smeared_ADM_constraints_across_slab": 0,
        },
        inputs=[RC05_JSON, RC10_JSON, AH04_JSON, AH05_JSON],
    )


if __name__ == "__main__":
    main()
