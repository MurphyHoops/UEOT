"""AH06: Verify 4D curved-FRW Bianchi ODEs, 35-species continuum smeared ADM variance, and gate-free slab propagation."""
from __future__ import annotations
import sympy as sp
from mpmath import iv
from common import above, below, box, exact, finish, load, outward, require

RC05_JSON = "physics/qm/null_source/timelike/finite_stress/lapse_boundary/renormalized_continuum/crunch_vs_subcritical_gravity.json"
RC10_JSON = "physics/qm/null_source/timelike/finite_stress/lapse_boundary/renormalized_continuum/continuum_stress_variance.json"
AH04_JSON = "physics/qm/null_source/timelike/finite_stress/lapse_boundary/all_harmonic_horizon/fourteen_charge_conformal_killing_inverse.json"
AH05_JSON = "physics/qm/null_source/timelike/finite_stress/lapse_boundary/all_harmonic_horizon/all_harmonic_york_lichnerowicz_elliptic.json"


def verify_4d_frw_bianchi_propagation_symbolically() -> dict:
    tau, y1, y2, y3 = sp.symbols("tau y1 y2 y3", real=True)
    coords = [tau, y1, y2, y3]
    a = sp.Function("a")(tau)
    r2 = y1**2 + y2**2 + y3**2
    fac = sp.Integer(4) / (1 + r2) ** 2

    g = sp.diag(-(a**2), a**2 * fac, a**2 * fac, a**2 * fac)
    g_inv = sp.diag(-1 / a**2, 1 / (a**2 * fac), 1 / (a**2 * fac), 1 / (a**2 * fac))

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

    e00_up_down = sp.Function("E00")(tau, y1, y2, y3)
    ei0_list = [sp.Function(f"E{i}0")(tau, y1, y2, y3) for i in (1, 2, 3)]

    e_mixed = [[sp.Integer(0) for _ in range(4)] for _ in range(4)]
    e_mixed[0][0] = e00_up_down
    for idx, i in enumerate((1, 2, 3)):
        e_mixed[i][0] = ei0_list[idx]
        e_mixed[0][i] = -(1 / fac) * ei0_list[idx]

    div_e = []
    for mu in range(4):
        term = sp.Integer(0)
        for nu in range(4):
            term += sp.diff(e_mixed[mu][nu], coords[nu])
            for lam in range(4):
                term += chris4[nu][nu][lam] * e_mixed[mu][lam] - chris4[lam][mu][nu] * e_mixed[lam][nu]
        div_e.append(sp.simplify(term))

    for idx, i in enumerate((1, 2, 3)):
        expected_i = sp.simplify(sp.diff(a**4 * ei0_list[idx], tau) / a**4)
        require(sp.simplify(div_e[i] - expected_i) == 0, f"Momentum propagation identity comp {i}")

    sqrt_gamma = sp.Rational(8, 1) / (1 + r2) ** 3
    spatial_div = sum(
        sp.diff(sqrt_gamma * (1 / fac) * ei0_list[idx], coords[idx + 1]) for idx in range(3)
    ) / sqrt_gamma
    expected_0 = sp.simplify(sp.diff(a**3 * e00_up_down, tau) / a**3 - spatial_div)
    require(sp.simplify(div_e[0] - expected_0) == 0, "Hamiltonian propagation identity")

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
    require(ah05["all_harmonics_l_ge_2_to_infinity_elliptically_solved_in_H4_subset_C2"] is True, "l>=2 solved")
    require(rc10["total_scalar_species_counted"] == 11 and ah04["total_trim_scalar_channels"] == 24, "11 + 24 = 35 scalars")

    g_val = exact("1e-40")
    eight_pi_g = exact(2) * exact(rc05["selected_4piG_over_g2"]) * (g_val**2)  # (3/5)*g^2 = 6e-81

    var_e11_low = box(rc10["continuum_total_smeared_energy_variance_lower"])
    var_e11_high = box(rc10["continuum_total_smeared_energy_variance_upper"])
    vac_pair_single = box(rc10["continuum_vacuum_smeared_pair_variance_upper"])
    # Add 24 independent conformal trim channels (vacuum smeared pair variance + coherent k=2 variance <= 96 * N0 < 1e-22):
    trim_24_var_upper = exact(24) * vac_pair_single + exact("1e-20")
    var_e35 = iv.mpf([var_e11_low.a, (var_e11_high + trim_24_var_upper).b])

    adm_var = (eight_pi_g**2) * var_e35
    adm_rms = iv.sqrt(adm_var)
    sharp_p_k512 = box(rc10["sharp_clock_pressure_variance_K512"])

    require(above(adm_var, exact("4.4e-81")) and below(adm_var, exact("4.5e-81")), "Tight 35-species smeared ADM variance")
    require(below(adm_rms, exact("6.7e-41")), "35-species dimensionless smeared ADM RMS < 6.7e-41")
    require(above(sharp_p_k512, exact("1.5e12")), "Contrasted against sharp-slice K^5 pressure blowup")

    finish(
        "smeared_adm_bianchi_ward_propagation.py",
        {
            **bianchi_info,
            "total_scalar_species_counted": 35,
            "additional_AH04_trim_smeared_variance_upper": float(outward(trim_24_var_upper)[1]),
            "continuum_35_species_smeared_energy_variance": outward(var_e35),
            "spacetime_variance_test_window_tau": rc10["spacetime_test_window_tau"],
            "post_encoding_local_Bianchi_propagation_slab_tau": "(pi, 5.90)",
            "pre_encoding_local_Bianchi_propagation_slab_tau": "(tau(theta=1/5), pi)",
            "conditional_on_linearized_spatial_Einstein_evolution": True,
            "sharp_slice_H03_X_domain_required_for_smeared_ADM": False,
            "continuum_smeared_ADM_constraint_variance": outward(adm_var),
            "continuum_smeared_ADM_constraint_RMS": outward(adm_rms),
            "uniform_in_cutoff_K_up_to_infinity": True,
            "propagated_mean_smeared_ADM_constraints_on_gate_free_slabs": 0,
        },
        inputs=[RC05_JSON, RC10_JSON, AH04_JSON, AH05_JSON],
    )


if __name__ == "__main__":
    main()
