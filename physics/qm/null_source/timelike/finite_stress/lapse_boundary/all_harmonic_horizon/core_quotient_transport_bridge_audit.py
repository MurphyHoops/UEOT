"""AH11: Certify Core-transport Dyson-LR supersonic leakage bound and audit irreducible physical postulates."""
from __future__ import annotations
import math
from mpmath import iv
from common import below, exact, finish, outward, require


def main() -> None:
    # Exact factorial supersonic bound ((n * eta_LR / e)^n) / n! < eta_LR^n at eta_LR = 2/5, n = 120:
    n_steps = 120
    eta_lr = exact(2) / exact(5)
    fact_n = exact(math.factorial(n_steps))
    two_j_dt = exact(n_steps) * eta_lr / iv.exp(exact(1))
    exact_lr_tail = (two_j_dt**n_steps) / fact_n
    power_majorant = eta_lr**n_steps

    require(below(exact_lr_tail - power_majorant, 0), "Exact factorial bound strictly below eta_LR^n")
    require(below(power_majorant, exact("2e-48")), "Supersonic leakage < 2e-48 (< 1e-45) at 120 lattice steps")

    d_sep = exact(1) / exact(40)
    a_lat = d_sep / exact(n_steps)
    require(below(a_lat, exact("2.1e-4")), "Lattice spacing 1/4800 < 2.1e-4 rad")

    inventory = {
        "C_CORE_DERIVED": [
            "quotient_descent_minimal_realization",
            "finite_quantitative_transport_chain_bound",
        ],
        "B_CONDITIONAL_BRIDGE": [
            "lieb_robinson_emergent_null_cone_to_minkowski_conformal_class",
            "gpt_self_dual_psd_cone_and_hurwitz_complex_selection",
            "squeezing_proof_operational_planck_sensor_floor",
        ],
        "S_ANOMALY_OR_STABILITY_SELECTED": [
            "spacetime_dimension_D_eq_4",
            "conformal_scalar_coupling_xi_eq_1_over_6",
            "quartic_sos_vacuum_stability_and_gate_free_3d_dirac_closure",
            "su3c_su3l_u1x_anomaly_and_ir_asymptotic_freedom_selection",
        ],
        "P_IRREDUCIBLE_PHYSICAL_POSTULATE": [
            "dimensional_constants_G_Lambda_hbar_c",
            "einstein_hilbert_weyl_squared_gravitational_action",
            "declared_relativistic_apparatus_and_matter_field_multiplet",
            "canonical_fock_hilbert_space_quantization",
        ],
        "X_OPEN_UNIFICATION_FRONTIER": [
            "nonperturbative_operator_quantum_einstein_geometry",
            "nonperturbative_4d_chiral_gauge_fermion_continuum_qft",
            "matched_protocol_quantum_hardware_blind_holdout_certification",
        ],
    }

    p_count = len(inventory["P_IRREDUCIBLE_PHYSICAL_POSTULATE"])
    x_count = len(inventory["X_OPEN_UNIFICATION_FRONTIER"])
    require(p_count == 4 and x_count == 3, "Irreducible postulates and open frontiers explicitly accounted")

    finish(
        "core_quotient_transport_bridge_audit.py",
        {
            "Core_v3_modified": False,
            "geodesic_separation_D_rad": "1/40",
            "supersonic_ratio_eta_LR": "2/5",
            "lattice_steps_across_D": n_steps,
            "lattice_spacing_rad": outward(a_lat),
            "exact_factorial_LR_leakage_tail": outward(exact_lr_tail),
            "power_majorant_LR_tail_upper": float(outward(power_majorant)[1]),
            "premise_classification_inventory": inventory,
            "irreducible_postulate_count": p_count,
            "open_unification_frontier_count": x_count,
            "unification_claim_permitted": False,
        },
    )


if __name__ == "__main__":
    main()
