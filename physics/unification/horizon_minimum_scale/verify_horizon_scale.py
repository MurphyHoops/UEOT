"""P-HORIZON-CLOCK-01 Certificate: Operational Planck Sensor Floor & Sensor-Shrink RG Trichotomy."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
import sympy as sp
from mpmath import iv

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from common import outward_str, require, sha256_file, strictly_above, strictly_below, write_json


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--output", type=Path, default=HERE / "result.json")
    args = ap.parse_args()

    s = sp.Symbol("s", real=True)
    j0 = sp.integrate((1 - s**2) ** 8 * s**2, (s, 0, 1))
    j1 = sp.integrate((1 - s**2) ** 16 * s**2, (s, 0, 1))
    j2 = sp.integrate(256 * s**2 * (1 - s**2) ** 14 * s**2, (s, 0, 1))
    require(j0 == sp.Rational(32768, 2078505) and j2 / j1 == 28, "Exact C^7 radial Beta ratio J2/J1 = 28")

    j0_iv = iv.mpf(int(sp.numer(j0))) / iv.mpf(int(sp.denom(j0)))
    j1_iv = iv.mpf(int(sp.numer(j1))) / iv.mpf(int(sp.denom(j1)))
    j2_iv = iv.mpf(int(sp.numer(j2))) / iv.mpf(int(sp.denom(j2)))
    cw2 = j1_iv / (4 * iv.pi * (j0_iv**2))
    cw_grad = j2_iv / (4 * iv.pi * (j0_iv**2))
    a_bar = iv.mpf("0.5") * iv.sqrt(cw2 * cw_grad) / cw2  # exact sqrt(7)

    # Dimensionless energy E_min and Planck floor ratio L_min / l_P for (N_gate=1, eta_t=1, lam_sys=2)
    e_min_1 = iv.mpf("1") / (8 * (a_bar + iv.sqrt(a_bar**2 + iv.mpf("0.25"))))
    l_ratio_1 = iv.sqrt(e_min_1)
    # High-precision clock gate (N_gate=10, eta_t=0.5, lam_sys=2): N_gate^2 / (4*eta_t^2) = 100 / 1 = 100
    b_10 = iv.mpf("100")
    e_min_10 = iv.mpf("100") / (2 * (a_bar + iv.sqrt(a_bar**2 + b_10)))
    l_ratio_10 = iv.sqrt(e_min_10)

    require(strictly_above(l_ratio_1, "0.153") and strictly_above(l_ratio_10, "1.96"), "Planck sensor floor check")

    # Universal S^3 variance coefficient 25 / (576 pi^2) and fixed-G marginal RG crunch radius sqrt(30)/200
    c_s3_lb = iv.mpf("25") / (576 * (iv.pi**2))
    rho_crunch_nu1 = iv.sqrt(iv.mpf("30")) / 200
    require(strictly_below(rho_crunch_nu1, "0.0274") and strictly_above(rho_crunch_nu1, "0.02738"), "Crunch radius")

    payload = {
        "result_ids": ["P-HORIZON-CLOCK-01"],
        "lean_module": "formalization/ueot-physics-unification/UEOTPhysicsUnification/OperationalHorizonMinimumScale.lean",
        "ball_C7_exact_Beta_integrals": {"J0": str(j0), "J1": str(j1), "J2": str(j2), "J2_over_J1": "28"},
        "Plancherel_cw2": outward_str(cw2),
        "kinetic_to_L2_ratio_sqrt7": outward_str(a_bar),
        "L_min_over_Planck_SNR1_etat1_lam2": outward_str(l_ratio_1),
        "L_min_over_Planck_SNR10_etat0p5_lam2": outward_str(l_ratio_10),
        "S3_universal_variance_coeff_25_over_576pi2": outward_str(c_s3_lb),
        "marginal_nu1_fixed_G_crunch_radius_rad": outward_str(rho_crunch_nu1),
        "physical_unification": "OPEN",
        "status": "PASS",
        "source_sha256": sha256_file(Path(__file__).resolve()),
    }
    if args.check and args.output.is_file():
        require(json.loads(args.output.read_text()) == payload, "horizon_minimum_scale certificate drift")
    else:
        write_json(args.output, payload)
    print("PASS: horizon_minimum_scale P-HORIZON-CLOCK-01")


if __name__ == "__main__":
    main()
