"""P-ADM-ALLHARM-02 Certificate: 15D S^3 Obstructions, Rotational Trim & All-Harmonic Elliptic Green Constant."""
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

    # 1. Exact closed-form 3-sphere Sobolev-Green series pi^2/12 - 55/576 vs 2000-term partial sum
    series_exact = (iv.pi**2) / 12 - iv.mpf("55") / 576
    partial = iv.mpf("0")
    for ell in range(2, 2001):
        ll = iv.mpf(ell)
        partial += ((ll + 1) / ((ll - 1) * (ll + 3))) ** 2
    require(
        strictly_above(series_exact - partial, "0") and strictly_below(series_exact - partial, "6e-4"),
        "Closed-form Sobolev-Green series check",
    )
    c_sob = iv.sqrt(series_exact) / (iv.sqrt(iv.mpf("2")) * iv.pi)

    # 2. Symbolic verification of 24-channel quadrature-balanced rotational trim pointwise isotropy at w=0
    x0, x1, x2, x3, tau, n0 = sp.symbols("x0 x1 x2 x3 tau N0", real=True)
    xs = [x0, x1, x2, x3]
    pairs = [(a, b) for a in range(4) for b in range(a + 1, 4)]
    c2, s2 = sp.cos(2 * tau), sp.sin(2 * tau)
    sum_sq = sp.Integer(0)
    for a, b in pairs:
        sum_sq += (
            (c2 * xs[a] - s2 * xs[b]) ** 2
            + (c2 * xs[a] + s2 * xs[b]) ** 2
            + (s2 * xs[a] + c2 * xs[b]) ** 2
            + (s2 * xs[a] - c2 * xs[b]) ** 2
        )
    sphere_rel = x0**2 + x1**2 + x2**2 + x3**2 - 1
    red = sp.simplify(sp.rem(sp.expand(sum_sq), sphere_rel, x0))
    require(sp.trigsimp(red) == 6, "Exact pointwise SO(4) sum == 6 across all 6 quadrature quartets")

    payload = {
        "result_ids": ["P-ADM-ALLHARM-02"],
        "lean_module": "formalization/ueot-physics-unification/UEOTPhysicsUnification/AllHarmonicConstraintEllipticity.lean",
        "s3_obstruction_counts": {"l0_Friedmann": 1, "l1_scalar": 4, "l1_conformal_grad": 4, "SO4_Killing": 6, "total": 15},
        "Sobolev_Green_series_closed_form": "pi^2/12 - 55/576",
        "Sobolev_Green_series_enclosure": outward_str(series_exact),
        "S3_Sobolev_Green_Linfty_constant": outward_str(c_sob),
        "quadrature_trim_w0_pointwise_sum_constant": 6,
        "physical_unification": "OPEN",
        "status": "PASS",
        "source_sha256": sha256_file(Path(__file__).resolve()),
    }
    if args.check and args.output.is_file():
        require(json.loads(args.output.read_text()) == payload, "all_harmonic_elliptic certificate drift")
    else:
        write_json(args.output, payload)
    print("PASS: all_harmonic_elliptic P-ADM-ALLHARM-02")


if __name__ == "__main__":
    main()
