#!/usr/bin/env python3
"""Scoped arithmetic check for UEOT Physics publication evidence.

This script uses only Python's standard library and no network or experimental
data. It verifies the two displayed sample counts and their probability/error
constants; it does not execute or replace the historical benchmark or Lean gates.

Usage:
  python empirical_number_check.py --output EMPIRICAL_NUMBER_CHECK.json
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
from decimal import Decimal, ROUND_CEILING, localcontext
import hashlib
import json
from pathlib import Path
import platform
import sys


def calculate() -> dict:
    with localcontext() as ctx:
        ctx.prec = 80
        one = Decimal(1)
        two = Decimal(2)
        sqrt_two = two.sqrt()
        alpha = one / Decimal(20)
        epsilon = Decimal(3) / Decimal(25)
        branches = 3
        settings = branches * (branches - 1)

        # Each observation lies in [-1, 1]. Hoeffding's two-sided tail is
        # 2 exp(-n epsilon^2 / 2), followed by a union bound over settings.
        required_n = two * (two * settings / alpha).ln() / epsilon**2
        n_hoeffding = int(required_n.to_integral_value(rounding=ROUND_CEILING))
        tail_761 = two * settings * (-(n_hoeffding - 1) * epsilon**2 / two).exp()
        tail_762 = two * settings * (-n_hoeffding * epsilon**2 / two).exp()

        kappa = Decimal(3) - two * sqrt_two
        witness_norm = two + one / sqrt_two
        p_star = kappa / (Decimal(4) * witness_norm)
        required_zero_n = alpha.ln() / (one - p_star).ln()
        n_zero = int(required_zero_n.to_integral_value(rounding=ROUND_CEILING))
        zero_tail_previous = (one - p_star) ** (n_zero - 1)
        zero_tail = (one - p_star) ** n_zero
        # From p_0 >= p_star - sqrt(8 ell), with zero SPAM allowance.
        pointer_threshold = p_star**2 / Decimal(8)

        checks = {
            "hoeffding_sample_count_is_762_per_setting": n_hoeffding == 762,
            "hoeffding_761_union_bound_exceeds_0_05": tail_761 > alpha,
            "hoeffding_762_union_bound_at_most_0_05": tail_762 <= alpha,
            "ideal_event_lower_bound_positive": p_star > 0,
            "zero_event_sample_count_is_188": n_zero == 188,
            "187_zero_event_probability_exceeds_0_05": zero_tail_previous > alpha,
            "188_zero_event_probability_at_most_0_05": zero_tail <= alpha,
            "pointer_threshold_cancels_conservative_bound": (
                abs((Decimal(8) * pointer_threshold).sqrt() - p_star)
                < Decimal("1e-75")
            ),
        }
        return {
            "arithmetic": "decimal transcendental arithmetic, 80 decimal digits",
            "inputs": {
                "branches_m": branches,
                "real_settings_L": settings,
                "alpha": str(alpha),
                "epsilon": str(epsilon),
                "measurement_outcome_interval": [-1, 1],
                "SPAM_allowance_for_pointer_threshold": "0",
            },
            "formulas": {
                "hoeffding_n": "ceil(2 ln(2 L / alpha) / epsilon^2)",
                "hoeffding_union_bound": "2 L exp(-n epsilon^2 / 2)",
                "kappa": "3 - 2 sqrt(2)",
                "witness_operator_norm": "2 + 1 / sqrt(2)",
                "p_star": "(3 - 2 sqrt(2)) / (4 (2 + 1 / sqrt(2)))",
                "zero_event_n": "ceil(ln(alpha) / ln(1 - p_star))",
                "zero_event_tail": "(1 - p_star)^n",
                "positive_conservative_pointer_bound": "ell < p_star^2 / 8, when delta_SPAM = 0",
            },
            "results": {
                "hoeffding_n_before_ceiling": str(required_n),
                "hoeffding_n_per_setting": n_hoeffding,
                "hoeffding_union_bound_at_761": str(tail_761),
                "hoeffding_union_bound_at_762": str(tail_762),
                "kappa": str(kappa),
                "witness_operator_norm": str(witness_norm),
                "p_star": str(p_star),
                "zero_event_n_before_ceiling": str(required_zero_n),
                "ideal_zero_event_n": n_zero,
                "zero_event_probability_at_187": str(zero_tail_previous),
                "zero_event_probability_at_188": str(zero_tail),
                "pointer_error_strict_threshold_with_zero_SPAM": str(pointer_threshold),
            },
            "checks": checks,
            "status": "PASS" if all(checks.values()) else "FAIL",
            "interpretive_limits": [
                "762 is per setting, not a total shot count.",
                "Hoeffding assumes independent fixed-expectation trials within each setting.",
                "The union bound does not require independence between settings.",
                "188 uses ideal calibration and a fixed-sample null; Chapter 46 states the conditional-null extension.",
                "188 excludes calibration, model validation, drift control, and reproducibility trials.",
                "The pointer threshold is sufficient for positivity of this conservative bound; it is not a universal hardware impossibility threshold.",
                "No actualization mechanism or experimental claim is established by this arithmetic.",
            ],
        }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = calculate()
    script = Path(__file__).resolve()
    result.update({
        "schema": "ueot.physics.publication.empirical_arithmetic.v1",
        "executed_at_utc": datetime.now(timezone.utc).isoformat(),
        "script": script.name,
        "script_sha256": hashlib.sha256(script.read_bytes()).hexdigest(),
        "python": sys.version,
        "platform": platform.platform(),
        "invocation": ["python", script.name, "--output", args.output.name],
        "bound_source": {
            "commit": "3d443ec29eb17af1fc00699a74e2d42d73516d81",
            "path": "physics/qm/book/UEOT_PHYSICS.md",
            "sha256": "b726e3b9033d79ef949b8e83469901fe728aa28ab204b2e4d55bf36a18b412f0",
            "sections": ["8.3", "39.3", "39.5", "39.6", "46.1"],
        },
        "new_hardware_data": False,
        "heavy_validation_rerun": False,
    })
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({
        "status": result["status"],
        "checks_passed": sum(result["checks"].values()),
        "checks_total": len(result["checks"]),
        "output": str(args.output),
        "output_sha256": hashlib.sha256(args.output.read_bytes()).hexdigest(),
    }, ensure_ascii=False))
    return 0 if result["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
