#!/usr/bin/env python3
"""Independent closed-form check of the saved UEOT two-census newborn laws.

Uses only Fraction and the recorded parameter point. It does not import or run
boundary_math_check.py, its transaction code, or its recursive birth-law solver.
This checks a finite numerical witness, not the all-horizon written proof.
"""

from fractions import Fraction as F
from pathlib import Path
import argparse
import json


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("json_file", nargs="?", type=Path,
                        default=Path(__file__).with_name("boundary_math_check.json"))
    args = parser.parse_args()
    saved = json.loads(args.json_file.read_text())
    s, delta, b, gamma, q = map(F, saved["parameter_point"])
    assert 0 < delta < s < 1 and 0 < b and b + gamma < 1
    assert delta < gamma and 0 < q < 1 and s + b > 1

    names = ("theta0H", "theta0D", "theta1H", "theta1D")
    assert set(saved["two_tick_joint_laws"]) == set(names)
    direct_laws, direct_means, first_birth, repair = {}, {}, {}, {}
    for name in names:
        theta1 = name.startswith("theta1")
        bloom = name == "theta1H"
        # First census: retention and strict birth are independent Bernoulli.
        survival = s - delta if bloom else s
        birth = b + gamma if bloom else b
        # Each first-census output has a fresh independent damage mark.
        beta = b + (1 - q) * gamma if theta1 else b
        direct = {
            "(0, 0)": (1 - birth) * (1 - survival * beta),
            "(0, 1)": (1 - birth) * survival * beta,
            "(1, 0)": birth * ((1 - survival) * (1 - beta)
                               + survival * (1 - beta) ** 2),
            "(1, 1)": birth * ((1 - survival) * beta
                               + 2 * survival * beta * (1 - beta)),
            "(1, 2)": birth * survival * beta ** 2,
        }
        assert sum(direct.values()) == 1
        assert direct == {k: F(v) for k, v in saved["two_tick_joint_laws"][name].items()}
        means = (birth, (survival + birth) * beta)
        assert means == tuple(map(F, saved["newborn_means_B1_B2"][name]))
        direct_laws[name], direct_means[name] = direct, means
        first_birth[name] = birth
        repair[name] = 3 if name.endswith("D") else 0

    def class_count(values):
        representatives = []
        for value in values:
            if value not in representatives:
                representatives.append(value)
        return len(representatives)

    gap = direct_means["theta1D"][1] - direct_means["theta0D"][1]
    assert gap == (s + b) * (1 - q) * gamma > 0
    assert direct_laws["theta0H"] == direct_laws["theta0D"]
    counts = {
        "B1": class_count(first_birth.values()),
        "B1_B2": class_count(direct_laws.values()),
        "B1_R1": class_count((first_birth[n], repair[n]) for n in names),
        "B1_B2_R1": class_count((direct_laws[n], repair[n]) for n in names),
    }
    assert counts == {"B1": 2, "B1_B2": 3, "B1_R1": 3, "B1_B2_R1": 4}
    print(json.dumps({"status": "passed", "joint_laws_checked": len(names),
                      "exact_second_tick_gap": str(gap), "finite_task_class_counts": counts,
                      "scope": "Independent exact two-census witness; no Lean compilation or all-horizon enumeration."},
                     indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
