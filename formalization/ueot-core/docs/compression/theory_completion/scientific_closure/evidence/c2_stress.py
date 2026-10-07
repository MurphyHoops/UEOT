#!/usr/bin/env python3
import json
from dataclasses import dataclass, asdict
from pathlib import Path

@dataclass
class Case:
    name: str
    estimate: float
    stat_radius: float
    drift_radius: float
    threshold: float
    coverage: bool = True
    split_disjoint: bool = True

    def verdict(self):
        if not self.split_disjoint:
            return "INVALID_DATA_REUSE"
        if not self.coverage:
            return "UNCERTIFIED_LOW_COVERAGE"
        lo = self.estimate - self.stat_radius - self.drift_radius
        hi = self.estimate + self.stat_radius + self.drift_radius
        if hi <= self.threshold:
            return "CERTIFIED"
        if self.threshold < lo:
            return "REJECTED"
        return "AMBIGUOUS"


def blocking_budget(blocks, independent_failure, beta_gap):
    return independent_failure + max(blocks - 1, 0) * beta_gap

cases = [
    Case("clear_carrier", 0.015, 0.01, 0.005, 0.05),
    Case("clear_rejection", 0.10, 0.01, 0.005, 0.05),
    Case("small_gap", 0.050, 0.012, 0.003, 0.05),
    Case("large_drift", 0.025, 0.01, 0.03, 0.05),
    Case("low_coverage", 0.01, 0.005, 0.0, 0.05, coverage=False),
    Case("discovery_certification_reuse", 0.01, 0.005, 0.0, 0.05, split_disjoint=False),
]

mixing = {
    "raw_timepoints": 1000,
    "effective_blocks": 20,
    "fast_mixing_failure_upper": blocking_budget(20, 0.01, 0.0005),
    "slow_mixing_failure_upper": blocking_budget(20, 0.01, 0.01),
    "iid_misuse_failure_upper": 0.01,
}

result = {
    "kind": "METHOD_STRESS_TEST_NOT_REAL_WORLD_VALIDATION",
    "cases": [{**asdict(c), "verdict": c.verdict()} for c in cases],
    "mixing": mixing,
    "assertions": {
        "small_gap_abstains": cases[2].verdict() == "AMBIGUOUS",
        "large_drift_abstains": cases[3].verdict() == "AMBIGUOUS",
        "low_coverage_refuses": cases[4].verdict() == "UNCERTIFIED_LOW_COVERAGE",
        "data_reuse_invalid": cases[5].verdict() == "INVALID_DATA_REUSE",
        "dependence_penalty_visible": mixing["slow_mixing_failure_upper"] > mixing["fast_mixing_failure_upper"],
        "raw_n_not_effective_n": mixing["raw_timepoints"] != mixing["effective_blocks"],
    }
}
assert all(result["assertions"].values())
out = Path(__file__).with_name("c2_stress.json")
out.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
