#!/usr/bin/env python3
"""Independent exact feedback checks consuming the frozen literal source probe.

No mean, fitness, success, or optimality is passed to the source.  One-step
counts are read from actual retained/newborn output records.  Higher moments
are the finite independent-subtree recursion of those same records.
"""
from __future__ import annotations

from collections import defaultdict
from fractions import Fraction as F
from hashlib import sha256
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
import json
import sys


HERE = Path(__file__).resolve().parent
SOURCE = HERE / "source-prototype.py"
spec = spec_from_file_location("ueot_frozen_core_source", SOURCE)
src = module_from_spec(spec)
sys.modules[spec.name] = src
spec.loader.exec_module(src)


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def actual_records(p, theta, body, atom):
    old = src.founder(theta, body, int(theta))
    receipt = src.tick(p, old, 0, atom)
    assert receipt["status"] == "executed"
    assert receipt["available"] == (
        receipt["actual_fee"]
        + sum(x.wallet for x in receipt["outputs"])
        + receipt["returned_to_environment"]
    )
    for child in receipt["outputs"]:
        assert src.decode(child.body) == (theta, False)
        if child.identity == old.identity:
            assert child.parent == old.parent and child.age == old.age + 1
        else:
            assert child.parent == old.identity and child.born_at == 1 and child.age == 0
    return receipt["outputs"]


def one_step_count_law(p, theta):
    law = defaultdict(F)
    for atom, weight in src.atoms(p):
        law[len(actual_records(p, theta, False, atom))] += weight
    assert sum(law.values()) == 1 and set(law) == {0, 1, 2}
    return dict(law)


def moments(p, horizon):
    """Finite tree moments; output records choose both actual recursive slots."""
    mu = {(theta, body): F(1) for theta in (False, True) for body in (False, True)}
    second = dict(mu)
    path = []
    for t in range(horizon + 1):
        k0 = p.survival + p.common_birth
        k1 = p.survival - p.care_only_survival + p.common_birth + p.bloom_only_birth
        lam = (k0, (1 - p.damage) * k1 + p.damage * k0)
        if t:
            for theta in (False, True):
                for body in (False, True):
                    first_rate = k1 if theta and not body else k0
                    assert mu[theta, body] == first_rate * lam[int(theta)] ** (t - 1)
        v0 = second[False, False] - mu[False, False] ** 2
        v1 = second[True, False] - mu[True, False] ** 2
        assert v0 >= 0 and v1 >= 0
        path.append(dict(T=t, lower_mean=mu[False, False], upper_mean=mu[True, False],
                         lower_variance=v0, upper_variance=v1,
                         outside_mean_share=mu[False, False] / (mu[False, False] + mu[True, False])))
        if t == horizon:
            break
        next_mu, next_second = {}, {}
        for theta in (False, True):
            for body in (False, True):
                a = b = F(0)
                for atom, weight in src.atoms(p):
                    children = actual_records(p, theta, body, atom)
                    kinds = [(src.decode(x.body)[0], src.damaged(x.body)) for x in children]
                    child_means = [mu[k] for k in kinds]
                    a += weight * sum(child_means)
                    # The two occupied subtree tapes are independent.  Empty
                    # slots contribute zero; no survivor conditioning occurs.
                    cross = 2 * child_means[0] * child_means[1] if len(kinds) == 2 else 0
                    b += weight * (sum(second[k] for k in kinds) + cross)
                next_mu[theta, body] = a
                next_second[theta, body] = b
        mu, second = next_mu, next_second
    return path


def main():
    p = src.Parameters(F(3, 4), F(1, 8), F(3, 8), F(1, 4), F(1, 3))
    p.validate()
    assert p.survival + p.common_birth > 1
    laws = [one_step_count_law(p, theta) for theta in (False, True)]
    assert laws == [{0: F(5, 32), 1: F(9, 16), 2: F(9, 32)},
                    {0: F(9, 64), 1: F(15, 32), 2: F(25, 64)}]

    total_zero = mean_total = mean_upper = ratio_zero_extension = best_lost = F(0)
    for a, pa in laws[0].items():
        for b, pb in laws[1].items():
            weight, n = pa * pb, a + b
            mean_total += weight * n
            mean_upper += weight * b
            total_zero += weight * (n == 0)
            best_lost += weight * (b == 0 and a > 0)
            if n:
                ratio_zero_extension += weight * F(b, n)
    assert total_zero == F(45, 2048)
    assert ratio_zero_extension == F(2095, 4096)
    conditional_ratio = ratio_zero_extension / (1 - total_zero)
    assert conditional_ratio == F(2095, 4006)
    ratio_means = mean_upper / mean_total
    assert ratio_means == F(10, 19)
    assert len({ratio_zero_extension, conditional_ratio, ratio_means}) == 3
    assert best_lost == F(243, 2048)

    path = moments(p, 64)
    epsilon, eta = F(1, 5), F(1, 10)
    chosen = next(row for row in path if row["outside_mean_share"] <= epsilon / 2)
    total_mu = chosen["lower_mean"] + chosen["upper_mean"]
    # For two independent founder lineages, Var(total)=v0+v1.  Selected-outside
    # variance plus total variance is therefore 2v0+v1.
    vsum = 2 * chosen["lower_variance"] + chosen["upper_variance"]
    required = 36 * vsum / (eta * epsilon ** 2 * total_mu ** 2)
    n = (required.numerator + required.denominator - 1) // required.denominator
    assert n > 0 and 36 * vsum / (n * epsilon ** 2 * total_mu ** 2) <= eta
    T = chosen["T"]
    bill = 2 * n + 10 * n * (2 ** T - 1)
    report = {
        "schema": "UEOT/CORE_ACTUAL_COHORT_FEEDBACK_PROBE/V1",
        "status": "PASS_EXACT_SOURCE_CHECK_NOT_EMPIRICAL_SUPPORT",
        "empirical_support": "UNVERIFIED",
        "source_sha256": sha256(SOURCE.read_bytes()).hexdigest(),
        "parameters": vars(p),
        "actual_one_step_count_laws": laws,
        "same_source_counterexamples": {
            "zero_population_probability": total_zero,
            "expected_upper_ratio_with_zero_extension": ratio_zero_extension,
            "expected_upper_ratio_given_nonzero": conditional_ratio,
            "ratio_of_expected_counts": ratio_means,
            "best_extinct_inferior_nonzero_first_round": best_lost,
            "no_claim_of_inferior_permanent_survival": True,
        },
        "horizons_checked": 65,
        "mean_closed_form_checked_from_actual_outputs": True,
        "cohort_moments_from_actual_independent_subtree_slots": True,
        "selection_example": {
            "epsilon": epsilon, "eta": eta, "T_chosen_first": T,
            "outside_mean_share": chosen["outside_mean_share"],
            "lower_mean": chosen["lower_mean"],
            "upper_mean": chosen["upper_mean"],
            "total_mean": total_mu,
            "lower_variance": chosen["lower_variance"],
            "upper_variance": chosen["upper_variance"],
            "total_variance": chosen["lower_variance"] + chosen["upper_variance"],
            "outside_variance_plus_total_variance": vsum,
            "cohorts_chosen_second": n,
            "cohort_count_uses_exact_moments_not_D_power_bound": True,
            "exact_failure_bound": 36 * vsum / (n * epsilon ** 2 * total_mu ** 2),
            "worst_case_initial_capital_plus_source_inflow": bill,
            "resource_limit": "This is a required bound, not free replication or a claim that a fixed budget can fund it.",
        },
        "moments": path,
    }
    out = HERE / "source-feedback-probe.json"
    out.write_text(json.dumps(encode(report), ensure_ascii=False, indent=2) + "\n")
    print(json.dumps(encode({k: v for k, v in report.items() if k != "moments"}),
                     ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
