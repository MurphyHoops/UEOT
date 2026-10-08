#!/usr/bin/env python3
"""Exact-rational end-to-end check: coordinate-mean C2 candidate decisions.

The generative law is one Bernoulli microscopic post-action state with
P(Y=True)=1/3. Two observation coordinates (Y, 1-Y) are fully dependent
within each sample, but temporally IID samples satisfy the existing frozen
finite-coordinate Hoeffding theorem. We enumerate *all binomial counts*
for a fixed N with exact rational probabilities, not Monte Carlo.

This script is a standalone software method check, NOT an empirical
demonstration or a replacement for the general Lean proof.
"""
from collections import Counter
from fractions import Fraction as Q
from math import comb, exp


N = 300
U = Q(1, 10)
RADIUS = 2 * U
THRESHOLD = Q(1, 4)
P = Q(1, 3)
TARGETS = {
    "true": (Q(1, 3), Q(2, 3)),
    "bad_a": (Q(4, 5), Q(1, 5)),
    "bad_b": (Q(1, 10), Q(9, 10)),
}


def loss(mean, pair):
    return abs(mean - pair[0]) + abs(1 - mean - pair[1])


def certified(score):
    if score + RADIUS <= THRESHOLD:
        return "certified"
    if THRESHOLD < score - RADIUS:
        return "rejected"
    return "ambiguous"


def resolve(mean):
    decisions = {name: certified(loss(mean, target))
                 for name, target in TARGETS.items()}
    possible = [name for name, decision in decisions.items()
                if decision != "rejected"]
    if len(possible) == 1 and decisions[possible[0]] == "certified":
        return ("unique", possible[0])
    return ("ambiguous", None) if possible else ("uncovered", None)


def main():
    truths = {name: loss(P, pair) for name, pair in TARGETS.items()}
    compatible = {name for name, risk in truths.items() if risk <= THRESHOLD}
    assert compatible == {"true"}
    status_counts = Counter()
    good_mass = Q(0)
    bad_calibration_mass = Q(0)
    wrong_unique_mass = Q(0)
    false_uncovered_mass = Q(0)
    total_mass = Q(0)
    nonvacuous_unique = False
    for k in range(N + 1):
        mean = Q(k, N)
        weight = comb(N, k) * P ** k * (1 - P) ** (N - k)
        total_mass += weight
        good = abs(mean - P) <= U  # both coordinates share this error.
        status, chosen = resolve(mean)
        status_counts[(status, chosen)] += 1
        all_valid = all(abs(loss(mean, pair) - risk) <= RADIUS
                        for (name, pair), risk in zip(TARGETS.items(), truths.values()))
        if good:
            good_mass += weight
            assert all_valid, (k, mean)
        if not all_valid:
            bad_calibration_mass += weight
        if status == "unique":
            if chosen not in compatible or any(
                other != chosen for other in compatible
            ):
                wrong_unique_mass += weight
            if chosen == "true" and good:
                nonvacuous_unique = True
        if status == "uncovered" and compatible:
            false_uncovered_mass += weight
    assert total_mass == 1
    assert nonvacuous_unique
    bound = 2 * len((0, 1)) * exp(-2 * N * float(U) ** 2)
    assert 0 < bound < 1
    assert float(bad_calibration_mass) <= bound
    assert float(wrong_unique_mass) <= bound
    assert float(false_uncovered_mass) <= bound
    assert bad_calibration_mass <= 1 - good_mass
    # Negative control: expected absolute residual differs from mismatch
    # of expected mean. This precisely motivates mean-first estimation.
    assert P * abs(Q(1) - Q(1, 2)) + (1-P) * abs(Q(0) - Q(1, 2)) != abs(P - Q(1, 2))
    print("N4_COORDINATE_CALIBRATION_METHOD_PASS")
    print("SAMPLE_SIZE", N)
    print("REGISTERED_COORDINATES", 2)
    print("CANDIDATES", len(TARGETS))
    print("POTENTIALLY_DEPENDENT_COORDINATES", "yes, Y and 1-Y")
    print("DISTINCT_BINOMIAL_COUNTS", N + 1)
    print("STATUS_COUNTS", dict(status_counts))
    print("HOEFFDING_UNION_BOUND", format(bound, ".8g"))
    print("P_BAD_COORDINATE_GOOD_EVENT", format(float(1-good_mass), ".8g"))
    print("P_BAD_CALIBRATION", format(float(bad_calibration_mass), ".8g"))
    print("P_WRONG_UNIQUE", format(float(wrong_unique_mass), ".8g"))
    print("P_FALSE_UNCOVERED", format(float(false_uncovered_mass), ".8g"))
    print("SCIENTIFIC_SCOPE", "synthetic exact-rational finite-model check only")


def check_strong_separation_power():
    """High-probability *recovery*, not merely error prevention, with margin."""
    n = 2000
    u = Q(1, 20)
    r = 2 * u
    threshold = THRESHOLD
    truth = TARGETS["true"]
    assert loss(P, truth) + 2*r <= threshold
    assert all(threshold + 2*r < loss(P, pair)
               for name, pair in TARGETS.items() if name != "true")
    weight = (1-P) ** n
    prob_failure = Q(0)
    prob_bad_good_event = Q(0)
    prob_unique = Q(0)
    for k in range(n+1):
        mean = Q(k,n)
        decisions = {name: (
            "certified" if loss(mean,pair)+r <= threshold else
            "rejected" if threshold < loss(mean,pair)-r else
            "ambiguous") for name,pair in TARGETS.items()}
        possible = [name for name,d in decisions.items() if d != "rejected"]
        unique_true = (possible == ["true"] and decisions["true"] == "certified")
        good = abs(mean - P) <= u
        if good:
            assert unique_true, (k,mean,decisions)
        else:
            prob_bad_good_event += weight
        if not unique_true:
            prob_failure += weight
        else:
            prob_unique += weight
        if k < n:
            weight = weight * Q(n-k,k+1) * (P/(1-P))
    bound = 4 * exp(-2*n*float(u)**2)
    assert 0 < bound < 1
    assert prob_failure <= prob_bad_good_event
    assert float(prob_failure) <= bound
    print("N4_STRONG_SEPARATION_POWER_PASS")
    print("POWER_SAMPLE_SIZE",n)
    print("POWER_COORDINATE_RADIUS",float(r))
    print("POWER_MARGINS_STRICT", "passed")
    print("POWER_HOEFFDING_FAILURE_BOUND",format(bound, ".8g"))
    print("POWER_ACTUAL_NONRECOVERY_PROB",format(float(prob_failure), ".8g"))
    print("POWER_ACTUAL_UNIQUE_PROB",format(float(prob_unique), ".8g"))
    print("POWER_SCOPE", "model-based exact binomial enumeration, not measured physics")


if __name__ == "__main__":
    main()
    check_strong_separation_power()
