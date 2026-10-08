#!/usr/bin/env python3
"""SISC SI-3 deterministic mechanism stress; NOT natural-system evidence.

Only Python standard library is used. Refuse invalid row-stochastic input.
Positive case derives transport formation, negative case shows that relaxing
normalization breaks the claimed nonexpansive theorem.
"""
import json


def weighted(K, response):
    return [sum(w * v for w, v in zip(row, response)) for row in K]


def channel_valid(K):
    return all(all(w >= 0 for w in row) and abs(sum(row) - 1) < 1e-12 for row in K)


def max_distance(a, b):
    return max(abs(x - y) for x, y in zip(a, b))


def run():
    channel = [[0.9, 0.1], [0.2, 0.8]]
    old_world = [0.4, 0.6]
    old_parent = [0.43, 0.57]
    tau = max_distance(old_world, old_parent)
    delta_world, delta_parent = 0.015, 0.02
    w_new = [x + e for x, e in zip(weighted(channel, old_world), [0.01, -0.015])]
    p_new = [x + e for x, e in zip(weighted(channel, old_parent), [-0.02, 0.012])]
    assert channel_valid(channel)
    assert tau <= 0.03 + 1e-12
    assert max_distance(w_new, weighted(channel, old_world)) <= delta_world + 1e-12
    assert max_distance(p_new, weighted(channel, old_parent)) <= delta_parent + 1e-12
    total_budget = delta_world + tau + delta_parent
    observed = max_distance(w_new, p_new)
    assert observed <= total_budget + 1e-12

    bad_channel = [[2.0, 0.0]]
    assert not channel_valid(bad_channel)
    bad_old_a, bad_old_b = [1.0, 0.0], [0.0, 0.0]
    assert max_distance(weighted(bad_channel, bad_old_a), weighted(bad_channel, bad_old_b)) > max_distance(bad_old_a, bad_old_b)

    report = {
        "kind": "SISC_SI3_FINITE_MECHANISM_METHOD_TEST_NOT_REAL_WORLD_EVIDENCE",
        "positive": {
            "channel_normalized": True,
            "source_tau": tau,
            "world_residual_budget": delta_world,
            "parent_residual_budget": delta_parent,
            "derived_bound": total_budget,
            "observed_target_distance": observed,
            "passed": True,
        },
        "negative": {
            "unnormalized_channel_rejected": True,
            "nonexpansive_conclusion_fails_without_normalization": True,
        },
    }
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    run()
