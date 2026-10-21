#!/usr/bin/env python3
"""Exact finite-PMF witness: belief memory can be necessary for certification.

This is an executable mathematical example, not a Lean theorem, empirical
experiment, or proof of the general infinite-horizon belief-control theorem.
Only fractions and finite sets are used. Actual prefix probabilities are
propagated separately from the backward belief-support computation.
"""
from __future__ import annotations

from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import hashlib
import json

STATES = (0, 1)
ACTIONS = (0, 1)
OBSERVATIONS = ("star",)
INITIAL = {0: F(1)}


def observe(x):
    return "star"


def transition(x, a):
    return {1 - x: F(1)}


def certified(x, a):
    return x == a


def all_beliefs():
    return frozenset(
        frozenset(xs)
        for size in range(1, len(STATES) + 1)
        for xs in combinations(STATES, size)
        if len({observe(x) for x in xs}) == 1
    )


def successor(support, action, observation):
    return frozenset(
        x_next
        for x in support
        for x_next, prob in transition(x, action).items()
        if prob > 0 and observe(x_next) == observation
    )


def admissible_actions(support, winning):
    return tuple(
        action
        for action in ACTIONS
        if all(certified(x, action) for x in support)
        and all(
            not successor(support, action, obs)
            or successor(support, action, obs) in winning
            for obs in OBSERVATIONS
        )
    )


def backward(winning):
    return frozenset(s for s in all_beliefs() if admissible_actions(s, winning))


def belief_controller(support, fixed_point):
    """The entire controller has an explicit fixed fallback action, zero."""
    actions = admissible_actions(support, fixed_point) if support else ()
    return actions[0] if actions else 0


def memory_from_observed_history(history):
    support = frozenset(x for x, p in INITIAL.items() if p > 0
                        and observe(x) == history[0])
    for action, obs in history[1:]:
        support = successor(support, action, obs)
    return support


def exact_actual_prefixes(fixed_point, steps):
    # Key: (observed causal history, hidden state); value: exact probability.
    law = {((observe(x),), x): p for x, p in INITIAL.items()}
    result = []
    for n in range(steps + 1):
        assert sum(law.values()) == 1
        posterior_supports = {}
        for (history, x), mass in law.items():
            if mass > 0:
                posterior_supports.setdefault(history, set()).add(x)
        uncertified = F(0)
        next_law = {}
        action_law = {a: F(0) for a in ACTIONS}
        state_law = {x: F(0) for x in STATES}
        for (history, x), mass in law.items():
            memory = memory_from_observed_history(history)
            assert memory == frozenset(posterior_supports[history])
            action = belief_controller(memory, fixed_point)
            state_law[x] += mass
            action_law[action] += mass
            if not certified(x, action):
                uncertified += mass
            for x_next, probability in transition(x, action).items():
                new_history = history + ((action, observe(x_next)),)
                key = (new_history, x_next)
                next_law[key] = next_law.get(key, F(0)) + mass * probability
        assert uncertified == 0
        assert state_law[n % 2] == 1 and action_law[n % 2] == 1
        result.append({
            "time": n,
            "actual_state_pmf": {str(x): str(p) for x, p in state_law.items()},
            "selected_action_pmf": {str(a): str(p) for a, p in action_law.items()},
            "actual_uncertified_occupancy": str(uncertified),
            "posterior_support_equals_controller_memory": True,
        })
        law = next_law
    return result


def serialize_beliefs(collection):
    return sorted((sorted(s) for s in collection), key=lambda s: (len(s), s))


def main():
    for x in STATES:
        for a in ACTIONS:
            assert sum(transition(x, a).values()) == 1
    stages = [all_beliefs()]
    while True:
        following = backward(stages[-1])
        assert following <= stages[-1]
        stages.append(following)
        if stages[-1] == stages[-2]:
            break
    assert stages == [
        frozenset({frozenset({0}), frozenset({1}), frozenset({0, 1})}),
        frozenset({frozenset({0}), frozenset({1})}),
        frozenset({frozenset({0}), frozenset({1})}),
    ]
    # The hidden state toggles independently of the action. A stationary
    # current-observation law with p=P(action=0) therefore has U_0=1-p,
    # U_1=p. Derive the coefficients directly from actual state laws.
    fixed_action_failure = {
        str(a): [int(not certified(n % 2, a)) for n in range(2)]
        for a in ACTIONS
    }
    assert fixed_action_failure == {"0": [0, 1], "1": [1, 0]}
    assert all(sum(row) == 1 for row in fixed_action_failure.values())
    result = {
        "status": "EXACT_FINITE_PMF_WITNESS_PASS_NOT_GENERAL_LEAN_THEOREM",
        "model": {
            "states": list(STATES), "actions": list(ACTIONS),
            "observations": list(OBSERVATIONS), "p0": {"0": "1", "1": "0"},
            "transition": "M(x,a) = delta(1-x)",
            "certification": "certified(x,a) iff a=x",
            "time_homogeneous": True,
            "controller_fallback_action": 0,
        },
        "backward_belief_stages": [serialize_beliefs(w) for w in stages],
        "first_fixed_point_index": 1,
        "winning_beliefs": serialize_beliefs(stages[-1]),
        "exact_actual_prefixes": exact_actual_prefixes(stages[-1], 12),
        "stationary_original_observation_obstruction": {
            "parameter": "p=P(action=0), 0<=p<=1",
            "fixed_action_actual_failure_vectors_n0_n1": fixed_action_failure,
            "uncertified_at_n0": "1-p", "uncertified_at_n1": "p",
            "sum_at_n0_n1": "1",
            "joint_zero_possible": False,
        },
        "scope": [
            "Actual finite prefix probabilities were propagated with Fraction.",
            "The all-time alternating-policy assertion additionally follows by induction, recorded in the mathematical review.",
            "The finite execution alone is not a proof of an infinite-horizon theorem.",
            "Certification is the explicit row predicate; it is not an asserted physical safety event.",
            "This witness does not identify the policy with a Classical.choose viableFamilyPolicy.",
        ],
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    output = Path(__file__).with_name("BELIEF_MEMORY_WITNESS.json")
    output.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({
        "status": result["status"],
        "backward_belief_stages": result["backward_belief_stages"],
        "actual_times_checked": [0, 12],
        "all_occupancies_exactly_zero": True,
        "stationary_observation_obstruction": "U0+U1=1",
        "output": str(output),
        "source_sha256": result["source_sha256"],
        "output_sha256": hashlib.sha256(output.read_bytes()).hexdigest(),
    }, indent=2))


if __name__ == "__main__":
    main()
