#!/usr/bin/env python3
"""Independent exact-rational cross-check of stochastic belief event intertwining.

No physical measurement, no Lean proof replacement. Uses the archived fixed
six-state row stochastic kernel, computes all finite words through horizon six
with arbitrary exact-rational signed and normalized belief sources.
"""
from fractions import Fraction as Q
from itertools import product
from sisc_stochastic_predictive_rank_test import ROWS, EMIT, probability


def source_response(weights, word):
    return sum((weights[i] * probability(i, word) for i in range(6)), Q(0))


def step(weights, output):
    updated = [Q(0)] * 6
    for x in range(6):
        if EMIT[x] == output:
            for y, transition in ROWS[x].items():
                updated[y] += weights[x] * transition
    return tuple(updated)


def main():
    basis = [tuple(Q(int(i == j)) for i in range(6)) for j in range(6)]
    weights = [
        *basis,
        tuple((basis[0][i] + basis[1][i]) / 2 for i in range(6)),
        tuple(basis[0][i] - basis[1][i] for i in range(6)),
        (Q(1, 3), Q(1, 6), Q(1, 6), Q(1, 6), Q(1, 6), Q(0)),
        (Q(2), Q(-3), Q(1, 2), Q(0), Q(5, 2), Q(7, 3)),
    ]
    words = [w for n in range(7) for w in product((0, 1), repeat=n)]
    total = 0
    for b in weights:
        for output in (0, 1):
            post = step(b, output)
            evidence = sum(post, Q(0))
            assert evidence == source_response(b, (output,))
            for word in words:
                assert source_response(post, word) == source_response(b, (output,) + word)
                total += 1
            if all(v >= 0 for v in b):
                assert all(v >= 0 for v in post)
                if evidence > 0:
                    normalized = tuple(v / evidence for v in post)
                    assert sum(normalized) == 1
                    for w in words:
                        assert source_response(normalized, w) == (
                            source_response(b, (output,) + w) / evidence
                        )
                else:
                    assert all(v == 0 for v in post)
    # Distinct hidden belief vectors that produce the same observed future words
    # remain identical on all tested futures after either event update.
    assert basis[0] != basis[1]
    for w in words:
        assert source_response(basis[0], w) == source_response(basis[1], w)
        for output in (0, 1):
            assert source_response(step(basis[0], output), w) == (
                source_response(step(basis[1], output), w)
            )
    print("BELIEF_INTERTWINING_EXACT_RATIONAL_PASS")
    print("WEIGHT_VECTORS", len(weights))
    print("FUTURE_WORDS", len(words))
    print("PREFIX_EQUALITIES_CHECKED", total)
    print("PRE_ACTION_EMISSION_PROTOCOL", "true")
    print("SIGNED_AND_POSITIVE_SOURCES", "included")
    print("DISTINCT_TOKEN_BELIEFS", "predictively equivalent, event-congruent")
    print("LIMITATION", "finite horizon software cross-check; Lean proves all words")


if __name__ == "__main__":
    main()
