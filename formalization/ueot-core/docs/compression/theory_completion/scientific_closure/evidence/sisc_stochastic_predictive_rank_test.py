#!/usr/bin/env python3
"""Exact-rational six-state trace no-go and predictive span rank check.

This is an independent algorithmic cross-check of formalized fixed examples,
not an external experiment or a second-party audit of Lean's kernel.
"""
from functools import lru_cache
from fractions import Fraction
from itertools import product


ROWS = (
    {4: Fraction(1)},
    {2: Fraction(1, 2), 3: Fraction(1, 2)},
    {2: Fraction(1)},
    {5: Fraction(1)},
    {2: Fraction(1, 2), 5: Fraction(1, 2)},
    {5: Fraction(1)},
)
EMIT = (0, 0, 0, 0, 0, 1)


@lru_cache(None)
def probability(state, word):
    if not word:
        return Fraction(1)
    if word[0] != EMIT[state]:
        return Fraction(0)
    return sum((p * probability(y, word[1:]) for y, p in ROWS[state].items()),
               Fraction(0))


def rank(rows):
    a = [list(row) for row in rows]
    pivot = 0
    for col in range(len(a[0])):
        start = next((i for i in range(pivot, len(a)) if a[i][col]), None)
        if start is None:
            continue
        a[pivot], a[start] = a[start], a[pivot]
        divisor = a[pivot][col]
        a[pivot] = [v / divisor for v in a[pivot]]
        for i in range(len(a)):
            if i != pivot and a[i][col]:
                v = a[i][col]
                a[i] = [u - v * w for u, w in zip(a[i], a[pivot])]
        pivot += 1
        if pivot == len(a):
            break
    return pivot


def main():
    assert all(sum(row.values()) == 1 for row in ROWS)
    words = [word for k in range(9) for word in product((0, 1), repeat=k)]
    signatures = [tuple(probability(x, word) for word in words) for x in range(6)]
    assert signatures[0] == signatures[1]
    assert all(2 * probability(4, word) == probability(2, word) + probability(3, word)
               for word in words)
    assert probability(2, (0, 0)) == 1
    assert probability(3, (0, 0)) == 0
    assert probability(4, (0, 0)) == Fraction(1, 2)
    groups = {}
    for x, sig in enumerate(signatures):
        groups.setdefault(sig, []).append(x)
    assert len(groups) == 5, groups
    dest = next(sig for sig, members in groups.items() if members == [4])
    def mass_to_class(x, key):
        return sum((p for y, p in ROWS[x].items() if signatures[y] == key), Fraction(0))
    assert mass_to_class(0, dest) == 1
    assert mass_to_class(1, dest) == 0
    linear_rank = rank(signatures)
    assert linear_rank == 4, linear_rank
    print('STOCHASTIC_EXACT_RATIONAL_CROSSCHECK_PASS')
    print('HORIZONS_EXAMINED', '0..8')
    print('NUMBER_OF_WORDS', len(words))
    print('TOKEN_STATES', 6)
    print('DISTINCT_PREDICTIVE_TRACE_CLASSES', len(groups))
    print('FINITE_TRUNCATED_PREDICTIVE_SPAN_RANK', linear_rank)
    print('LUMPABILITY_CONTRADICTION', 'same full-trace law; dest-class masses 1 versus 0')
    print('CLAIM_LIMIT', 'finite horizon software rank; all-horizon trace/lumpability proved separately in Lean')


if __name__ == '__main__':
    main()
