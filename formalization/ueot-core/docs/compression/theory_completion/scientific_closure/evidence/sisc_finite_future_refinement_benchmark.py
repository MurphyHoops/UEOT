#!/usr/bin/env python3
"""Executable validation of process-derived predictive quotient for finite systems.

All n≤3, two-action binary-output deterministic systems are exhausted;
larger n are deterministic samples. This is a *software test*, not a Lean
proof of an n−1 distinguishing-word bound and not independent physics data.
"""
from itertools import product
import random


def canonical_labels(signatures):
    labels = {}
    result = []
    for x in signatures:
        if x not in labels:
            labels[x] = len(labels)
        result.append(labels[x])
    return tuple(result)


def refine(read, step):
    n = len(read)
    m = len(step[0])
    partition = canonical_labels(read)
    for depth in range(n + 1):
        new_partition = canonical_labels(tuple(
            (read[s], *(partition[step[s][a]] for a in range(m)))
            for s in range(n)))
        if new_partition == partition:
            return partition, depth
        partition = new_partition
    raise AssertionError("no stabilization within n rounds")


def exhaustive_response_signature(read, step):
    n, m = len(read), len(step[0])
    words = [()]
    for k in range(1, n):
        words.extend(product(range(m), repeat=k))
    def response(s, w):
        for a in w:
            s = step[s][a]
        return read[s]
    return canonical_labels(tuple(tuple(response(s, w) for w in words)
                                  for s in range(n))), len(words)


def summary_valid(summary, read, step):
    return all(
        summary[x] != summary[y]
        or (read[x] == read[y]
            and all(summary[step[x][a]] == summary[step[y][a]]
                    for a in range(len(step[0]))))
        for x in range(len(read)) for y in range(len(read)))


def check(read, step, all_summaries=False):
    n = len(read)
    state, depth = refine(read, step)
    signature_state, tests = exhaustive_response_signature(read, step)
    assert all((state[x] == state[y]) == (signature_state[x] == signature_state[y])
               for x in range(n) for y in range(n))
    assert depth <= n - 1
    assert summary_valid(state, read, step)
    if all_summaries:
        for summary in product(range(n), repeat=n):
            if summary_valid(summary, read, step):
                assert all(summary[x] != summary[y] or state[x] == state[y]
                           for x in range(n) for y in range(n))
    return depth, tests


def main():
    systems = 0
    max_depth = 0
    for n in (1, 2, 3):
        for read in product(range(2), repeat=n):
            for transition in product(range(n), repeat=n * 2):
                step = tuple(tuple(transition[2*s:2*s+2]) for s in range(n))
                depth, tests = check(read, step, all_summaries=True)
                max_depth = max(max_depth, depth)
                systems += 1
    rng = random.Random(20261008)
    sampled = 0
    for n, count in ((4, 512), (5, 128)):
        for _ in range(count):
            read = tuple(rng.randrange(2) for _ in range(n))
            step = tuple(tuple(rng.randrange(n) for _ in range(2)) for _ in range(n))
            depth, tests = check(read, step)
            max_depth = max(max_depth, depth)
            sampled += 1
    # Two identical present observations can have disjoint future behaviors.
    read = (0, 0, 1)
    step = ((0, 0), (2, 1), (2, 2))
    classes, depth = refine(read, step)
    assert classes[0] != classes[1] and read[0] == read[1]
    # All-future identity can still merge distinct source tokens.
    assert refine((0, 0), ((0, 0), (1, 1)))[0] == (0, 0)
    print("FINITE_FUTURE_REFINEMENT_PASS")
    print("EXHAUSTIVE_SMALL_SYSTEMS", systems)
    print("LARGER_DETERMINISTIC_SAMPLES", sampled)
    print("MAX_REFINEMENT_DEPTH_OBSERVED", max_depth)
    print("VERIFIED", "quotient vs words length < n; recursive closure; minimality of finite summaries")


if __name__ == "__main__":
    main()
