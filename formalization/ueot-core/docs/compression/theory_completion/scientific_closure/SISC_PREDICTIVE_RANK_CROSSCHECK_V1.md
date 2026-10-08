# N1 predictive linear rank: exact-rational adversarial cross-check

Status: **local exact-arithmetic software PASS**. Separately:
`SISCStochasticTraceNoGo.lean` proves all-horizon equalities, and
`SISCLinearPredictiveLift.lean` proves finite-dimensional shift closure in
general. This file does **not** claim that the finite matrix rank was itself
machine-checked by Lean or independently verified on physical measurements.

`evidence/sisc_stochastic_predictive_rank_test.py` implements a *second*
calculation of the fixed six-state transition model using Python's exact
`Fraction`, a memoized observation-word probability recursion and rational
Gaussian elimination. It verifies 511 binary observation words, all words
of lengths 0 through 8 inclusive.

Results:

- 6 microscopically distinct source tokens;
- 5 distinguishable trace-law classes for the enumerated word family;
- **rational matrix rank 4** across those finite probes;
- source tokens 0 and 1 have identical tested trace laws;
- destination class {4} has transition probability 1 from token 0 and 0
  from token 1, defeating Markov-class lumpability;
- state 4's trace law is exactly the arithmetic average of states 2 and 3
  on every tested word.

The six-state **all-word** equalities and Markov contradiction are separately
machine-checked in Lean. Combined with those two full-horizon identities,
the finite rank-4 witness is consistent with the *full* response span having
rank four; the end-to-end `finrank=4` implication has not yet been promoted
to a single Lean theorem and is not reported as such.

Research implication: the smallest linear predictive state can be *smaller*
than the set of distinct observational trace classes and remains recursively
closed even when the latter does not form a Markov quotient. An application
must still certify accessible experiments, noisy estimator bounds, valid
belief filtering and separately grounded objecthood semantics.
