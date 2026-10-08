# N2 stochastic belief update — exact-rational independent algorithm test

Status: LOCAL METHOD CHECK, not independent reviewer and not physical evidence.

The script `evidence/sisc_belief_intertwining_exact_test.py` reimplements the earlier six-state fixed stochastic process in Python `fractions.Fraction`. Its probability recursion comes from the existing six-state test fixture, but **belief updates and mixture-level response checking are a separately written procedure**.

For 10 source vectors (six point masses, two mixtures, one signed token-difference, one signed general vector), 2 observed Boolean symbols and **127** future words of lengths 0–6, it verifies **2,540 exact rational equalities**:

`F_(U_(a,o)b)(w) = F_b((a,o)::w)`.

It independently checks event likelihood as total unnormalized mass, nonnegativity for nonnegative sources, valid normalization and continuation at strictly positive evidence, zero vector after an impossible event for nonnegative sources, and event congruence of distinct but trace-equivalent source-token point masses.

Result: **BELIEF_INTERTWINING_EXACT_RATIONAL_PASS**.

This test only covers the finite enumerated horizons, whereas `SISCStochasticPredictiveIntertwining.lean` formally proves general finite-word equalities. It does not identify the stochastic model from empirical measurements or close causal object identity and persistence.
