# Experimental verification of the finite-state intuition (method test)

Status: **LOCAL DETERMINISTIC SOFTWARE TEST PASS**, not a new Lean proof of
word-length complexity, non-deterministic model, or external physical data.

`evidence/sisc_finite_future_refinement_benchmark.py` independently implements
finite deterministic partition refinement of source states by their present
output and all immediately reachable successor response classes. It compares
the fixed point against brute-force response signatures on *every* input word
of length `< n`, where `n` is the finite source-state count.

The test also enumerates candidate finite summaries to check minimality:
any exact observation-preserving, action-congruent summary is at least as fine
as the resulting predictive quotient (i.e., it never merges its distinct
future classes).

Results on this fixed source implementation:

- Exhaustively tested all **5898** binary-output, two-action deterministic
  transition/observation tables with `n = 1,2,3`.
- Tested **640** additional reproducible deterministic sampled systems with
  `n = 4,5` (seed 20261008).
- All compared partition classes matched their full finite-word
  response signatures for words of length `< n`.
- Maximum observed refinement depth was **3** in the examined systems.
- Included one pair of equal-present-response states separated by future
  interventions, and one distinct-token pair never separated.

**Interpretation:** This supports the next scientific/mathematical program of
replacing the nonconstructive pairwise distinguishing-word selection with a
constructive finite partition-refinement algorithm and a *machine-checked*
word-length bound. Although the tested cases are exhaustive for n≤3, they do
not prove the general n−1 claim. The separately machine-checked theorem only
guarantees existence of at most `|X|²` separating words, without a bound on
each witness length. These claims must remain separate.

This executable test generates no new UEOT real-world observational support
and does not affect Core status or the C7 external-review gate.
