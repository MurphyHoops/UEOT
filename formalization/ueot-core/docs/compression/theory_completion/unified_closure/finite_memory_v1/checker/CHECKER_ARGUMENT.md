# Executable decision from exactly matched finite source data

Status: **ACTUAL_LEAN_BUILD_AND_NATIVE_REVIEW_CLEAR**. This note describes
`SupportMemoryCheck.lean`. The final source passed
[focused compilation](../actual-execution/compile-04/STATUS.json), the
[complete build](../actual-execution/full-build-01/FULL_BUILD_RECEIPT.json), and
[independent native execution review](../independent/ACTUAL_BUILD_NATIVE_REVIEW.md).
Canonical publication remains separately recorded.

## Program and reuse

`finiteMemoryCheck` receives a finite initial support `initial`, finite state
and action types, an observation map with decidable equality, and decidable
fixed transition and certification relations `R` and `C`. It calls the
existing `finiteRelationViabilityCheck` at

\[
B = 2^{|X|} - 1.
\]

For each `x ∈ initial`, it passes the entire initial support fiber
`initial.filter (fun z => q z = q x)`. Thus a common action must work for the
whole observed ambiguity set. Different hidden states with the same observation
are not given separate control decisions. The ambient observation type need
not have a finite enumeration; any possible initial observation has a witness
in the finite initial support.

No new recursive checker is introduced. The new wrapper supplies one explicit
horizon, tests all initial fibers, and connects the returned Boolean to the
already constructed infinite controller. Neither an unknown correct policy nor
a winning-family certificate is an input. The definition contains no Classical
selector and no actual PMF-support decider.

## Correctness and matching obligations

The actual-source theorem retains all three source identities:

| Obligation | Exact role |
|---|---|
| `h0 : x ∈ initial ↔ x ∈ p₀.support` | The enumerated initial supports are those of the original initial law. |
| `hR : z ∈ (P n x a).support ↔ R x a z` | The fixed table represents the same actual transition support at every time. |
| `hC : certified n x a ↔ C x a` | The checked row condition is the actual certification condition. |

The mathematical arena bound proves `M + 1 ≤ 2 ^ |X|`, hence `M ≤ B`, including
the natural-number subtraction edge. Refinement at `B` is therefore the same
fixed point as refinement at the exact arena cardinal `M`. The existing
finite relation checker correctness and homogeneous-support equivalence show
that each accepted initial fiber is winning, and conversely.

One actual-PMF support decider is introduced by `Classical.propDecidable` only
inside the proof in order to consume the pre-existing correctness theorem.
It is absent from the executable wrapper's arguments and body. This proof-only
use does not provide an algorithm for deciding arbitrary real PMF positivity.

The main endpoints are:

- `finiteMemoryCheck_iff_initial_winning`: accepted Boolean iff every nonempty
  actual initial observation fiber belongs to the greatest support fixed point;
- `finiteMemoryCheck_iff_controller_zero_uncovered`: accepted Boolean iff the
  same `supportMemoryController` has zero actual uncertified-row occupancy at
  every time;
- `finiteMemoryCheck_iff_exists_all_times_policy`: accepted Boolean iff some
  complete causal policy has zero actual uncertified-row occupancy at every time.

The converse directions use the existing finite-horizon viability theorem and
the proved fixed-point cutoff. They do not assume that any provided policy is
definitionally equal to the newly selected controller.

## Boundaries

The total finite-memory controller's winning-action selector remains
noncomputable. A computable decision and a mathematical controller construction
are separate delivered results; this wrapper does not claim executable policy
synthesis. Its explicit bound may be exponential and no runtime or query
complexity theorem is claimed.

An empty initial table is accepted as a vacuous finite Boolean problem. It
cannot match a genuine PMF's empty support through `h0`, so this corner case
does not assert a vacuous actual-source control theorem.

Exact finite tables must still be justified. Sampling, support estimation,
unknown or very small positive transition probabilities, noisy decisions,
and physical safety require their own results. Support homogeneity continues
to allow time-varying nonzero probability weights and does not produce a fixed
numerical killed matrix.
