# Independent static review: C3 search and actual Doob witness

Status: STATIC_MATHEMATICAL_API_CLEAR. Actual Lean execution is a separate gate.

Reviewer: `finite_window_source`, independently of the authors of the two
reviewed files. The reviewer authored the finite-window and Doob source APIs
consumed by the witness; this record is therefore not an independent review
of those API implementations. The other independent source review covers
that responsibility.

Date: 2026-10-22. Baseline: accepted main
`50a91fb9c81e0f5e698ce2cc02ec1a44c9583b04`.

## Exact reviewed source identities

| File in `UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/` | SHA256 |
| --- | --- |
| `C3ExecutableSearch.lean` | `6a70601f35f12edf0eaf881a39aa36fc8d22d5b42111d0c937fa92948df70abc` |
| `FiniteWindowDoobWitness.lean` | `542bec9e3a96e97622090191915f1a60b4c5a8df3db9496119bcd48d86532934` |

Both complete files were read. The hashes above were read from the same local
source files after that review. Compile-04 was queued/running when this record
was written. No claim of a successful compile, axiom audit, native build or
production integration is made here. Later changes need their own delta
review; this record retains the identities of this stage.

## C3 executable search

The actual `scan` program receives a Boolean oracle, a start index and finite
fuel. It inspects the current index, stops at the first true result, and
otherwise recurses at the next index while recording the current query. The
output is computed from these data. An externally chosen good index is not
an input.

The following source claims are mathematically consistent with this program:

- `scan_found_iff` characterizes the first positive oracle value in the
  requested half-open interval, including the preceding negative values.
- `scan_none_iff` characterizes a negative result at every index in that
  interval.
- The trace length is exactly the available fuel on failure and exactly
  `i - start + 1` on success at `i`. The membership and no-duplicates results
  account for the recorded indices. The resulting query bound is the interval
  length.
- `familyOracle` exposes exactly the registered `n + 1` candidates; its
  off-table extension is outside every possible query of `search`.
- The semantic bridge uses the explicit premise that each registered Boolean
  answer is equivalent to `Good` on the same candidate. The existing
  `firstGoodIndex` occurs in the theorem conclusion and proof, not in the
  executable input.
- Monotonicity of `Good` is unnecessary for a linear first-positive scan.
  Nestedness of the candidate family is used only to conclude that no
  strictly smaller good carrier exists within that registered family. The
  inclusion argument is valid even if the family contains duplicates.

The threshold, exhaustive-negative and nonmonotone examples match the three
different execution behaviors. They do not purport to construct a physical
intervention oracle.

Scope retained: the oracle is exact; its internal evaluation cost is outside
the query-count result; the domain of minimality and failure certification is
the registered family. The result does not enumerate all minimal carriers,
establish a powerset-wide optimum, or certify noisy oracle answers. No static
mathematical blocker was found.

## Actual three-state finite-window / Doob witness

The original state space is `Option Bool`. `none` is the absorbing cemetery;
the two `some` states form the safe subtype. A one-element action type and
constant observation/feedback make the original controlled source explicit.
Its rows, including the cemetery column, are stochastic and nonnegative.

The safe killed matrix is defined by restricting this actual model and its
actual feedback. In the order `false`, `true`, it is

\[
Q=\begin{pmatrix}3/8&3/8\\1/8&1/8\end{pmatrix}.
\]

The original initial PMF is the uniform safe PMF embedded into the original
three-state alphabet. Its cemetery mass is zero. The file proves the left
QSD equation for this same matrix and safe law:

\[
\eta Q=\tfrac12\eta,
\qquad \eta=(\tfrac12,\tfrac12).
\]

The actual survival law is obtained through the existing same-source QSD
endpoint. The right data use `rho = 1/2` and

\[
h=(3/2,1/2),\qquad Qh=\tfrac12h,\qquad \langle\eta,h\rangle=1.
\]

Consequently the natural Doob initial law is `(3/4,1/4)` and each Doob
transition row is also `(3/4,1/4)`. These values belong to the actual PMF
constructed by the Doob path API, not an independently asserted pair table.

`conditionedPair` filters the original complete action/state experiment on
survival through time one and retains the complete state pair. Its safe atoms
are obtained from `actual_conditioned_safe_path_mass`. `doobPair` maps the
genuine `doobPathLaw` into the same original pair alphabet, with injectivity
proved for the embedding. In the safe pair order `(false,false)`,
`(false,true)`, `(true,false)`, `(true,true)`, the atom tables are

| Actual pair law | Four safe atoms |
| --- | --- |
| Survival-conditioned original source | `(6, 6, 2, 2) / 16` |
| Natural initial-tilt Doob source | `(9, 3, 3, 1) / 16` |

The actual filtered-source support theorem removes every conditioned atom
with a cemetery coordinate. The Doob map has the same support exclusion.
Thus the final calculation covers all nine atoms of the common original
pair space. The absolute differences on its four safe atoms are
`(3,3,1,1)/16`, so the L1 distance is `1/2` and total variation is `1/4`.
Equivalently, the sum of pointwise common mass is `3/4`, which is the form
used by the existing TV theorem in the implementation.

This witness establishes that a genuine left QSD does not identify the
complete finite-window conditioned path with the stationary Doob path even
when that Doob path receives its natural initial tilt. It preserves the
original model, initial PMF, source feedback, killed matrix and positive right
data throughout. It makes no Q-process limit or spectral convergence claim.
No static mathematical or source-identity blocker was found.

## Review decision

Both reviewed source snapshots receive STATIC_MATHEMATICAL_API_CLEAR within
the scopes stated above. Actual compilation and later integration receipts
must be attached separately and must identify the source bytes they tested.

## Addendum: compile-08 witness candidate

The witness candidate submitted for compile-08 has SHA256
`e37d32b9f5da631392706e60c68d21fcb26491fea1c67614be57afbf6d4b0455`.
Its complete source delta was compared with the original reviewed
`542bec9e3a96e97622090191915f1a60b4c5a8df3db9496119bcd48d86532934`
snapshot from the preserved compile-04 input.

The changes qualify the correct `colApply`, make already established scalar
and PMF identities explicit before arithmetic, use named nonnegativity proofs
with the exact killed-matrix and initial-row types, and correct the equality
orientation in the cemetery-map contradiction. The conditioned cemetery
proof now consumes the safe-prefix conjunction directly. No model, matrix,
initial law, event, conditioning hypothesis, eigenvector, atom-table statement
or TV conclusion changes.

The final Doob atom calculation explicitly invokes `doob_path_atom` with the
actual source initial row and the named killed-matrix nonnegativity proof.
This strengthens visibility of the source connection. The updated snapshot
receives STATIC_MATHEMATICAL_API_CLEAR; its actual compile result is still a
separate receipt.

The existing atom tables also show that both horizon-one pair laws have
initial marginal `(3/4,1/4)`. The final transition row is `(1/2,1/2)` under
finite-window conditioning and `(3/4,1/4)` under the Doob law. Thus the
counterexample already uses matching natural initial marginals; its
separation does not arise from selecting an incompatible Doob initial PMF.

### Execution notice after the static addendum

The coordinating root reported compile-09 PASS for the same witness
`e37d32b9f5da631392706e60c68d21fcb26491fea1c67614be57afbf6d4b0455`
in 4.082827625 seconds with an empty log, following successful sequential
compilation of Window `61feecf09bd38d2b5497a7be33d073b1c04cd20a3e45a6840af19dd1670af363`
and Doob `1bcf2d6baaa55e4ea648d19a78dc490a86b525eaaa109464654184d447544081`.
No witness source change occurred between this addendum and that reported
execution. Its final static verdict remains CLEAR. Execution was performed
by the coordinating root and is documented in the separate focused-chain
and aggregate receipts.
