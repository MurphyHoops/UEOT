# SISC rowwise probe implementation: source and scope

This note describes the new source-level increment implementing the reviewed
`global_review_tail_v1/books-global/SISC_PROBE_CONTRACT_V2.md`. Actual compilation
and native export receipts are recorded separately by the integration owner;
this note itself is not a build receipt.

## 1. Actual sampling experiment and scalar budget

`UnifiedClosure/RowwiseProbeSampling.lean` defines the common event directly from
the actual population means and row-specific empirical means. The finite probe
type J, every allocation N_j > 0, the outcome functions, true row laws and u >= 0
are fixed before sampling. Samples are measurable and independent within each
row under one probability measure, with their true row marginals explicitly
proved or supplied. Cross-row independence is not required by the general
bound.

The existing `BoundedLossTwoSided.measure_empiricalRisk_bad_le` is applied once
per row, and only the probe events are unioned. This proves

\[
\mu^{\mathrm{real}}(G^c)\le
\min\left(1,\sum_j 2e^{-2N_ju^2}\right).
\]

There is no candidate-count penalty and no PMF-TV state-subset factor. The
measurability of G is separately proved. Empty J gives G = univ and budget zero
for this pure concentration layer; it cannot construct an N3 protocol, whose
`observed_nonempty` field remains required.

The product-experiment specialization reuses the actual
`VariableRegisteredSamples.productRowLaw`, `productRowSample` and their
measurability, marginal and within-row independence theorems. Its sample space
is `(Sigma j, Fin (N j)) -> X`. Each coordinate is a separate experimental unit;
different treatment outcomes are not asserted to be jointly observed in one
unit. The generic scalar theorem does not need the sample-value type to be
finite, although the N3 model and the concrete witness are finite.

## 2. N3/N4 candidate calibration and power

`UnifiedClosure/SISCRowwiseProbeCalibration.lean` retains the existing logical
namespace `ScientificClosure.SISC` and all the original protocol fields except
the interval estimator. Its input `RowwiseCoordinateLawMatchesKernel` identifies
each actual group mean with the same original kernel/source/action/read
coordinate. The theorem `rowwise_population_risk_eq_registered` then derives
the risk identity. The final risk identity is not postulated as a structure
field, and predictions are exactly `P.prediction`.

The constructed interval has:

| Field | Actual value |
|---|---|
| estimate | Sum of absolute empirical-coordinate mismatches |
| statistical radius | `(card J) * u` |
| drift radius | `0` |
| total radius | `(card J) * u` |

The existing coordinate L1 Lipschitz theorem calibrates all registered
candidates on the same G. The candidate type itself need not be finite; the
registry is a finite set. Existing N4 two-radius margins establish unique
identification. The true candidate is an argument to the correctness theorem
only, not to the interval constructor or resolver.

The failure set is bounded by inclusion in the measurable G complement. The
present API reports a `mu.real` **outer-measure bound** on that failure set; it
does not separately export a `MeasurableSet` theorem for the resolver or the
failure set. This still supplies a measurable good event on which the stated
success result holds. Do not advertise an additional resolver measurability
certificate.

## 3. N6 intervention and transfer audit

The new rowwise audit uses the empirical mean of each actual probe group.
Independent assumptions identify these means with the specified parent's
reference responses and authenticate transfer to the specified child. The
existing `LocalResponseGap` is used with its full type-wide quantifier:

\[
\forall d\ne c,\ \exists j,\quad 2u<|R_c(j)-R_d(j)|.
\]

It is not weakened to registered or authenticated competitors. On G the new
audit meets the existing deterministic source-singleton theorem; the same
scalar budget bounds failure. As with N3, the exported failure estimate is an
outer-measure bound, without an additional measurable-resolver theorem.

The audit structure's response field is updated with these data, but each
theorem concerns the specified child with its own model and transfer premises.
No conclusion about another child, physical genealogy, object identity, or
offspring status follows without its respective external bridge.

## 4. Concrete witness and mismatch boundary

`UnifiedClosure/SISCRowwiseProbeWitness.lean` has two actual probes and two
registered candidates. The allocations are 128 and 256. Each group repeats the
same declared action and next-state law (the point mass at Boolean false), and
only its own coordinate is read. The actual sigma-indexed product law proves
the sampling premises; the kernel/read mean match is proved directly. Both N3
candidate power and N6 audited-source power are instantiated. The N6 toy's
transfer predicate is explicitly true and is not inferred from response fit.

The exact confidence expression is `2 exp(-4) + 2 exp(-8)`. A deliberately
conservative exact inequality gives at most `28/45`, so the bound is strictly
below one without relying on decimal exponent evaluation. This is a formal
experiment on a specified probability law, not a new physical data collection.

The negative control changes only the declared source kernel to the point mass
at Boolean true while retaining the actual data law at false. The actual mean
is zero and the declared kernel mean is one. The mean-matching predicate is
therefore false. A concrete all-zero record belongs to the exact actual-mean
Good event while the wrong kernel's newly constructed interval fails
calibration. Perfect concentration about the data's mean cannot repair a
misspecified target source.

## 5. Remaining scientific scope

Fixed positive N_j is not random stopping or adaptive sampling. General
within-row dependence, drifting protocols, real intervention implementation,
model adequacy, authentication soundness, and physical genealogy remain
separate obligations. This increment adds a genuine rowwise statistical bridge;
it does not close the full original C2/C7 tasks or alter the frozen 106 P-ID
ledger, its 11/89/6 classification, or the four counted generators.

## 6. Focused execution checkpoint (retained history)

The integration owner executed the following focused checks on the isolated
Mac validation tree. These frozen production sources all passed with exit code
zero and an empty compiler log:

| Module | SHA256 | Elapsed seconds |
|---|---|---:|
| RowwiseProbeSampling | `24f389bd6fe31c8c62758edf38e1badc3e3148851bac0b9d23d3ee54bd002c26` | 32.851 |
| SISCRowwiseProbeCalibration | `794aa7051f2457ba4c14fad0b2568563e8471aca0489267c223fcac10c64d1e8` | 7.502 |
| SISCRowwiseProbeWitness | `4524aad99685a7e50364ccea61468d96f55071d1060cb32b07a07e5a2773a5b0` | 10.061 |

The integrated `lake build UEOT` then passed in 22.749 seconds with the complete
678-module production source inventory. This is an actual local build result;
it is not a claim that a cloud proof job ran. The earlier interval-expression
parse failure and witness addition-order failure remain preserved as failed
attempts in their original source/log snapshots. The subsequent source hashes
above are the repaired, passed versions.

An independent source review binds these same three hashes and reports
`CLEAR_WITH_OUTER_MEASURE_BOUNDARY`; the boundary is stated in sections 2 and 3.
Native axiom/type export, canonical governance and publication acceptance are
separate integration gates. At this checkpoint their completion is not asserted
by this note; their actual receipts belong to the enclosing
`longterm_control_statistics_v1` integration package.

## 7. Final integrated proof acceptance

The three source hashes above are also included in the final accepted
678-module inventory `60cd5f8ab161c5b51394463c466947a4c6a6c1742ecdcd9c2bbfc41c0c06bd31`.
The actual final full build passed in 39.787 seconds. Both actual native
executions passed with identical complete JSON; the 12 added modules have
90 public registrations and 199 compiler-owned theorem constants (including
private/generated constants), all with standard axiom closure. Independent
source and actual-execution review is CLEAR. The separate full UMC audit
passed over 79 modules and 1,073 owned constants. These counts describe the
enclosing batch, not this three-module SISC subset. Canonical Git and release
status belongs to the [integration evidence](../longterm_control_statistics_v1/RESULTS_AND_BOUNDARIES.md#5-acceptance-evidence).
