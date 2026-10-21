# SISC rowwise experiment: independent mathematical and source review

Reviewer: `/root/infinite_policy`.

Decision for the source identities below: **CLEAR, with the explicitly
documented outer-measure API boundary in section 8**. No blocking mathematical
or source-identity error was found. This is an independent static review; the
reviewer did not execute Lean, inspect a native export, or certify a full build.
Those execution gates remain separate root-owned evidence. Final source freeze
confirmation is pending the root's final hash set.

## 1. Exact inputs

| Candidate source | SHA256 |
|---|---|
| `UnifiedClosure/RowwiseProbeSampling.lean` | `24f389bd6fe31c8c62758edf38e1badc3e3148851bac0b9d23d3ee54bd002c26` |
| `UnifiedClosure/SISCRowwiseProbeCalibration.lean` | `794aa7051f2457ba4c14fad0b2568563e8471aca0489267c223fcac10c64d1e8` |
| `UnifiedClosure/SISCRowwiseProbeWitness.lean` | `4524aad99685a7e50364ccea61468d96f55071d1060cb32b07a07e5a2773a5b0` |

Paths are relative to `UEOT/V3/Compression/TheoryCompletion/`. Exact byte
snapshots of these three candidates accompany this review. `SOURCE_INPUTS.json`
also records the exact hashes of seven inspected dependencies, including the
two-sided Hoeffding theorem, the sigma-indexed product law, the unchanged N3
resolver and margin theorem, the L1 response-risk inequality, and the N6 audit
and response-gap definitions. This review does not treat a theorem's name or a
previous chat as a substitute for those source types and proofs.

## 2. The actual common Good event and scalar concentration

`coordinateGood` uses the empirical mean of the registered outcome in each
actual row and the population mean of that row's declared PMF:

\[
G=\left\{\omega:\forall j,
\left|\widehat m_j(\omega)-m_j\right|\le u\right\}.
\]

The definition is independent of a candidate label. The separate theorem
`coordinateGood_measurable` proves its measurability from the measurable
outcome and sample maps and finite `J`; it does not take the measurability of
Good as an unproved field.

`measure_coordinateGood_compl_le` applies the existing scalar
`BoundedLossTwoSided.measure_empiricalRisk_bad_le` within each row and then a
finite union bound over `j`. Its source assumptions are explicit:

- `N : J → ℕ` is a fixed input, and every `N j` is positive;
- outcomes take values in `[0,1]` and are measurable;
- samples within each row are independent under the same `μ`;
- every sample coordinate has the exact marginal `(row j).toMeasure`;
- `μ` is a probability measure, `J` is finite and `u ≥ 0`.

The resulting bound is exactly

\[
\mu(G^c)\le
\min\left(1,\sum_j 2\exp(-2N_j u^2)\right).
\]

Cross-row independence is not used by this general theorem. The construction
does not allow an outcome-dependent allocation, optional stopping, unknown
drift, or an arbitrary correlated single trajectory to satisfy these
premises automatically. This is a scalar-mean budget, not a PMF total-variation
budget; the state-subset multiplier from existing TV calibration is correctly
absent.

## 3. L1 risk radius and identity with the same N3 kernel

`rowwiseCoordinateRisk` first estimates each coordinate mean and then sums its
absolute difference from `P.prediction c j`. It does not confuse
`E |Y-r|` with `|E Y-r|`.

On the single Good event, the reused inequality
`finite_absolute_response_risk_lipschitz` proves

\[
\left|\widehat R(c)-R(c)\right|
\le\sum_j|\widehat m_j-m_j|
\le |J|u.
\]

The interval constructor therefore uses statistical radius
`(Fintype.card J : ℝ) * u` and zero drift radius. Its implementation is a
structure update changing only `interval`. It preserves the original kernel,
source state, action, readout, prediction table, registered candidate set,
causal predicate, tolerance and nonempty-observation field.

The independently stated condition `RowwiseCoordinateLawMatchesKernel` binds
each actual population mean to the same
`P.kernel.mass P.source P.action` and `P.read`. The proof
`rowwise_population_risk_eq_registered` derives the final L1 risk identity by
substituting these coordinate equalities. The final risk equation is not simply
assumed as an input.

This matching condition is precisely a coordinate-mean condition. It is enough
for this registered readout risk, but it is not an identity of the entire row
PMFs and does not establish unobserved response laws, counterfactual joint laws,
or physical fidelity. Concentration about a data law's own mean cannot discharge
it. The explicit negative control in section 7 confirms this boundary.

## 4. Candidate selection and identification margins

The interval constructor takes `P`, samples, an observed record, `u` and its
nonnegativity proof. It does not take a known true candidate. The unchanged
`resolveRegisteredCandidates` selects only from the interval-based registered
possible set, requiring a unique possible candidate with a certification
interval before outputting `.unique c`.

The true label `c` appears only in the correctness theorem, with explicit
registration, causal admission and separation margins:

\[
R(c)+2|J|u\le\tau,
\qquad
\tau+2|J|u<R(d)
\]

for every other registered causal `d`. These are the existing N4 two-radius
margins, applied to the actual newly constructed interval; there is no new
oracle-selected winner.

Because the coordinate inequality holds for every candidate on the same Good
event, the proof correctly has no extra union bound over candidate labels. The
ambient candidate type need not be finite; the resolver still receives its
finite registered set. The existing N3 nonempty-observation condition is
preserved in the protocol, while `empty_probe_boundary` correctly restricts
its empty-index conclusion to pure scalar calibration.

## 5. N6 audit: full-type gap and independent source evidence

`rowwiseInterventionAudit` replaces observed responses by actual rowwise means
and sets the comparison tolerance to `u`. Neither this constructor nor
`auditedSourceCandidates` takes the true parent as an algorithm input.

The N6 correctness theorem explicitly retains:

- membership of the claimed parent in the registered set;
- an external `authenticatedTransfer parent child` premise;
- equality of every actual population mean with that parent's registered
  `referenceResponse`;
- `LocalResponseGap referenceResponse u parent`.

The inspected `LocalResponseGap` definition quantifies over **every other
parent in the full parent type**, requiring a coordinate gap greater than
`2*u`. The new adapter preserves that stronger quantifier and does not silently
restrict it to the registered or transfer-attested subset.

The constructor fills the same empirical response function for all children,
but the theorem applies only to the particular child for which model matching
and transfer evidence are supplied. Its source comment explicitly retains
this boundary; no joint experiment for different children is derived. Fitting
does not create authentication or a genealogical relation. Positive
genealogical interpretation remains an external bridge.

Both N3 and N6 failure sets are proved subsets of the same corresponding Good
complement, so each bound spends that scalar budget once.

## 6. Nonempty, unequal-allocation product experiment

The concrete witness uses `Bool` probes, with allocations `128` and `256`,
so the index set is genuinely nonempty and the sample counts genuinely differ.
The sample space is the existing
`(Σ j, Fin (allocation j)) → Bool`; `trainingLaw` is the actual
`productRowLaw row allocation`, with each row equal to `PMF.pure false`.

The witness obtains sample measurability, actual marginal laws and within-row
independence from the existing product-law theorems. This is an actual finite
probability-space instantiation, not a bare list of independent-sampling
assumptions. The product experiment has independent rows as an additional
property, although the general theorem does not require that property.

The source's post-action kernel is the same point mass at `false`, with the
two candidates predicting coordinate values `0` and `1`. The formal source
computes their registered L1 risks as `0` and `2`. At `u=1/8`, the L1 radius is
`2*(1/8)=1/4`; tolerance `1/2` satisfies the required inside and outside
margins. N3 and N6 both consume this concrete experiment.

The exact scalar budget is

\[
2e^{-4}+2e^{-8}.
\]

The new nonvacuity lemma bounds it by `28/45 < 1` using `e^4 ≥ 5` and
`e^8 ≥ 9`; this is a conservative exact analytic bound, not a decimal estimate.
The algebra and inequality directions are sound in the inspected proof.
Successful Lean execution of that latest witness is still a separate gate.

The two coordinate groups are separate experimental units. They do not claim
joint potential outcomes for one unit under incompatible interventions. The
example is a formal point-mass model, not empirical validation or a noisy-data
performance measurement.

## 7. Concrete δ₀/δ₁ model-mismatch negative control

The negative control retains actual data rows `δ_false` while replacing the
declared post-action source kernel by `δ_true`. The source derives failure of
`RowwiseCoordinateLawMatchesKernel`: the data mean is `0`, while the declared
kernel/read mean is `1`.

It then goes beyond reporting a missing premise. For the all-false record,
all empirical means are exactly `0`, so `zero_record_is_actual_good` proves
membership in the actual data Good event at radius zero. Nevertheless,
`exact_data_good_does_not_calibrate_wrong_kernel` proves that the constructed
zero-radius interval fails calibration for the wrong kernel. Candidate
`false` has empirical mismatch `0` but declared kernel-derived L1 risk `2`.

This is an actual failed conclusion under exact data-mean concentration. It
demonstrates why statistical accuracy and model/source matching are distinct
responsibilities.

## 8. Documented API boundary: outer measure versus exported measurability

The common Good event has an explicit measurability theorem. The two decision
failure endpoints currently return bounds on `μ.real {ω | failure ω}` using
set inclusion and `measureReal_mono`. They do not separately export a
`MeasurableSet` certificate for each resolver/audit failure set, or a measurable
resolver theorem.

Those bounds are valid as outer-measure bounds on the displayed sets. This is
not a mathematical blocker and does not weaken their use as upper bounds.
The finite registered filters and measurable empirical means also give a
mathematical route to an explicit failure-event measurability theorem, but that
additional Lean API is not supplied by these three source files. Reports must
preserve this distinction rather than claiming a separately formalized
resolver-measurability certificate.

The SISC author acknowledged this boundary and agreed to preserve it in the
source-level explanation. No source changes were made by this reviewer.

## 9. Review result and exact limits

**No blocking mathematical or source-identity defect found for the recorded
hashes.** The main guarantees are conditional calibration, identification and
audit bounds for the explicit experiments and model/transfer premises. They
do not establish random-stopping validity, generic trajectory dependence,
independent source authentication, general empirical success, unique physical
genealogy, or global UEOT scientific closure.

This artifact is source review evidence only. It must be rebound to the final
frozen source hashes after any source edit; compiler PASS, native axiom/type
reuse, full-library build, review of the final integrated commit and
resulting-main acceptance remain distinct records.
