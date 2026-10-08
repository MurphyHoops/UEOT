# UEOT SISC N3 — whole-library reconciliation, core theorem and local decision

Date: 2026-10-09 (Asia/Taipei). Branch: `research/sisc-local-20261008`. The canonical frozen Core v3, its 106/106 governed theorems, and the four counted Compression generators remain intact. This stage is **local research and exact kernel verification**, not external empirical validation.

## A. What we found already proved — no duplicate mathematics

The existing repository already contains the mathematical building blocks needed for N3:

1. `InverseObjecthood/FiniteCandidateRecovery.lean` proves a positive finite strict-risk gap and unique ERM candidate recovery under the correct uniform-error event. N3 *does not* replace this result or call any externally preselected minimizer a derived successor.
2. `InverseObjecthood/Identifiability.lean` rigorously separates evidence equality, valid candidate equality, and scientific object equivalence. N3 reuses its exact `ObjectClassIdentifiedByEvidenceAmongValid` predicate with the appropriate equality Setoid, without upgrading the conclusion to full physical identity.
3. `InverseObjecthood/NonIdentifiabilityBoundaries.lean` contains independent ambiguity/no-go witnesses, so there is no scientific justification to force a unique candidate when evidence is nonseparating.
4. `ScientificClosure/C2IntervalDecision.lean` already proves sound scalar interval decisions `certified`, `rejected`, `ambiguous`. The new resolver **calls this implementation** for every candidate rather than reimplementing interval logic.
5. `ScientificClosure/C3NestedSearch.lean` finds the first good member of a nested registered candidate chain; it has no universal causal successor discovery and is not misrepresented as one.
6. `SISCFiniteStochasticQuotient.lean`, `SISCStochasticPredictiveIntertwining.lean`, and `SISCEmissionTiming.lean` supply finite stochastic K, belief recurrence, and explicitly typed measurement time order. The N3 candidate mismatch measures **post-action** response, consistent with the existing P-REF-02 post-transition observation interface.

This reuse audit is especially important: a theorem can be Lean-valid and scientifically redundant; N3 advances by composing existing interfaces and proving the missing decision/identification contract, not by relabeling P4 risk recovery.

## B. Main new result: causal candidate recovery without a supplied transporter

Inputs: source microstate x, declared action a, normalized finite controlled stochastic kernel K, observed state-response vectors r(y,j), a finite registered candidate set C, predicted candidate response vectors R_c(j), an independently registered `causal(parent,c)` admissibility predicate, and a C2 interval per candidate with statistical and drift radii.

Define the model ground risk

`risk(c) = Σ_j | Σ_y K(x,a,y) r(y,j) - R_c(j) |`.

The registered protocol requires at least one observation coordinate. It does **not** assume or construct a parent transporter `tp`.

A simultaneous calibration event is stated **separately**:

`∀ c∈registered, |estimate_c - risk(c)| ≤ statisticalRadius_c+driftRadius_c`.

This is a scientific measurement/statistics obligation, not free information from Lean or K.

Define

`possible = {c∈registered | causal(c) ∧ C2(c) ≠ rejected}`

`certified = {c∈registered | causal(c) ∧ C2(c) = certified}`.

The resolver returns **unique(c)** if and only if possible is exactly {c} AND c has a certified C2 result. If no potential candidate remains, it returns **uncovered**. All other cases return **ambiguous**, including one certified candidate accompanied by another unresolved candidate, or a single statistically unresolved candidate.

Under the simultaneous good event, Lean proves:

- `unique_resolution_sound`: the resolved candidate is causally admitted, registered, truly model-compatible, and unique among **truly model-compatible registered causal candidates**.
- `uncovered_excludes_registered_truth`: the uncovered outcome excludes only true compatible candidates in this registered family. It does not prove any actual object's death.
- `two_compatible_force_nonunique`: two truly compatible candidates preclude a unique decision.
- `two_possible_candidates_force_ambiguity`: even two merely *possible* candidate tokens force abstention.
- `undecided_singleton_force_ambiguity`: one not-yet-certified candidate does not suffice for unique identity.
- `registered_candidate_risk_nonnegative`: the model risk is a genuine finite sum of response deviations.
- `unique_candidate_recovers_inverse_objecthood_valid_class`: an exact bridge to P4's existing valid-candidate identification schema, not ontic identity.
- `wrong_unique_implies_calibration_failure`: a wrong unique output with another genuinely compatible registered candidate would contradict simultaneous interval calibration.

Proofs are in `SISCRegisteredCausalCandidates.lean`. They have no `sorry`, no extra axioms and no hidden `tp`.

## C. Three independently fully specified Lean toy examples

`SISCRegisteredCandidateExamples.lean` builds a normalized one-state controlled kernel, two Boolean registered candidate tokens, a nonempty observation coordinate and explicit C2 intervals. It proves the simultaneous calibration condition in **all three** example systems:

1. **Unique** — false candidate is exactly response-compatible, true candidate's response differs by 3 at tolerance 1: result `unique(false)`.
2. **Ambiguous** — false is certified but the true candidate has a conservative interval crossing tolerance: result `ambiguous`. Choosing false would be an unsafe overclaim.
3. **Uncovered** — both registered candidates have exact true mismatch 3 above tolerance 1: result `uncovered`. This is **model noncoverage**, not physical nonexistence.

The constructors and all outcomes are Lean-checked, not an illustrative untested pseudo-implementation.

## D. Relation to the unified UEOT mathematical backbone

The full established chain is now:

`controlled stochastic process → (declared observation interface) → prediction/belief dynamics → risk and calibrated intervals over *registered causal candidates* → evidence-limited operational successor decision`.

The new part removes a **chosen successor transporter** from the *finite search algorithm*. It does **not** derive the causal evidence predicate, completeness of candidate registry, probability concentration, persistence, repair or same-object semantics from the world dynamics. The risk is a finite expectation-vector mismatch; if the experiment requires full distributional response, richer interventions/tests and the existing observable-spanning / statistical machinery must be used.

The `SameObject` and GOD/GOA questions remain separately typed, with independent evidence gates.

## E. Most urgent scientific strengthening

**N4.1 Probabilistic calibration:** reuse the existing P-STAT uniform confidence/finite class bounds to prove that the deterministic `Calibrated` good event occurs with certified probability under valid sampling assumptions; explicitly distinguish correlated data and drift.

**N4.2 Causal ancestry:** replace the externally registered causal predicate by a certified provenance relation from interventions and transport traces, or show no-go for indistinguishable histories.

**N4.3 Intervention response completeness:** lift expected responses to distributions/full future controlled traces. Use the prior finite-test spanning and stochastic lumpability results; explicitly return unresolved when probes cannot distinguish causal alternatives.

**N4.4 Time/branching:** model a graph of admissible successors and independently measured births/splits/merges rather than forcing unique token ancestry for naturally branching systems.

**N4.5 Physical formation/persistence:** only after a credible causal edge, candidate register and formation evidence, attempt quantitative long-time viability/repair proofs. A persistent mathematical response vector is not itself an autopoietic object.

## F. Reproducibility and custody

The V5 inventory records **588 first-party Lean files**, **105,243 lines**, **3,554 lexical theorem/lemma declarations**, of which **586 modules** are reachable through the public root. It retains all V1–V4 source hash proofs and checks, permitting only additive ScientificClosure root imports.

A fully green local gate establishes a *conditional formal artifact*, **not** external peer review, physical validation, coverage outside declared candidates or a scientific-final truth claim. Do not push to GitHub until the full user-authorized local scientific program satisfies its further evidence gates.

Decision: `LOCAL_FORMAL_PASS` only upon exact-head audit; `SISC_SCIENTIFIC_FINAL=HOLD`; `real_world_support=UNVERIFIED`; `independent_review=REVIEW_PENDING`; `CLOUD_PUSH=HOLD`.
