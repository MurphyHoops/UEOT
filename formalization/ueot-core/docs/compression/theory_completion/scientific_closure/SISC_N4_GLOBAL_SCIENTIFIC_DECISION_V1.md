# UEOT SISC N4 — full-library statistical and scientific decision

Date: 2026-10-09 (Asia/Taipei). Local-only branch `research/sisc-local-20261008`, anchored to frozen main `f744194dabdbb8632e69b1d9cbc1f0e347877571`.

## Decision

**N4 finite conditional statistical theory: LOCALLY FORMALIZED AND REGRESSION-TESTED.**
**UEOT universal physical Objecthood / scientific final: HOLD.**
**External independent evidence: UNVERIFIED.**
**GitHub push: HOLD.**

No mutation of frozen 106/106 Core theorem sources or four governed Compression generators.

## 1. Source-aware reuse review — what was already proven

We checked the actual statements, not only filenames, across the first-party Lean library:

- `UEOT/V3/BoundedLossTwoSided.lean`: `measure_exists_candidate_bad_le` already proves two-sided Hoeffding + a finite union bound over an arbitrary finite index type. It needs IID validation samples under the same data law, measurable [0,1] losses and N>0. **No independence across test coordinates or candidates is required.**
- `FiniteCandidatePStat08.lean`: fixed finite-candidate ERM excess-risk bound and the confidence-radius formula. N4 reuses its underlying uniform two-sided supporting lemma rather than presenting Hoeffding as a new theorem.
- `InverseObjecthood/FiniteCandidateRecovery.lean`: exact ERM recovery from a true finite strict-risk gap. Distinct from the N3 abstaining certified/possible decision, whose power conditions are proved separately.
- `ScientificClosure/C2IntervalDecision.lean`: certified/rejected/ambiguous decisions under calibrated intervals. N4 does not reimplement that decision theory.
- `ScientificClosure/C2SamplingBudget.lean`: a **correlated-sampling arithmetic budget** that does NOT by itself establish a beta-mixing/blocked concentration theorem. N4 correctly stays in the IID lane.
- `StatisticalConsistency/Contract.lean`, `InverseObjecthood/HighProbabilityDiscovery.lean`: sample-size-varying confidence schedules and conditional object-class discovery. N4 adds a missing concrete statistical good-event bridge rather than claiming those conditional contracts were absent.
- `TheoryCompletion/AutopoiesisClosure.lean`: P12 **already contains conditional finite-lifecycle integration** connecting object discovery, a declared parent bridge, repair organization, lineage evolution, homeostasis, resource control and scale transport. Its causal parent bridge, repair programs and validity conditions are **inputs**, not inferred from passive observations. N4 does not duplicate P12.
- `CrossTrack/ParentBindingDiagnosticNoGo.lean`: a parent-binding forward Lipschitz margin need not identify its source parent. This blocks any inference that stable diagnostics automatically certify provenance.
- `Objecthood/StationaryCausalPathLawBridge.lean`: exact path-law equality for a declared deterministic stationary causal embedding, not candidate-parent recovery from arbitrary observations.

This review prevents two false statements: (a) that the repository lacks lifecycle theorems; (b) that those *conditional* lifecycle theorems prove physical causality and object identity have already been discovered endogenously.

## 2. N4-A: an explicit risk-matching statistical bridge

`SISCStatisticalCandidateCalibration.lean` constructs N3 C2 certificates from IID candidate-level empirical losses. The frozen two-sided Hoeffding theorem gives

`Pr[calibration failure] ≤ 2 |C| exp(-2N u²)`

provided each candidate's **expected sample loss exactly equals** the N3 model-defined risk. A false unique claim involving a competing truly compatible registered candidate is controlled by this bound.

Critically, `SampleLossMatchesRegisteredRisk` remains an **explicit model-match hypothesis**: empirical `E|Y-r|` does not estimate N3's `|EY-r|` without further conditions. This gap prompted a stronger N4-B theorem rather than being hidden.

## 3. N4-B: correct mean-first risk confidence without the false identity

`SISCMeanResponseCalibration.lean` estimates the actual *post-action coordinate mean* `hat m_j` before forming the risk estimate `Σ_j |hat m_j-R_c(j)|`. Its finite reverse-triangle theorem proves a Lipschitz bound on every candidate's L1 expected-response risk in terms of coordinate mean errors.

Assume `m=|O|` finite declared measurement coordinates, IID post-action microstate observations, measurable responses in [0,1], and the **independently required** law-match contract

`E_dataLaw[read(Y,j)] = Σ_y K(x,a,y) read(y,j)`.

The same simultaneous coordinate good event calibrates **all** registered candidate intervals with radius `r=m u`. The existing finite Hoeffding theorem then yields

`Pr[any candidate's C2 interval is uncalibrated] ≤ 2m exp(-2N u²)`.

This improvement does not depend on the number of candidate labels, because every candidate reuses the same estimated coordinate means. Cross-coordinate dependence inside the same sample is allowed; **temporal** IID observations are still required.

A separate machine-checked falsifying example proves `E|Y-1/2| != |EY-1/2|` in a uniformly random binary response model, preventing accidental return to the invalid loss formulation.

On the simultaneous calibration event N3 cannot (a) certify an incompatible unique label; (b) exclude another truly compatible registered causal candidate while claiming uniqueness; or (c) report uncovered while a truly compatible registered causal candidate exists. N4-B carries each unsound decision subset into the calibrated failure event, bounding all of these probabilities by `2m exp(-2N u²)`. These are **sample-dependent selector** statements: the selected candidate need not be fixed before the data, because a joint coordinate event controls all registered candidates.

## 4. N4-C: actual identification power requires separation margins

`SISCSeparationPower.lean` proves the missing complementary result. For a registered, causally admitted candidate `c` and a common certificate radius bound `r`:

`Risk(c)+2r ≤ tolerance`

and for all other registered causally admitted `d ≠ c`,

`tolerance+2r < Risk(d)`

imply, on the simultaneous calibration good event, that the **existing unmodified N3 resolver returns `unique(c)`**. The proof constructs the certified singleton possible set and excludes all rivals, rather than assuming the correct answer.

Specializing to the mean-first sample protocol (`r=|O|u`) gives

`Pr[resolver ≠ unique(c)] ≤ 2|O| exp(-2N u²)`.

This supplies **detection power** under explicit model separation, not just control of false labels. If risk gaps are too small, correct abstention may persist; the theorem does not promise universal recovery.

## 5. Independent exact-rational *software* tests

`evidence/sisc_n4_coordinate_calibration_method.py` exhaustively evaluates binomial counts under a fully specified synthetic transition model with Bernoulli p=1/3 and two observation coordinates `(Y,1-Y)`; these coordinates are dependent, but draws across time are IID.

For N=300 and u=0.1, it computes exact-rational probabilities over 301 possible counts:

- Hoeffding union bound: **0.0099150087**.
- Actual good-event and candidate-calibration failure probability: **0.00018389015**.
- Actual unsound unique-selection probability: **5.7460159×10^-20**.
- Actual false-uncovered probability: **6.9794583×10^-16**.

The rare incorrect decisions are actually exercised, not assumed impossible.

For a stricter certified-margin regime N=2000, u=0.05, the program verifies the N4-C margin conditions, exhausts 2001 counts and reports

- Hoeffding non-recovery upper bound: **0.00018159972**.
- Actual synthetic non-recovery probability: **1.0835929×10^-8**.

All probabilities were aggregated as `Fraction` rational sums, with decimal output for display. These are **synthetic mathematical method checks**, not observed real-world physical data and not independent proof review.

## 6. The remaining non-circular bridge to physical UEOT Objecthood

Even after these proofs, the full scientific claim remains conditional on:

1. **Correct microprocess identification.** `PostActionCoordinateLawMatchesKernel` is an explicit model validity input. An estimated kernel fitted on the *same* validation samples is not automatically covered by the fixed-model Hoeffding proof; held-out or adaptive-valid inference is needed.
2. **Causal provenance and candidate completeness.** The `causal` predicate and registry are independently specified, not inferred from transition statistics alone. N3 does not recover nature-wide unique physical parent identity.
3. **Observation sufficiency.** Means can alias different distributions and hidden histories; use full controlled trace/law tests, calibrated statistic families and causal interventions where scientifically required.
4. **Dependent data.** The existing correlated-budget arithmetic requires a real mixing/martingale concentration theorem. It is **not** an IID substitute.
5. **Physical objecthood.** P12 already proves a conditional lifecycle theorem, but its parent/repair/organization/viability bridge inputs must be established from independent mechanisms and measurements. No new theorem derives GOD, GOA or SameObject from N4 confidence alone.
6. **Computability and measurability.** The finite resolver includes a noncomputable real comparison/choice specification. The present upper bounds use Mathlib's measure-real monotonicity; a deployed finite algorithm and measurable decision map require their own executable/semantic certificate.

Next scientific priority: build a **provenance-grounded causal certificate** from interventional path data, and connect its verified relation to the already established P12 parent bridge. In parallel, derive and verify genuinely dependent-sample statistical bounds, then extend beyond expectation-vector observations.

## 7. Governance and audit

V6 source digest inventory reads/hashes **591** first-party Lean files, **105,933** source lines and **3,570** lexical theorem/lemma declarations; **589** files are publicly UEOT-root-reachable and two are independent Lake/audit entrypoints. It checks unchanged V1–V5 source digests, permitting only additive import changes at the known ScientificClosure root.

The exact-head local gate checks full `lake build UEOT`, selected N4 theorem `#print axioms` surfaces, source proof-escape scanners, frozen historic manifests, original C7 evidence/adversarial mutation tests, all longstanding Compression and Finalization governance tests, and the new exact-rational statistical method test.

No cloud push, PR or managed Core theorem-count revision.

**Disposition:** `LOCAL_FORMAL_PASS` only when final exact-head gate returns zero; `SISC_SCIENTIFIC_FINAL=HOLD`, `real_world_support=UNVERIFIED`, `independent_review=REVIEW_PENDING`, `CLOUD_PUSH=HOLD`.
