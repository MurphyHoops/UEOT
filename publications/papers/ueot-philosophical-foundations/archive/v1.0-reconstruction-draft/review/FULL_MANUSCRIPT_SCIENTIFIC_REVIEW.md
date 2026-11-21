# Full-manuscript scientific and formal review — round 1

**Reviewer:** native agent B, `formal_audit`; separate from the coordinating manuscript author.  
**Reviewed manuscript:** `/workspace/scratch/1e756a672d37/draft-review/manuscript-round1.md`, complete file, lines 1–318.  
**Manuscript SHA-256:** `c563076ada008c7417cd8f8e7720a2133b94144fddf492cbfae3686c823c8ec3`.  
**Reviewed bibliography:** `publications/papers/ueot-philosophical-foundations/references.bib`.  
**Bibliography SHA-256:** `7f5c6a83f8b75e9ff4c9c77987aac92e5989160acbde2ee48e5210247b6a2692`.  
**Scientific reference snapshot:** `MurphyHoops/UEOT@3d443ec29eb17af1fc00699a74e2d42d73516d81`.  
**Date:** 2026-11-11.

## 1. Verdict

**Bounded revisions required. No displayed mathematical classification or numerical example needs withdrawal.** The paper is substantially more careful than the strong original programme. It consistently distinguishes a model-internal result from empirical confirmation, predictive types from numerical bearers, expected population from individual retention, and an optimal external policy from an inherited programme. Its central preservation argument is presented as an elementary constraint on explanation, not a new Lean theorem or a proof of metaphysical realism.

The main scientific scope problem is the presentation of the finite-cohort selection result immediately after the enlarged growth domain without restating its narrower, unchanged `Valid` contract. Several further sentences need precise alignment with their supporting endpoint: the raw execution-gate example, projection of the silent tag, the constant in the uniform growth bound, and the source-specific rank-three example. The state-space homology example should also be confined to the exact inference it refutes; agent A is separately checking the original paper's alternative reference to an interaction network.

These are local repairs to the argument's scientific support. They do not establish that the philosophical position is novel, empirically confirmed, or accepted by external reviewers.

## 2. What was actually checked

I read the entire frozen manuscript, including its abstract, tables, equations, conclusion, disclosure and licence paragraphs, and the complete supplied bibliography. Every mathematical use was compared with F01–F27 in `FORMAL_CLAIM_EVIDENCE_MATRIX.md`. The current source statements and proof bodies had been read in the first audit; the present review additionally re-read the exact growth least-bound proof, selection event and quantifier definitions, raw execution/request/repair definitions, the boundary consumer and both written numerical examples.

The five growth-source hashes previously matched against the archived actual Lean receipt remain the basis for reusing that compilation evidence. **No Lean invocation, new theorem, simulation, new experimental result or edit to the manuscript/scientific source was made in this review.** External philosophical literature and the historical original's full interpretation remain the responsibility of agents C and A respectively; this report does not claim an independent DOI or full primary-literature audit.

Line references below identify the frozen Markdown version, not an unspecified later draft.

## 3. Required and recommended revisions

### B-S01 — Major scope clarification: the selection theorem has the older domain

**Location:** §5.3, line 219; F18–F19.

The paragraph follows a discussion explicitly based on the enlarged `ProbabilityValid` domain. Its phrase “Its cohort comparison chooses a finite horizon and then sufficiently many independently funded founders” does not tell the reader that the reviewed feedback theorem still assumes the old `Valid` domain. The paper must not imply that PR447 enlarged the selection theorem together with the growth theorem. In addition, independence is a property of the complete cohort noise laws; separate funding alone does not give the statistical premise.

`CoreRegenerativeFeedback.exists_finite_cohort_selection` assumes `Valid p`, `0 < ε ≤ 1` and `η > 0`. It chooses a positive finite horizon before a positive finite number of independent cohorts. A cohort has one healthy founder of each of the two programmes. Its good event requires a positive total and a high-programme share at least `1−ε`; extinction remains failure. The original `Valid` domain adds `γ>δ` and `s+b>1` to the strict probability domain used by the growth classification.

**Suggested replacement for the cohort sentences:**

> In the narrower original positive regime—adding \(\gamma>\delta\) and \(s+b>1\) to the probability conditions above—the feedback theorem chooses a finite horizon and then a finite number of independent cohorts, each beginning with one healthy founder of each programme and supported by its own continuing resource account. For specified error tolerances it makes the high-programme share at that census close to one with high probability, while counting extinction as failure. It does not establish almost-sure selection over unlimited time in one fixed finite population.

If numerical quantifiers are wanted, state: for every `0<ε≤1` and `η>0`, there exist finite positive `T,n` such that the good event has probability at least `1−η`. Do not reverse the choice of `T` and `n`, or turn this into a uniform-in-time result for one fixed finite population.

### B-S02 — Moderate endpoint precision: distinguish raw execution from request selection

**Location:** §4.2, line 135; related wording at lines 103 and 303; F08.

“Two bodies with the same decoded instruction but different gate states can select different primitive actions” does not describe the cited F08 endpoint precisely. `CoreRegenerativeQuotient.code_only_prediction_loses_execution` compares the same decoded code and a fixed original diagnosis. The gate-open body's `rawExecute` is `some .bloom`; the gate-closed body's is `none`.

There is an important qualification to the criticism: the sentence is **not simply false in the entire source**. The `diagnostic` definition itself reads the gate, and `requestOf` chooses a row using that diagnosis; a gate change can consequently alter the requested action. `programStep` then pays, restores, and executes the selected row. These are different operations. The current paragraph does not identify which it means.

**Preferred replacement tied directly to the already cited theorem:**

> Two bodies can have the same decoded instruction while differing in whether that instruction can execute before restoration: the open gate permits the primitive execution, whereas the closed gate returns no executable action. Code identity alone therefore does not preserve the execution conditions.

This avoids inventing a new dedicated theorem and preserves the paper's intended inference. Keep the distinction from complete predictive equivalence under all protocols; the manuscript already does this correctly.

### B-S03 — Moderate quantifier precision: fix the initial population before choosing the common constant

**Location:** §5.2, lines 184–190; F14.

The least-rate formula and proof interpretation are correct. The text should explicitly scope the constant `C`. It may depend on the source parameters and the fixed initial population; it is common to all allowed policies and all census times. It cannot be one finite constant uniform over arbitrary initial population sizes, since the time-zero population is unbounded over that class.

The exact definition is `UniformExpectedUpper p initial rho := 0 < rho ∧ ∃ C, ∀ K n, E[N_n] ≤ C*rho^n`. The initial state is outside the existential quantifier. The least-base result additionally requires that initial population to be nonempty.

**Suggested start of line 190:**

> For each fixed parameter choice and fixed nonempty finite canonical initial population, there is a constant \(C\), independent of the permitted policy and census time, such that …

The rest of the paragraph correctly retains all finite horizons, two-sided positive bounds for an attaining policy, no assumed growth limit for every competitor, and the written status of root-limit consequences.

### B-S04 — Moderate source precision: tag erasure is a commuting projection

**Location:** §3.3, line 103; F09.

The underlying positive example is sound, including preservation of marked history. I read the finite-history proof, not merely the file's prose. `eraseMember_keeps_identity` preserves identity, parent, birth time, age and ancestry. `populationExpectation_eraseState` transports the complete finite-horizon law. `attainable_test_values_eraseState` retains the same allowed policy class in both directions. Public-history test values are preserved by `public_history_test_expectation_eq`.

However, “audit tag” obscures that the erased coordinate is a **causally silent physical tag**, distinct from the protected audit identity and ancestry fields. Raw bodies and returned body slots still carry the tag before projection. The result is not literal equality of every raw record.

**Suggested replacement for the first two sentences:**

> A causally silent physical tag can be projected out while preserving the public transaction records, payments, marked histories and available public-history policies. The source proves that its actual transitions commute with that projection at every finite horizon.

The following contrast with erasing diagnosis is supported: healthy bloom is affordable and damaged bloom is not under the same six-unit account.

### B-S05 — Moderate scope and citation precision: identify the rank-three response task

**Location:** §2.2, line 51; F24 and F26.

The formula is right, but the sentence introduces `s,b,q` before their later definitions and says that the response map “has determinant.” It is its **Jacobian** that has determinant `b`. The record does not show an arbitrary physical three-parameter experiment or a universal impossibility of two-dimensional representation. It fixes the healthy `θ0` care programme, holds `δ,γ` fixed, varies `(s,b,q)` in a legal open parameter neighborhood, and records retention, birth, and the joint event of birth with damaged output.

**Suggested replacement, or equivalent short footnote:**

> For the healthy \(\theta_0\) care programme in Section 5, the public probabilities of retention, birth, and birth with a damaged output are \((s,b,bq)\). Holding \(\delta,\gamma\) fixed, their Jacobian with respect to \((s,b,q)\) has determinant \(b>0\) on the legal open domain. These responses therefore cannot all factor there through one common smooth two-dimensional intermediate representation [@qianMathematics2026, §23.4].

Retain the existing caveat concerning nonsmooth/discrete encodings. Add, if space permits, that parameter variation is a model-internal possibility, not demonstrated independent manipulability in nature. The disclosure at line 309 correctly calls this written mathematics with exact checks, not a dedicated new Lean endpoint.

### B-S06 — Historical-to-mathematical scope check: the contraction example concerns the specified state space

**Location:** §2.2, line 43; F03–F04.

The contraction example is mathematically correct. What it directly refutes is an inference from stable persistence to nontrivial first homology **of the chosen dynamical state space**. A graph representation can have different topology from that state space. No source theorem identifies those topologies. Agent A reports that the original claim also names an interaction-network alternative; that original-text question must be resolved before claiming that this one example defeats every version of the original topological disjunction.

**Safe replacement for “The counterexample defeats the universal topological necessity”:**

> The example defeats an unrestricted inference from stable persistence to nontrivial first homology of the dynamical state space. Any further claim about an interaction network needs its own representation and argument.

Keep the existing statement that the example neither refutes biological organization nor makes feedback irrelevant.

### B-S07 — Minor but useful specification: birth counts include all current parents, and no retained slots

**Location:** §3.2, lines 79 and 89; F10.

The table is correct, including the warning that `(B1,R1)` has only three classes. To prevent a reader from interpreting `B_t` as births only from the original founder, replace “excluding the retained original individual” with a definition applying to the whole population:

> Let \(B_t\) count all strict newborn slots produced by the actual population at census \(t\), excluding every retained slot; a newborn first executes at the following census.

The second-period values are otherwise easy to misread, because they include births produced by every first-period successor. Also replace the domain phrase “including …” with the explicit “the probability conditions of Section 5 together with \(\gamma>\delta\) and \(s+b>1\).” This preserves the exact source domain without adding new assumptions.

### B-S08 — Minor source-law clarification: resampling is not prohibited as an algorithm

**Location:** §3.1, line 71; F02.

The reviewed source construction keeps the same latent source across its joint past/future law. A mathematically correct posterior-resampling algorithm can nevertheless reproduce that conditional law. The philosophical obligation is a correct common joint source, not a prohibition on all computational resampling.

**Suggested change:** replace “rather than from a conveniently resampled hidden state” with “rather than from an independently substituted hidden state that changes the conditional joint law.” No adaptive-protocol or pointwise-null-history overclaim otherwise appears in this paragraph.

### B-S09 — Moderate traceability repair: route broad citations to exact contracts

**Locations:** lines 51, 53, 69–71, 103, 121, 127–139, 153, 219 and 253; bibliography keys `ueotSource2026`, `qianMathematics2026`, `ueotStatus2026`.

The immutable snapshot and accompanying matrix make the analysis reproducible in principle. I found no fabricated numerical claim or missing scientific source. Several citations nonetheless point only to the whole book or the `core_theory_closure_v1` directory, while the relevant Lean module lies outside that directory. A standalone paper reader cannot readily identify the exact theorem from that citation alone.

Use section locators and short notes pointing to the matching supplement IDs. In particular:

| Manuscript use | Sufficient precise route |
|---|---|
| Canonical a.e. minimality | Mathematics §§4.1–4.3; F01; `PredictionDependent.canonical_ae_minimal` |
| Common-source conditional future | F02; `MeasurablePredictiveCanonicalSource.actual_past_future_factorization` and `.actual_response_ae_minimal` |
| Operational Ω | Mathematics §12.2; F05; `OmegaMinimalFailure.p_omg_01` |
| Execution and tag quotient | F08–F09; exact endpoints listed under B-S02 and B-S04 |
| Paid recovery and its boundaries | F11–F12; `CoreRegenerativeSource` and `CoreRegenerativeRepair` |
| Purpose nonidentification | Mathematics §18.3, N-TEL-01; F21; `PurposeIdentifiability` with its unrestricted-product caveat |
| Selection | F18–F19; `CoreRegenerativeFeedback.exists_finite_cohort_selection` and the separate boundary file |
| Rank-three example | Mathematics §23.4; F26; explicit written/non-dedicated-Lean status |
| Present physics scope | Direct immutable link to `physics/qm/status/CURRENT.json` and the physics book opening; F27 |

`ueotStatus2026` currently links to `core/status/CURRENT.md`. That file supports the Core closure/empirical distinction but is not the direct physics-status record. Its BibTeX note mentions physics, which does not make the linked Core file itself evidence for the physics state. Add a dedicated physics-status entry or an explicit exact path in the source note. The manuscript's bounded physics sentence is true; this is an attribution repair, not a demand to expand the paper into a physics survey.

## 4. Complete F01–F27 coverage disposition

| ID | Manuscript location | Review result |
|---|---|---|
| F01 | §3.1, 63–75 | Accurate common-reference a.e. minimality; add a precise source locator. No unique ontology inferred. |
| F02 | §3.1, 71 | Accurate restricted source connection; B-S08 avoids overreading “resampling.” No arbitrary adaptive protocol claim. |
| F03 | §2.2, 43 | No unsupported attraction or repair conclusion. State-space/network scope remains B-S06. |
| F04 | §2.2, 43 | Contraction counterexample is correct; restrict exact target as above. |
| F05 | §4.1, 121 | Correct fixed certificate/horizon, finite deletion and monotonicity qualifications. |
| F06 | §4.1, 121–123 | Correctly confines empty destructive families to declared interventions. |
| F07 | §4.1, 123 | Correct separation of access loss and physical failure. No unsupported uniqueness claim. |
| F08 | §3.3, 103; §4.2, 135 | Philosophical inference sound; distinguish raw execution, request and repaired execution in B-S02. |
| F09 | §3.3, 103 | Full marked/public-history preservation genuinely supported; state projection precisely in B-S04. |
| F10 | §3.2, 79–93 | Exact 2/3/4 classes, correct joint task and `(B1,R1)` warning; improve population-wide birth definition and domain route. |
| F11 | §4.2, 127–131 | Correct six-unit budget, three-unit damage repair, paid care, two-output reserve, trusted bootstrap/backups and actual cell execution. |
| F12 | §4.2, 133 | Correct specified-kernel and information-erasure boundaries; no claim excluding all future supply or alternative recovery. |
| F13 | §5.2, 163–182 | Correct mechanism-derived means and retained/newborn distinction. |
| F14 | §5.2, 184–190 | Correct least positive base and all-finite-time interpretation; B-S03 fixes initial-state scope of C. |
| F15 | §5.2, 192–201 | Both iff conditions and equality cases are right; own damaged founders retained. |
| F16 | §5.2, 201–205; §6.1, 237–241 | Internal programme realization is not conflated with an arbitrary external request policy. |
| F17 | §5.3, 209 | Correct individual retention cost versus birth gain. No infinite-lineage-survival optimization claimed. |
| F18 | §5.3, 219 | Requires B-S01: older domain, statistical independence, cohort composition and extinction treatment. |
| F19 | §5.3, 219 | Qualitative positive-probability loss event correct. The paper sensibly avoids extra exact-ratio details. |
| F20 | §4.3, 139–147 | Correct retained/newborn identity convention and its interpretive limits. Full weighted many-to-one theorem is not invoked; no uniform-living-sampling claim is made. |
| F21 | §5.1, 153–159 | Strongly and correctly qualified; product construction is not misused against mechanism-grounded function. |
| F22 | §2.2, 53 | Set-valued/tied optimality correctly allowed. |
| F23 | §2.2, 53 | Long-run mathematical types correctly separated; no unsupported mixing or uniqueness claim. |
| F24 | §2.2, 45–51 | Gauge identity correct; source-specific rank connection needs B-S05. |
| F25 | §1, 23; §§5.1, 5.4 | No forced scalar utility claimed. Dedicated incomparability theorem is not invoked and need not be added. |
| F26 | §2.2, 51; disclosure 309 | Correct written-result status; exact task, fixed parameters and Jacobian should be supplied. |
| F27 | §6.2, 253; disclosure 309–313 | Accurate no-new-build/no-experiment/internal-review distinctions. Improve direct physics citation. Final past-tense review disclosure is appropriate only after all three actual reviews are delivered. |

## 5. Numeric and event-semantic audit

The following checks use the displayed source formulas and existing records, not a new simulation or Lean run.

1. **Second census births:** at `(s,δ,b,γ,q)=(3/4,1/8,3/8,1/4,1/3)`, the source gives `Eθ0D B2=(s+b)b=27/64` and `Eθ1D B2=(s+b)[b+(1−q)γ]=39/64`. The difference is `3/16`. These are new births across the actual second-census population, not total population and not only founder-produced births.
2. **Repair distinction:** `R1` is deterministic zero versus three for the two `θ0` starts. Their first caps are three versus six, both affordable under the same six-unit rule. Their complete finite joint birth records can be coupled; their repair fees and some ancestry source-kind records differ. The draft correctly uses this as a loss of task-relevant information rather than an assertion of total physical equivalence.
3. **Critical growth example:** at `(2/3,1/8,1/4,1/4,1/3)`, `kc=11/12`, `kb=25/24`, and `λ1=(2/3)(25/24)+(1/3)(11/12)=1=ρ*`. The damaged-founder internal programme has expectation `11/12` at every positive census; the refused request preserves one body pathwise. The example occurs in the current written book and growth README. `GrowthClassificationCheck.critical_rates` verifies the rates, while `critical_actual_internal` supplies actual growth attainment. Do not describe the separate all-positive-census `11/12` sentence as a newly added dedicated theorem merely because those related endpoints are formal.
4. **Refusal semantics:** the explicit rejected result is `retained=some x`, no newborn, zero repair/operation payment, refund five, rejected status. No current raw noise field is consulted. The draft's explanation of the unit baseline is accurate and sufficiently candid.
5. **Resource support:** continued inflow and two-output reservation are made explicit. The manuscript does not promise closed-wallet unbounded growth or costless restoration.

## 6. Conditions for scientific sign-off

Before treating this review as cleared, the revised text should make B-S01's old-domain and independent-cohort contract explicit; scope `C` to a fixed initial population; disambiguate the gate example and tag projection; identify the rank-three task; and repair the most consequential source locators. B-S06 should be reconciled with agent A's actual original-text finding. B-S07 and B-S08 are short clarity repairs that prevent foreseeable technical misreadings.

Subject to those revisions, the paper's scientific conclusion is appropriately bounded: **one implemented finite source exhibits both failures of explanatory transfer and conditional compatibility of paid recovery, inherited execution and an expected-population growth benchmark.** It supports a disciplined philosophical comparison. It proves neither natural universal optimality nor relational realism itself, and the manuscript generally states that distinction well.

This report is an internal AI-assisted scientific review, not external peer review or a fresh kernel certification. A final revised-manuscript delta check is still required to confirm that the proposed repairs were actually made.
