# Chapter 66: empirical, originality, resource, and evidence review

## 1. Scope and source identity

**Reviewer:** internal agent B. **Review date:** 2026-11-11 UTC. **Decision:** PASS for the empirical and resource boundaries of the bound Chinese chapter, with the prior-art clarification in §3 recommended for the bilingual publication. This is an internal independent review, not external peer review or experimental confirmation. The final English integration and PDF appearance require their own observed checks.

The review was extended after new physics research reached main. The prior review of chapters 0–65 remains a historical checkpoint; it is neither overwritten nor misrepresented as having included chapter 66. The new research publication is edition 3.6 with 67 chapters and 173 stable result IDs. The principal editor is preparing the bilingual edition 3.7. This report adds a review projection over the existing claim ledger rather than another authoritative ledger.

| Input | Verified identity |
|---|---|
| Refreshed main | `925e3a8a411c0b1bab99dd9150bf005893656140` |
| Research source commit / PR | `4e5de046ad59eaa37856027af6547ca26bdea1c2` / PR 450 |
| Tested main commit | `dee9bfa68c5fc60bed2853356c28011b0d3c53a0` |
| Main research book SHA-256 | `eabce172cd32773e21fa5373359d0fef7e52442b5d0368e11268130b4f89e921` |
| Assigned chapter extraction SHA-256 | `0b108dcda4c78483230101adf48869a1e2cee4441b67665d4e1cf4429d128b3a` |
| Current research status SHA-256 | `74c1c20973a1845d7b7e1b8543a0483ce58fb5a0198fb1894d729ad0442f69f7` |

The reviewer read all 16 sections, the supplied book diff, `CURRENT.json`, local Lean/runtime receipts, exact finite results, numerical diagnostics, and the committed PR/main verification records through `git show` at the pinned main commit. The chapter extraction matches that commit up to boundary whitespace. All nine runtime sources were independently hashed and match the execution receipt. No formal working tree, kernel, Lean source, experiment data, or remote branch was modified. No scientific test suite or heavy proof build was rerun.

## 2. Scientific and empirical assessment

Chapter 66 is a conditional finite-quantum construction. It fixes complex Hilbert spaces, complete original instruments, visible labels, a finite controller, and a predeclared acceptance event. The transformed experiment reproduces the original accepted joint record–terminal-state law under its stated initial-state and action assumptions. It does not increase the success probability of an unchanged original experiment or establish a new law of nature.

The following distinctions are explicit and scientifically necessary:

- Hidden Kraus indices and internal random seeds are not silently added to visible records. Matching a summed channel or a terminal marginal is weaker than matching the full labelled CQ output.
- Singular support is retained. Completion independence holds on the exact reachable support; leakage can make different legal completions distinguishable.
- Shared observation fibres require shared randomization weights. An implementation using information unavailable to its controller is not admitted by the criterion.
- Complete positivity of a mathematical target does not imply that a device's allowed action library can implement it. The convex-hull criterion concerns one round of finite-library classical randomization, not arbitrary quantum circuit controllability.
- A deterministic normalized filter for one known state is not a universal channel on unknown inputs. The rank-one replacement exception concerns the system marginal; retaining a correlated external reference changes the task.
- Repeated trials require fresh preparations and independent reset. A single unknown state is not assumed to be available again after failure.
- Cost, calibration, numerical approximation, and mathematical existence retain separate responsibilities. Numerical residuals and LP statuses do not become exact certificates or hardware performance measurements.

No empirical overclaim or blocking resource-accounting error was found in the reviewed chapter. A device that violates a stated implementation contract would reject that implementation model; it would not thereby refute standard quantum mechanics or confirm a uniquely UEOT mechanism.

## 3. CFW-R1 and the originality boundary

**Verified primary source:** Federico Carollo, Juan P. Garrahan, Igor Lesanovsky, and Carlos Pérez-Espigares, *Making rare events typical in Markovian open quantum systems*, Physical Review A **98**, 010103(R), published 10 July 2018. [Publisher](https://journals.aps.org/pra/abstract/10.1103/PhysRevA.98.010103), [DOI](https://doi.org/10.1103/PhysRevA.98.010103), [author manuscript v2](https://arxiv.org/html/1711.10951v2).

The publisher metadata and the manuscript's main argument, time-dependent construction, and finite-time examples were read. The paper includes a time-dependent quantum Doob transform, a backward terminal-value construction, and the Hamiltonian in Eq. (11). Its finite-time examples and Fig. 4 use sampled quantum-jump Monte Carlo trajectories. They are numerical demonstrations, not the report of a new hardware experiment. The displayed August 2026 HTML header is not the publication date.

Accordingly, finite-time quantum Doob construction itself is established prior art. Chapter 66's separately stated responsibilities concern its accepted finite tree, original visible CQ output, singular support, specified action library, observation restrictions, initialization, costs, and proof bindings. This review verifies the relevance of one primary precedent; it does not establish worldwide priority for every formula or combination in the chapter.

**Suggested bilingual clarification in the opening paragraph:**

Chinese: “改变动力学使原稀有轨迹成为另一过程的典型轨迹已有量子 Doob 研究先例，包括有限时间的时变构造 [CFW-R1]；本章的责任是把原来源、可见记录、奇异支撑、实际动作库、资源和形式证明连接起来，不据此声称发现了新的自然规律。”

English: “Changing the dynamics so that rare trajectories of the original process become typical in another process has precedents in quantum Doob theory, including finite-time, time-dependent constructions [CFW-R1]. This chapter connects the original source, visible records, singular support, the allowed action library, resources, and formal proofs; it does not claim a new law of nature.”

The research/source appendix should similarly identify the finite-time precedent without implying that the external paper proves all the project's added finite-tree and implementation statements. This clarification was sent to agents A and C and the principal editor.

## 4. Existing result IDs and their empirical responsibilities

All entries below use the chapter's existing identifiers. The data column is deliberately explicit: the current evidence consists of mathematical arguments, finite witnesses, and recorded program executions, not measurements on a new physical device.

| Claim ID | Model result and standard-physics basis | Additional operational premise | Observable or test | Present evidence and failure boundary |
|---|---|---|---|---|
| P-FCOND-01 | Backward adjoints of complete finite instruments give the accepted-event effect and original success probability. | Fixed original tree and event, with all rejected leaves retained. | Original acceptance frequency and complete branch probabilities. | Conditional proof; a device needs independently calibrated original instruments. Changing the controller requires a new effect. |
| P-FCOND-02 | A positive Gram sum forces every branch to annihilate the acceptance kernel. | Exact support of the derived effect. | Support leakage and branch action on declared inputs. | Mathematical statement; a floating rank estimate cannot certify the premise. |
| P-FCOND-03 | Support transformation plus legal complement produces a complete instrument. | Correct roots/inverses on support and an actual complete fallback. | Outcome-resolved instrument tomography, including failures and leakage. | Exact and numerical witnesses are separate. A noncomplete approximate Kraus list is not an admitted physical action. |
| P-FCOND-04 | The transformed finite tree matches each accepted original leaf block after normalization. | Positive acceptance probability, specified transformed initial state, unchanged target event. | Complete joint visible records and terminal-state conditional tomography. | No acquired device data. Matching only a marginal or success fraction does not establish this result experimentally. |
| P-FCOND-05 | Labelled Choi coordinates translate allowed randomization into a convex-hull iff. | Fixed finite library, specified input restriction, common weights within an observation fibre. | Calibrated action maps, realized controller weights, and allowed information. | Exact finite positive and negative witnesses. Failure for a specified completion or support does not rule out all terminal-only simulators. |
| P-FCOND-06 | A real linear separator excludes the specified convex class. | All allowed actions satisfy the separator inequality. | Calibrated confidence region for the same labelled Choi functional. | An exact model certificate is supplied; no noisy-device exclusion has been performed. Enlarging the library changes the null class. |
| P-FCOND-07 | Affinity/no-signalling restrictions classify deterministic normalized initialization; rank-one marginal replacement is exceptional. | Same channel on all unknown inputs; reference preservation is a separate requirement. | Preparation tests including mixtures and, when claimed, correlated references. | Paper classification with exact finite controls. A known-input success does not establish an all-input implementation. |
| P-FCOND-08 | A complete scaled filter has success probability `p_G/c` and the stated posterior. | Admissible scale and independent fresh preparations for repeated attempts. | Filter pass/fail counts and posterior tomography. | No filter hardware data. Optimality concerns the specified one-Kraus scaling family, not all resource strategies. |
| P-FCOND-09 | Independent renewal gives total mean cost `mu/p`, including early termination. | Fresh independent trials, consistent nonnegative cost units, all preparation/failure/reset costs. | Time-ordered records with actual costs, success indicators, and reset verification. | Paper expectation argument and finite formal recurrence; no measured speedup. Drift or failed reset invalidates the renewal model. |
| P-FCOND-10 | Complete-output trace distance bounds accepted-output error by the stated sharp probability factor. | Same acceptance extractor and positive probabilities. | Full unselected output statistics, including rejection, plus acceptance rates. | Exact rare-event examples. Selected samples alone cannot establish the source error budget. |
| P-FCOND-11 | Kraus operator-norm differences give a sufficient labelled one-step defect bound. | Two legal complete instrument families, compatible labels, fixed controller and modeled reference. | Independent operation-error and norm certificates propagated through the protocol. | Paper sufficient bound; floating residuals alone are not certified real upper bounds. Unmodeled couplings are outside scope. |
| C-FCOND-01 | A vanishing positive eigenvalue can produce a diverging support inverse root. | Exact matrix family and support semantics. | Numerical condition diagnostics, not a new observable effect. | Exact counterexample plus recorded numerical rejection control. Treating small positive eigenvalues as zero changes the model. |

## 5. Numerical examples and cost interpretation

The following values were checked against the inspected exact receipt and the chapter's matrix/cost expressions. The exact receipt has SHA-256 `26f47f9a501f6cf9567e686b310523cd01ae73c91801655e202010402e2c86ad`. Its 95 listed entries all have `PASS_EXACT_SYMBOLIC`; this review did not execute those 95 checks again.

| Quantity | Checked result | Interpretation |
|---|---|---|
| Pauli example, three-step acceptance | `1/8` | Original probability; transformed initialization is unchanged because the effect is scalar. |
| Pauli example, action cost per original attempt | `7/4` | Includes failure early stopping: one mandatory call, then continuation probabilities `1/2` and `1/4`. |
| Pauli example, original cost per success | `14` | `(7/4)/(1/8)` under the stated action-only units. |
| Pauli implementation | Weights `1/2,1/2`; three actions; `3+3r` with randomization overhead | The comparison requires `3+3r<14`; measured preparation, reset, control, readout and calibration costs can remove the advantage. |
| Non-scalar example, backward root effect | `[[183,27],[27,51]]/4096` | Matches the exact receipt. |
| Non-scalar original success probability | `117/4096 = 0.028564453125` | Neither the transformed law nor scaled initialization changes this original probability. |
| Non-scalar original action cost | `701/512` per attempt; `5608/117 ≈ 47.9316` per accepted output | Cost is derived from actual early-stop leaf probabilities, not maximum depth multiplied by expected attempts. |
| Best scale in the stated filter family | `(117+3 sqrt(565))/4096` | Largest eigenvalue of the displayed effect. |
| Scaled filter probability | `39/(39+sqrt(565)) ≈ 0.6213186012` | Equivalent to the receipt's rationalized expression. This is the initial filter's probability, not an observed hardware success rate. |
| Original-only action library | Failure probability `23/32` on `I/2`; uniform lower bound `5/8` | Separates this library from the target with zero failure probability. Extra filters/new actions are a larger class. |
| CP branch order difference | `[[0,-1/128],[-1/128,-3/256]]` on `P_0` | A genuinely noncommuting branch-map witness; the Pauli conjugation channels in the first example commute despite anticommuting Kraus representatives. |

The numerical reference reports CQ and completeness residuals of order `10^-16`. Their status remains floating-point diagnostics. The exact examples, general Lean declarations, and a certified general spectral algorithm are different claims. Source inspection confirms that `psd_factors` tests the ratio of positive eigenvalues, rejects the recorded near-singular positive case, and does not discard a uniformly small positive scalar effect merely because of absolute scale. Small negative floating errors may be clipped and are recorded; this is not an exact support-certification theorem.

## 6. Actual execution, stored remote acceptance, and publication reuse

| Evidence event | Inspected record | What it supports |
|---|---|---|
| Local v31.10 runtime execution | `runtime/execution_receipt.json`, completed `2026-11-11T05:13:40.866317+00:00`; SHA-256 `2e16fd056d90eb939ce13784bed77fc76cda3763e681296b966a7ca89b88c20f` | 19 semantic tests, 95 exact finite symbolic checks, and separate numerical-reference execution on nine identified sources. The semantic log was read, not merely its PASS flag. |
| Local v31.10 Lean execution | `lean-verification.json`, recorded `2026-11-11T05:14:38.455449+00:00`; SHA-256 `1888f3c1a3409fa90dcda2797b6387b1e9bf65f36a2dcee0a2e93241401fd941` | Complete public build and 1285 requested named axiom reports; 49 modules and 959 explicit theorems, including eight new modules, 105 explicit theorems and 162 new audit targets. 1285 is not a count of new theorems or physical laws. |
| PR 450 CI | [run 42966223125](https://github.com/MurphyHoops/UEOT/actions/runs/42966223125), source `4e5de046…` | The committed verification record reports successful runtime and Lean jobs, matching 19/95/1285 counts and identified runtime files. |
| Independent main CI | [run 42967294067](https://github.com/MurphyHoops/UEOT/actions/runs/42967294067), tested main `dee9bfa6…` | The committed verification record independently reports successful jobs and the same counts; the integration record binds equal tested source/main trees. |
| Metadata/current main | `925e3a8a…`, status `MAIN_VERIFIED` | Later metadata records the preceding events. It is not itself another execution of all gates. |
| This bilingual publication review | Readback and source hashes in `ch66_review/RECEIPT_READBACK.json` | Independent manuscript/source/receipt consistency checks and primary-source review. No new 19-test run, 95-check run, 1285-audit run, or hardware experiment. |

Agent B inspected the committed CI records, not a fresh live GitHub API response or newly downloaded artifact archive. The integration receipt states that artifact contents were inspected in the research acceptance and that raw ZIP bytes were not hashed; the publication must preserve that scope. All nine current runtime files were directly compared with their recorded hashes in this review. The separate 155-file recursive proof closure and the CI's directly hashed source count must not be conflated.

The chapter correctly distinguishes the Lean finite-tree/intertwining and related contracts from paper proofs of all-input initialization classification, the retained-reference obstruction, the Kraus norm estimate, and the infinite iid expectation interpretation. Nearby Lean success does not upgrade those paper arguments to formal declarations. The old 757 monograph checks keep their edition-3.0 execution identity.

## 7. Publication integration instructions and open empirical work

The new research diff contains phrases such as “this edition” and “executed in this round”. In bilingual edition 3.7 these must explicitly refer to **the v31.10 research execution / research edition 3.6**, while the present publication reuses identified evidence. Preserve the earlier B-RT corrections to §0.4–0.5 and §0.11 when integrating the incoming research text. Do not restore the old implication that project hardware-experiment receipts already exist. The historical B-02 correction from `[0,56]` to `[0,65]` remains true for its original checkpoint; the enlarged current edition separately uses `[0,66]`.

A future device validation should freeze the original instruments, accepted tree, controller observations, allowed library, preparation/reset procedure, error estimator, cost units, and failure thresholds. It should retain all rejected records and failures, calibrate the operation maps independently, and compare the full CQ target within declared uncertainty. An excess beyond the certified error budget rejects the specified implementation. A total measured cost that does not beat the original-process budget gives no resource advantage. Neither outcome alone identifies a new natural mechanism.

**Remaining empirical state:** no measured hardware advantage, no experimentally established universal implementation algorithm, no uniquely selected complex sector, and no unrestricted infinite-time/coherent-controller result. Chapter 66 is a substantive finite conditional and implementation contribution while these wider questions remain open. Final bilingual assembly and PDF visual acceptance are separate from this chapter-source review.

## 8. Integrated bilingual source closeout

The subsequent complete English Chapter 66 and the Chinese/English source-status increment were reviewed in publication edition 3.7, followed by a full read of the final frozen delta. The accepted Chinese source has SHA-256 `fd651a93cc4f38b755409f184bab231c43e889f648efda852340f8b594fb9060`; the English source has SHA-256 `437d4239be7a4239e701b760af1fcccdaf30f5b7ab976e9703c532990acb9a91`. All 16 sections and 12 result IDs retain the model, resource, evidence and non-hardware boundaries described above. The introduction and C.7 now explicitly acknowledge finite-time, time-dependent Doob prior art, closing the recommendation in §3. The final delta makes positive acceptance, the accepted paths, trace-distance normalization, and retries until the first success more explicit without adding empirical claims.

The separate `PUBLICATION_3_7_EMPIRICAL_CLOSEOUT.md` records the accepted source increment, reviewed appendices, and a current readback of 155 proof/configuration inputs (including 97 Core sources) plus nine runtime inputs. Its PASS is an internal manuscript/evidence review, not new scientific execution or empirical confirmation. The old 0–65 checkpoint retains its historical identity. PDF visual acceptance was not performed as part of this source closeout.
