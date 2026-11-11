# Publication 3.7: empirical and originality review of the integrated increment

**Decision:** PASS for the source increment described below; no empirical or originality blocker was found. This is an internal, independently assigned review by agent B, not external peer review or evidence that nature supports a new UEOT mechanism. PDF visual acceptance remains a separate task and is not asserted here.

## 1. Reviewed identity and scope

The integrated sources were read from `ueot-physics-final/physics/qm/book` on 11 November 2026. The final frozen-source identities are retained in `final37_review/FROZEN_INPUT_IDENTITY.json`; the preceding integration checkpoint remains in `final37_review/INPUT_IDENTITY.json`.

| Source | Bytes | SHA-256 |
|---|---:|---|
| `UEOT_PHYSICS.md` | 706234 | `fd651a93cc4f38b755409f184bab231c43e889f648efda852340f8b594fb9060` |
| `UEOT_PHYSICS.en.md` | 858402 | `437d4239be7a4239e701b760af1fcccdaf30f5b7ab976e9703c532990acb9a91` |

This review read all 16 English sections of Chapter 66, its reading guide, all 12 stable result statements and their surrounding limitations. It compared the Chinese Chapter 66 increment against the separately reviewed research source. It also read the Chinese and English versions of §§0.5, 47.14, C.1, C.6, C.7, C.8 and F.4. A diff against the accepted 0–65 checkpoint was inspected to ensure that the old experimental-status corrections remained in place. The changes to §0.11 additionally strengthen the requirement for independent calibration, controls, or conservative bounds on ordinary errors.

The final frozen delta was read in full. It makes the positive-acceptance premise explicit in §66.9, describes the accepted paths correctly in English §66.2, specifies the one-half normalization of trace distance in §66.11, and states independent retries until the first success in §66.16. The English chapter title changes only capitalization. These revisions clarify existing contracts and add no experimental claim or altered numerical result.

The previous `INTEGRATED_EMPIRICAL_RED_TEAM` report remains a historical 0–65 checkpoint. Its original identity is not relabelled as a 67-chapter review. Together with the separate research-source review in `CH66_EMPIRICAL_REVIEW.md` and this integration review, the cumulative empirical coverage now spans Chapters 0–66 and Appendices A–F, including all 173 existing result IDs.

## 2. Chapter 66: retained scientific boundaries

| Issue checked | Finding in the integrated English and Chinese sources |
|---|---|
| Prior art | The introduction and C.7 now explicitly acknowledge finite-time, time-dependent quantum Doob constructions in Carollo et al. The added finite-tree, support, implementation and resource responsibilities are stated separately. The earlier recommendation is closed. |
| Standard physical input | Finite complex Hilbert spaces, complete instruments and a fixed controller remain explicit inputs. The text does not claim that generic Core uniquely selects this quantum sector. |
| Target object | The joint visible record and terminal quantum state remain the target. Hidden Kraus indices, a random seed, a marginal output and a success fraction are not silently interchanged. |
| Singular support | Completion independence is restricted to exact reachable support. Leakage, a zero acceptance probability and numerical inverse-root conditioning remain explicit limitations. |
| Allowed implementation | The Choi criterion concerns a stated finite action library, one-step classical randomization and common weights on each observation fibre. The text does not promote this criterion to arbitrary circuit controllability or an unrestricted terminal-only impossibility theorem. |
| Initialization | The all-unknown-input classification, known-state preparation, rank-one marginal exception and retained-reference obstruction remain distinct. Repeated fresh unknown inputs are not available for free. |
| Resource account | The Pauli comparison retains the stipulated action units and the condition `3 + 3r < 14`. The nonscalar example retains `117/4096`, `5608/117` and `39/(39+sqrt(565))` with their different probability/cost meanings. Neither example is reported as measured hardware advantage. |
| Error evidence | Full unselected outputs are required for the conditioning error premise. Floating residuals are not rigorous real upper bounds; incomplete approximate Kraus families are not admitted as complete physical actions. |
| Counterexamples | The original-only action library remains excluded only within its declared class; adding filters or actions changes the class. The Pauli conjugation maps are correctly described as commuting, while the second example tests noncommuting CP branches. |
| Proof status | The all-input classification, reference obstruction, sufficient Kraus bound and infinite-retry expectation interpretation remain paper proofs. Nearby Lean success does not upgrade their status. |
| Empirical status | No new hardware data, measured advantage, universal spectral algorithm, unrestricted coherent-controller result or new natural law is claimed. A future device experiment tests a declared implementation and its cost/error contract. |

The full prior-art check, original-paper locations, numerical readback and twelve-ID claim-to-test matrix remain in `CH66_EMPIRICAL_REVIEW.md`. No new model calculation or heavy scientific suite was executed to approve the English assembly.

## 3. Evidence identities and reuse

The source statements in C.8 match the inspected `evidence/v3.7/source-reuse.json`, SHA-256 `040f2d01b899f3e44456cb3c741c2dbbf87eaa522e6938f1188245d48f129086`. A new, narrow readback at `2026-11-11T06:07:08.693036+00:00` independently hashed all 164 listed files in the current working copy. All hashes matched the expected values. The recorded comparison columns also agree with those expected values. The counts are 155 proof/configuration inputs, of which 97 are Core sources, plus nine distinct runtime inputs. The 97 are a subset of 155 and are not added again. Both pinned Git inventories contained the same 5033 tracked Core blobs. This readback is saved as `final37_review/SOURCE_REUSE_READBACK.json`.

The research source `4e5de046ad59eaa37856027af6547ca26bdea1c2`, tested main `dee9bfa68c5fc60bed2853356c28011b0d3c53a0`, and publication baseline `925e3a8a411c0b1bab99dd9150bf005893656140` remain separate identities. Source and tested main share the recorded scientific Git tree; the later publication baseline carries metadata additions. A different metadata tree is not falsely described as a new execution of the scientific gates.

The text correctly assigns the 19 semantic/numerical controls, 95 exact finite checks and 1285 named axiom requests to their v31.10 research executions. The earlier 757 monograph checks retain their edition-3.0 identity. The 1285 requests are not called 1285 new theorems or empirical confirmations. F.4 correctly separates the general formal contracts from concrete exact programs and paper proofs.

Root reports direct inspection of live PR/run/job/step metadata; agent B's independently completed work inspected committed CI receipts, their identities and the current source readback. Agent B did not issue a fresh GitHub API request, download an artifact ZIP, or rerun Lean/runtime suites for this closeout. C.8 preserves that distinction: the original acceptance receipts document the earlier artifact-content inspection, while this publication checks remote metadata and source identity. It does not claim to have downloaded or byte-checked those original ZIPs again.

## 4. Closure and remaining publication work

The previous B-RT experimental-status corrections in §§0.4–0.5 and the reversible-record example are retained. The new research wording is explicitly attributed to research edition 3.6 / v31.10, while the bilingual publication is edition 3.7. The larger chapter/ID counts describe coverage and do not imply additional natural experiments.

There are no requested source corrections from this increment review. The primary-source attribution recommendation for CFW-R1 is now closed. The empirical limitations remain open scientific obligations, rather than publication defects hidden by a PASS label.

The PDF-build and page-inspection receipts mentioned in C.8 are separate publication deliverables. This source closeout does not certify them. No page image was inspected during this closeout; actual page inspection will be recorded only after the rendered final PDFs are available.
