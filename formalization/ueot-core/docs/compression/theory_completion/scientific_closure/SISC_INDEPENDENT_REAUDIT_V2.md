# SISC independent re-audit v2 — scientific truth conditions

Baseline: local `research/sisc-local-20261008@921d4c4204d8385eb093462b4b5ee503306dcfd3`.
Scope: ten stage commits, all six new Lean modules, C7 protocol/runner/verifier
and `audit_sisc_local.py`. This is a **source-to-claim review**, not a new
independent external scientific experiment. All original commits remain
preserved; no frozen Core file is to be modified.

## Findings ranked by scientific risk

| ID | Grade | Exact finding | Corrective test / boundary |
|---|---|---|---|
| A-01 | HIGH | SI-3 assumes `tp` and *all-parent* model residual bounds `hParent`; it proves conditional preservation after chosen transport, not discovered parent correspondence, new objecthood or nontrivial object formation. | Add direct mechanism→registered candidate uniqueness bridge; prove at least one nonempty, separating instance; retain mechanism discovery OPEN. |
| A-02 | HIGH | SI-4 finite path theorem starts from the independent premise `∀p, ∃q, edge p q ∧ defect≤delta`. The earlier SI-3 theorem was not used to provide this premise. | Prove a restricted SI-3→SI-4 composition without assuming an equivalent `hStep` and explicitly expose global source-completion assumptions. |
| A-03 | HIGH | SI-2 `ResponseSeparated` is global on **all** target tokens and hence stringent, hard to calibrate, and sometimes incompatible with observation-identical clones. Candidate registration/coverage and causal edge truth are not proved. | Add local, provenance-filtered uniqueness and a clone-aware unresolved witness. Never reinterpret unique registration as physical identity. |
| A-04 | HIGH | C7 hash manifest is authored only after collection and by the same producer. A coherent replacement of the JSONL and its manifest is not detectable without an **independent precommitted anchor**. Existing same-author verifier is not independent. | Preserve immutable v1 evidence; add separately named shadow verifier with richer consistency checks and forgery demonstration; remain REVIEW_PENDING/UNVERIFIED. |
| A-05 | MEDIUM | C7 verifier does not check cross-stage clone inode stability on UPDATE, renamed file name on every stage, timestamp monotonicity, or schema provenance. `PASS_METHOD` must not mean source authenticity. | Add a versioned verifier **without rewriting preregistered v1 runner/verifier or raw evidence**; mutate only temporary copies in regression. |
| A-06 | MEDIUM | `audit_sisc_local.py` hardcodes exactly ten commits. Future independently committed improvements would make the project's own gate fail, and Python `assert` checks vanish with `python -O`. | Distinguish frozen base ten and later append-only audit commits; use explicit checks, not optimization-sensitive `assert`, for critical provenance. |
| A-07 | MEDIUM | C5 exact rejection requires the actual operator-norm error envelope. Rank of common 2D at a fixed budget point does not identify named physical Π/Φ and exact and practical nulls have different rejection thresholds. | Retain correct theorem; add targeted null-boundary controls and measurement contract; no experimental confirmation claim. |
| A-08 | MEDIUM | C6 price `lambda` is an external evaluator input. Pareto dominance and measurement do not select a purpose, let alone derive GOD or GOA. | Keep C6 OPEN; prepare independent evaluator/viability prerequisites instead of repackaging existing optimization as universal teleology. |
| A-09 | LOW | SI-1 countermodels show logical non-identifiability, not empirical prevalence; one constant `Bool→PUnit` map has zero information by construction. | Preserve as boundary theorem with exact type scope, not universal physical no-go. |

## Essential mathematical upgrades

1. **Derived existence + discriminating observations:** define a registered
   post-transport candidate predicate `FormedByResponse` with independent
   provenance; from SI-3 construct the exact transported completion. Add a
   single-register response-gap theorem to reject any competing completion.
   For every competitor `q ≠ tp p`, a registered coordinate must separate
   response vectors by more than `2 * tau_target`, *not* just their labels.
2. **Finite path coherence from formation mechanics:** in a homogeneous
   response-channel subclass and with independently checked universal source
   formation, derive `q=tp p` as an edge witness and the C4 binding defect as
   its quantitative bound; instantiate SI-4 path induction. Do not call this
   a theorem for arbitrary changing parent fibres.
3. **Empirical negative controls:** document that coherent evidence forging
   accompanied by a recomputed hash is undetectable with self-signed hashes.
   Make evidence consistency failures distinguishable from a coherent tested
   hypothesis failure. Preserve the archival v1 receipt byte-for-byte.

## Publication and evidence rule

Each correction is to be added on the same local branch with an independent
commit and exact-head tests. The old ten commits are not rewritten. A proof
that a conditionally declared theorem compiles is a *formal* result; an
independent response mechanism or a real-world `SameObject` conclusion
requires different evidence. No GitHub push, issue mutation, PR or scientific
status promotion is authorized by the present local re-audit.
