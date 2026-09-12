# UEOT Core v3.0 — Parallel Lean Completion Roadmap

This is the execution plan for completing all 106 frozen source P-IDs in
`UEOT_Core_Mathematics_v3.0_Complete.md`.

Machine-readable live state belongs in `PID_STATUS.yaml`. Human recovery state
belongs in `FORMALIZATION_STATE.md`. The authoritative integrated source count
belongs in `V3_COVERAGE_STATUS.md`.

## 1. Promotion gate

A P-ID is counted `proved` only after: exact source audit, source-faithful Lean
closure, official import reachability, feature full-target CI, minimal clean
port, clean-port CI, PR CI, serialized `main` integration, post-main
`lake build UEOT`, prohibited-proof audit, and ledger synchronization.

Helpers and isolated green files do not increment source coverage.

## 2. State semantics

Do not collapse all unfinished work into `pending`.

- **SOURCE_AUDIT** — frozen statement and existing-library coverage are being mapped.
- **PROOF** — at least one source-essential missing lemma remains.
- **INTEGRATION** — proof is complete but official import/clean-port work remains.
- **PROMOTION** — source-complete clean port is moving through CI/PR/main.
- **BLOCKED** — dependency or source ambiguity prevents correct proof work.
- **PROVED** — passed the full gate and is counted in `V3_COVERAGE_STATUS.md`.
- **ARCHIVE** — merged/superseded/historical evidence only.

`pending` in the coverage ledger means only “not yet counted proved”. Before
writing Lean for any P-ID, read its proof contract in `PID_STATUS.yaml` and
prove only the listed `missing` obligations.

## 3. Current checkpoint — 2026-09-12

- integrated proved: **50/106**
- P-STAT-06: **PROVED/CLOSED**
- P-INFO-02: **PROOF**
- P-INFO-03/04: **SOURCE_AUDIT**
- P-INT-01: **BLOCKED** on canonical conditional-information interface

### Lane A — P-STAT-06 [CLOSED]

Promotion completed through post-main CI:

- feature CI `34684444280`: success;
- clean-port CI `34684655595`: success;
- PR #40 CI `34685272294`: success;
- main commit `d17d0e78ec7bf9cd35b1d314afa93aaeecdcb092`;
- post-main CI `34685534516`: success.

No new Doob/Hoeffding/MGF/radius/union/feature wrapper belongs under P-STAT-06
unless a future frozen-source audit finds a substantive mismatch.

### Lane B1 — P-INFO-02 [PROOF]

Frozen target:

`E TV(P(Y|H), P(Y|M,U)) <= sqrt(I(H;Y|M,U)/2)`.

The source audit corrected the earlier “wrapper-only” diagnosis. Pinned Mathlib
has measure-theoretic KL chain/data-processing, but no directly reusable
measure-level Pinsker theorem was found. The proof contract is therefore:

1. binary Pinsker analytic core;
2. boundary cases for event probabilities 0 or 1;
3. event-indicator KL data-processing reduction;
4. supremum over measurable events to obtain `2*TV^2 <= KL`;
5. conditional-kernel averaging;
6. Jensen square-root step;
7. one canonical source-facing P-INFO-02 theorem.

Active branch: `formal/pinfo02-pinsker`.

Current completed layer: `UEOT.V3.InformationBinaryPinsker`, proving the open
binary-simplex analytic inequality and imported by the official `UEOT.V3`
target. Current feature CI: `34685655814`.

### Lane B2 — P-INFO-04 [SOURCE_AUDIT]

Frozen target is the identity-memory Fano lower bound

`I(J;Y_T) >= log K - h2(e) - e*log(K-1)`.

Mathlib has no directly reusable Fano theorem. Existing external Lean prior art
covers a finite single-distribution entropy inequality, but the frozen source
still needs the joint/conditional Fano statement, decoder data processing, and
the repository's measure-theoretic mutual-information bridge. Do not replace
that contract with a weaker finite entropy wrapper.

### Lane B3 — P-INFO-03 [SOURCE_AUDIT]

Frozen target:

`R_obj(0) = H(C|U)` for discrete canonical predictive core
`C=P(Y in . | H,U)`, with random encoders allowed.

The integrated deterministic-statistic stack is reusable, but it does not by
itself prove the random-encoder rate-distortion statement. The missing work is
the genuine predictive-rate-distortion interface, zero-distortion
recoverability, conditional DPI lower bound, and attainability by `M=C`.

### Lane C — P-INT-01 [BLOCKED]

Do not start another conditional-independence formalism. Reuse the canonical
conditional-information interface produced by the P-INFO packet. The frozen
target is an iff/bridge statement, not a one-direction surrogate.

### Lane D — remaining pending families [SOURCE-AUDIT POOL]

QSD/persistence, implementation/composition, control/quotient, KL/variational,
and final assembly work may enter PROOF only after a source/dependency audit
records a concrete missing obligation in `PID_STATUS.yaml`.

## 4. Concurrency discipline

- proof development may be parallel; main promotion is serialized;
- one P-ID family owns one module or tight module group;
- no second entropy/KL/concentration stack when an integrated one already exists;
- while one lane waits in CI, work on another lane's source audit or actual
  missing lemma; repeated CI polling is not proof progress;
- do not rebase stale experimental branches merely to make them look current;
  clean-port only the verified source-matched delta.

## 5. Merge train

`source audit -> proof contract -> only missing helpers -> canonical source theorem -> official import -> feature CI -> clean port -> clean CI -> PR CI -> serialized main integration -> post-main CI -> ledger sync`.

## 6. Completion condition

UEOT Core v3.0 is machine-complete only at **106 proved / 0 partial / 0 pending**,
with full `lake build UEOT` green on `main`, source-to-ledger consistency green,
transitive prohibited-proof/axiom audit green, and no P-ID counted through a
helper theorem alone.
