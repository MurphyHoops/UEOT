# UEOT Core Lean — Live Formalization State

> Recovery entry point. Machine-readable lane state is `PID_STATUS.yaml`.
> Integrated source-count truth is `V3_COVERAGE_STATUS.md`.

Last synchronized: **2026-09-13**

## Environment

- canonical source: `UEOT_Core_Mathematics_v3.0_Complete.md`
- source P-IDs: **106**
- canonical source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`
- canonical source object: available for semantic audit in the project File Library
- exact source bytes in public repo: **pending synchronization**
- current audit did **not** recompute the SHA from local raw bytes
- Lean: **4.33.1**
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- official target: `lake build UEOT`
- integration branch: `main`

## Current checkpoint

| state | count |
|---|---:|
| integrated proved | **55** |
| active proof | **0** |
| blocked | **0** |
| pending unclassified | **51** |
| total | **106** |

The authoritative source-level ledger is **55 proved / 51 pending**.

The newest promotion is **P-INT-01**. Its general Standard-Borel predictive
factorization iff, structured `(M,U)` layer, countable protocol family, common
versions/common conull set, and common measurable decoder are source-audited,
main-integrated and green post-main. There is currently no active proof lane;
the next phase is the source-to-main A/B/C/D audit of the remaining 51 P-IDs.

## P-INT-01 [PROVED / COUNTED]

Frozen source theorem: **Predictive Factorization Characterization Theorem 5.1**.
For the source's Standard-Borel variables, with structured
`H=(H^S,H^E)`, `M=f(H^S)`, `U=g(H^E)`, and `Z=(M,U)`:

`Y_f^+ ⟂ H | Z`

iff there exists a measurable probability-law factor `Psi` such that

`C^f = Psi(M,U)` almost surely.

For the declared countable intervention/protocol family, the frozen source
requires common versions so the protocol-indexed statements hold on one common
conull set.

Canonical source-facing theorems:

- `UEOT.V3.InformationPInt01.p_int_01`;
- `UEOT.V3.InformationPInt01Common.p_int_01_common`;
- `UEOT.V3.InformationPInt01Common.p_int_01_common_decoder`.

Completed proof architecture:

1. generic Standard-Borel factorization iff;
2. structured internal/environment representation;
3. forward and reverse implications;
4. canonical conditional-law factorization;
5. countable protocol/intervention family;
6. one common conull set/common version;
7. common measurable decoder packaging.

Promotion evidence:

- final proof branch `formal/pint01-factorization-iff`;
- verified feature head `3943391af4d459a370ab840d1b15babcae26f82a`;
- feature full-target CI `34747270058`: success;
- clean integration commit `d757ea0dd14755233b94d40763f457773a52089f`;
- clean integration CI `34749908649`: success;
- `main` commit `d757ea0dd14755233b94d40763f457773a52089f`;
- post-main CI `34750114264`: success;
- prohibited-proof audit: zero `sorry`, zero `admit`, zero `native_decide`, zero
  unsourced `axiom` in the clean integration diff;
- canonical-source semantic audit completed 2026-09-13.

Do not reopen this lane absent a substantive source mismatch or CI regression.
Do not import the discrete canonical-core restrictions of P-INFO-03 into this
source theorem.

## P-INFO-03 [PROVED / COUNTED]

Frozen target:

`R_obj(0)=H(C|U)` for discrete canonical predictive core
`C=P(Y∈·|H,U)`, allowing genuinely randomized encoders `P(M|H,U)` that cannot
access future `Y`.

Canonical source-facing theorem:

`UEOT.V3.InformationPredictiveRateZero.predictiveObjectRateZero_eq_sourceEntropy`.

Promotion evidence:

- final proof branch `formal/pinfo03-rate-zero`;
- final proof head `b90cb81f5ae600ba961e2948f304aa87472c8ea9`;
- proof CI `34744325632`: success;
- clean integration CI `34744658528`: success;
- main commit `57e987a18a5dd8feca224b91e3e78b93c2a44de8`;
- post-main CI `34744919310`: success.

## Closed lanes

Do not reopen without a substantive source mismatch or CI regression:

- P-STAT-06;
- P-INFO-02;
- P-INFO-03;
- P-INFO-04;
- P-ID-02;
- P-INT-01.

## Current phase — remaining source-to-main audit

The audit population is **51 unclassified P-IDs**. Before opening another proof
stack, read each frozen source statement and compare it against current `main`.
Classify each P-ID as:

- **A:** a source-facing theorem already exists on `main`; semantic audit and
  promotion may be enough;
- **B:** substantial mathematics exists on `main`, but a source-facing wrapper,
  exact quantifier alignment, or final obligation is missing;
- **C:** major ingredients exist, but one or more bridge theorems are missing;
- **D:** genuinely new formal mathematics is required.

Module names alone never justify promotion. Existing green/count\-ed P-IDs must
not be reproved during this audit.

## Public canonical-source synchronization [REPRODUCIBILITY TASK]

The exact canonical source bytes are still not present in the public repository.
Required for third-party self-contained reproduction:

1. synchronize exact bytes without regeneration;
2. independently recompute SHA-256;
3. verify the frozen manifest value.

This is separate from theorem proof status.

## Mandatory recovery procedure

1. Read `UEOT_CORE3_LEAN_OPERATIONS.md`, GitHub Issue #56,
   `PID_STATUS.yaml`, this file, then `V3_COVERAGE_STATUS.md`.
2. Fetch current main SHA and relevant Actions runs/branches/PRs.
3. Distinguish source audit, theorem closure, official import reachability,
   feature CI, main integration, post-main CI, ledger counting, and public
   source-artifact reproducibility.
4. Read the frozen source statement before writing Lean.
5. Audit existing main code before creating new infrastructure.
6. Never use `sorry`, `admit`, unsourced axioms, `native_decide`, or
   kernel-skipping devices as proof completion.
7. While CI runs, advance another independent audit/proof lane.

## Repository truth hierarchy

1. frozen canonical source specification;
2. `docs/V3_COVERAGE_STATUS.md`;
3. `docs/PID_STATUS.yaml`;
4. GitHub Issue #56 for live construction intent;
5. `docs/FORMALIZATION_STATE.md`;
6. official imported Lean source on `main`.