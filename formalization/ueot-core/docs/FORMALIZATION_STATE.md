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
| integrated proved | **54** |
| active proof | **1** |
| blocked | **0** |
| pending unclassified | **51** |
| total | **106** |

The authoritative source-level ledger is **54 proved / 52 pending**.

The newest promotion is **P-INFO-03**. Its exact randomized-encoder
zero-distortion rate theorem is now source-audited, main-integrated and green
post-main. The dependency it supplied to P-INT-01 is therefore no longer a
blocker; P-INT-01 is the active proof lane.

## P-INFO-03 [PROVED / COUNTED]

Frozen target:

`R_obj(0)=H(C|U)` for discrete canonical predictive core
`C=P(Y∈·|H,U)`, allowing genuinely randomized encoders `P(M|H,U)` that cannot
access future `Y`.

Canonical source-facing theorem:

`UEOT.V3.InformationPredictiveRateZero.predictiveObjectRateZero_eq_sourceEntropy`.

The completed proof chain is:

1. genuine countable conditional entropy from `U`-disintegration;
2. generic KL conditional mutual information and fiber decomposition;
3. genuine randomized encoder joint-law geometry;
4. zero average TV implies equality of canonical and decoded future laws a.e.;
5. measurable law-code inversion recovers the discrete core from `(M,U)`;
6. conditional data processing yields the source entropy lower bound for every
   zero-distortion randomized scheme;
7. the deterministic canonical encoder `M=C` with canonical decoder has zero
   distortion;
8. its objective satisfies `I(H;C|U)=H(C|U)`;
9. `sInf` over bundled code-space + encoder + decoder + zero-distortion schemes
   gives the exact rate identity.

Source-semantics audit confirms:

- arbitrary code alphabets are Standard Borel, not artificially countable;
- countability is used only for the discrete canonical core labels;
- the encoder input is `(H,U)` and does not contain future `Y`;
- the final infimum is over whole feasible schemes rather than a fixed `M`;
- the ENNReal theorem is stronger than the frozen explicit finite-entropy
  clause and includes that source case;
- code-space quantification is universe-polymorphic within the ambient Lean
  universe, the normal predicative implementation boundary.

Promotion evidence:

- final proof branch `formal/pinfo03-rate-zero`;
- final proof head `b90cb81f5ae600ba961e2948f304aa87472c8ea9`;
- proof CI `34744325632`: success;
- clean integration CI `34744658528`: success;
- main commit `57e987a18a5dd8feca224b91e3e78b93c2a44de8`;
- post-main CI `34744919310`: success;
- prohibited-proof audit: no `sorry`, `native_decide`, or unsourced `axiom` in
  the integrated P-INFO-03 diff.

No deterministic-only reproof or duplicate conditional-information stack should
be opened absent a real source mismatch or regression.

## P-INT-01 [ACTIVE PROOF]

Frozen source theorem: **Predictive Factorization Characterization Theorem 5.1**.
For the source's Standard-Borel variables, with `Z=(M,U)`:

`Y ⟂ H | Z`

iff there exists a measurable probability-law factor
`Psi : Z -> P(Y)` such that

`C*=L(Y|H)=Psi(Z)` almost surely.

This is a general Standard-Borel theorem. It must **not** inherit the discrete
canonical-core assumption used by P-INFO-03.

Active branch:
`formal/pint01-factorization-iff`.
Base main commit:
`57e987a18a5dd8feca224b91e3e78b93c2a44de8`.
Initial active head at this synchronization:
`d0829f75ce8e8d7ee251f5644478f3b75b1e445a`.
Initial full-target CI:
`34745077495` in progress.

Current proof architecture:

1. represent the source measurable map `Psi : Z -> P(Y)` as a Markov kernel
   `Kernel Z Y`;
2. identify the canonical future law with the regular conditional kernel
   `P(Y|H)`;
3. use pinned Mathlib's
   `condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight` as the exact
   conditional-independence bridge;
4. exploit that `Z` is a measurable function of `H` to identify conditioning on
   `(Z,H)` with conditioning on `H`;
5. prove both directions of the factorization iff without countability.

Do not replace this with the finite-protocol `PredictiveClassRecovery` theorem;
that theorem is P-STAT-05 and has a different scope.

## Previously frozen closed lanes

Do not reopen without a substantive source mismatch or CI regression:

- P-STAT-06;
- P-INFO-02;
- P-INFO-03;
- P-INFO-04;
- P-ID-02.

## Parallel source-to-main audit

The audit population remains **51 unclassified P-IDs**. For each P-ID classify:

- **A:** source-facing theorem already exists on main; audit and promote;
- **B:** substantial infrastructure exists but a precise source obligation is missing;
- **C:** genuinely unformalized source mathematics.

Module names alone never justify promotion.

## Public canonical-source synchronization [REPRODUCIBILITY TASK]

The exact canonical source bytes are still not present in the public repository.
Required for third-party self-contained reproduction:

1. synchronize exact bytes without regeneration;
2. independently recompute SHA-256;
3. verify the frozen manifest value.

This is separate from theorem proof status.

## Mandatory recovery procedure

1. Read `PID_STATUS.yaml`, this file, then `V3_COVERAGE_STATUS.md`.
2. Fetch current main SHA and relevant Actions runs.
3. Distinguish source audit, theorem closure, official import reachability,
   feature CI, main integration, post-main CI, ledger counting, and public
   source-artifact reproducibility.
4. Read the frozen source statement before writing Lean.
5. Audit existing main code before creating new infrastructure.
6. Never use `sorry`, unsourced axioms, `native_decide`, or kernel-skipping
   devices as proof completion.
7. While CI runs, advance another independent audit/proof lane.

## Repository truth hierarchy

1. frozen canonical source specification;
2. `docs/V3_COVERAGE_STATUS.md`;
3. `docs/PID_STATUS.yaml`;
4. `docs/FORMALIZATION_STATE.md`;
5. `UEOT/V3.lean`;
6. `docs/PARALLEL_FORMALIZATION_ROADMAP.md`.
