# UEOT Core v3.0 Lean Coverage Status

This file is the **authoritative source-level P-ID ledger** for the frozen
`UEOT_Core_Mathematics_v3.0_Complete.md` specification.

## Verification contract

- source P-IDs: **106**
- canonical source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`
- Lean: **4.33.1**
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- official target: `lake build UEOT`
- integration branch: `main`
- canonical source object: project File Library
- exact canonical source bytes in public repo: pending synchronization

A P-ID is counted `proved` only after frozen-source semantic matching, official
import reachability, feature/integration/post-main CI gates, prohibited-proof
audit, safe main integration, and ledger synchronization. Feature-green work
alone never changes this ledger.

## Current source-level coverage

| status | count |
|---|---:|
| **proved** | **63** |
| **partial** | **0** |
| **pending** | **43** |
| **total** | **106** |

`pending` means only “not yet counted proved”; it does not mean no relevant
mathematics or Lean code exists.

## Proved P-ID set

- **Carrier / representation:** P-CAR-01, P-CAR-02, P-CAR-03, P-CAR-04
- **Resolution:** P-RES-01, P-RES-02, P-RES-03, P-RES-04, P-RES-05, P-RES-06
- **Prediction:** P-PRED-01, P-PRED-02, P-PRED-03
- **Dynamics:** P-DYN-01, P-DYN-02, P-DYN-03, P-DYN-04
- **Statistics:** P-STAT-01, P-STAT-02, P-STAT-03, P-STAT-04, P-STAT-05, P-STAT-06, P-STAT-07, P-STAT-08, P-STAT-09
- **Invariant / identifiability:** P-INV-01, P-INV-02, P-INV-03, P-INV-04, P-INV-05
- **Quotient:** P-QUO-03
- **Refinement / agency:** P-REF-04, P-REF-05
- **Telescoping reward:** P-TEL-01
- **Bridge:** P-BRG-02
- **Metric:** P-MET-01, P-MET-02
- **Internal/external factorization:** P-INT-01, P-INT-02, P-INT-03
- **Information:** P-INFO-01, P-INFO-02, P-INFO-03, P-INFO-04, P-INFO-05
- **Process:** P-PROC-01
- **Recovery:** P-REC-01, P-REC-02
- **QSD:** P-QSD-02
- **Persistence:** P-PER-01, P-PER-03
- **Transport / identity:** P-ID-01, P-ID-02
- **Representation covariance:** P-FAC-01
- **Omega / integrity:** P-OMG-01, P-OMG-02
- **Dual-drive / alignment:** P-DDH-01, P-ALI-03
- **Composition:** P-COMP-03, P-COMP-05
- **KL / path information:** P-KL-01
- **Evolution:** P-EVO-01

Count check: `61 + 2 = 63`.

## Newly counted promotions — P-EVO-01 and P-COMP-05

### P-EVO-01 — exact Price selection/transmission decomposition

Frozen contract retained in the source-facing theorem:

- finite parent and offspring type spaces;
- `M = D_b K`;
- `b_i >= 0`, including zero-growth rows;
- deterministic mean-frequency update `p' = pM / bar_b`, requiring only
  `bar_b > 0`;
- exact covariance/selection plus transmission decomposition;
- no identification of that deterministic mean-frequency ratio with an
  expected random population-frequency ratio.

Canonical theorem: `UEOT.V3.EvolutionPrice.p_evo_01`.

Evidence:
- feature branch `formal/pevo01-price-decomposition`;
- feature head `a3f9473c4dfb71c049fa177a5effce46837122bd`;
- feature CI `34754264183`: success;
- final patch only exposed the pinned finite-sum commutation API; no source
  semantic change.

### P-COMP-05 — canonical Booleanization of overlapping regions

Frozen contract retained: membership-signature cells uniquely partition the
base, reconstruct the original regions, and the nonempty cells are exactly the
atoms of the unique least Boolean algebra containing all declared regions.

Canonical theorem: `UEOT.V3.CompositionBooleanAtoms.p_comp_05`.

Evidence:
- feature branch `formal/pcomp05-boolean-atoms`;
- feature head `dfb398a6c2f8edfa458ef5d2a242f02fd3d46971`;
- feature CI `34754344097`: success;
- implementation uses `BooleanSubalgebra.closure (Set.range V)` directly;
- local decidable membership is confined to an internal helper and does not add
  a source-facing mathematical assumption.

### Joint promotion evidence

- clean integration branch `formal/evo01-comp05-main-integration`;
- clean atomic integration/main proof commit
  `bfd9d83073cb929ea12de4267005023749023df5`;
- exact proof diff: two source-facing theorem files plus their two top-level
  imports;
- integration CI `34754713285`: success;
- safe non-force main fast-forward to the same proof commit;
- post-main CI `34754974676`: success;
- prohibited-proof audit: `sorry=0`, `admit=0`, `native_decide=0`, unsourced
  `axiom=0`;
- frozen-source semantic audit: complete.

**Status: BOTH PROVED / COUNTED.**

## Active unresolved front

There are **43 not-yet-counted P-IDs**.

Active source-facing proof lanes:
- **P-COMP-06** — `formal/pcomp06-carrier-lift@168e432b8479a6683d933d81bc1e362df2a4340c`; feature CI `34754842269`: success. It retains both nested inclusion-min operations in the physical-carrier→child-coalition lift. Awaiting final source/prohibited audit and clean promotion from the latest full-green main.
- **P-COMP-07** — `formal/pcomp07-composition-window@0826699b3fe135c3faec353153cc4d2fa533e13a`; feature CI `34755041666` pending at ledger creation. Compactness + continuity are used to derive attained threshold boundaries; boundary witnesses are not assumed.
- **P-ALI-02** — `formal/pali02-parent-value@b0ef953829c83f0219ffe62e8b54243ae2270b51`; feature CI `34755240251` pending at ledger creation. The source Hilbert decomposition and Cauchy--Schwarz lower bound are represented directly.

Audited next lane: **P-KL-03** can reuse
`UEOT.V3.InformationKernelKL.klDiv_compProd_right_eq_lintegral`, pinned Mathlib
`klDiv_compProd_eq_add`, and Ionescu--Tulcea finite-prefix infrastructure. The
remaining obligation is finite-horizon iteration for possibly history-dependent
kernels; a one-step or homogeneous-Markov surrogate is not countable.

## Reproducibility task

The exact canonical source bytes are still not present in the public repository.
Synchronizing those exact bytes and independently recomputing the SHA-256 is
separate from theorem proof status.

## Completion rule

UEOT Core v3.0 is machine-complete only when all **106** frozen-source P-IDs pass
the source-theorem proof contract; helpers or feature-green branches never count
on their own.
