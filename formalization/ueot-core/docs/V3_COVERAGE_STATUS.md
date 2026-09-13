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
| **proved** | **64** |
| **partial** | **0** |
| **pending** | **42** |
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
- **Composition:** P-COMP-03, P-COMP-05, P-COMP-06
- **KL / path information:** P-KL-01
- **Evolution:** P-EVO-01

Count check: `63 + 1 = 64`.

## Newly counted promotion — P-COMP-06

### P-COMP-06 — physical carrier to child-coalition lift

Frozen contract retained exactly: child-coalition sufficiency is induced by
covering at least one physical minimal carrier, and the minimal sufficient child
family is the **outer inclusion-minimum** of the union of the per-physical-carrier
minimal covering families. Both nested inclusion-min operations are present in
the machine theorem.

Canonical theorem: `UEOT.V3.CompositionCarrierLift.p_comp_06`.

Evidence:
- feature branch `formal/pcomp06-carrier-lift`;
- feature head `168e432b8479a6683d933d81bc1e362df2a4340c`;
- feature CI `34754842269`: success;
- clean integration branch `formal/pcomp06-main-integration`;
- clean integration/main proof commit
  `b26de5a7bf8a725e9446b883f9181d0732e86c7f`;
- exact integration diff: theorem file plus one top-level import;
- integration CI `34755655869`: success;
- safe non-force main fast-forward;
- post-main CI `34755873092`: success;
- prohibited-proof audit: `sorry=0`, `admit=0`, `native_decide=0`, unsourced
  `axiom=0`;
- frozen-source semantic audit: complete.

**Status: PROVED / COUNTED.**

## Previous counted promotions — P-EVO-01 and P-COMP-05

- `UEOT.V3.EvolutionPrice.p_evo_01`, feature CI `34754264183`: success.
- `UEOT.V3.CompositionBooleanAtoms.p_comp_05`, feature CI `34754344097`: success.
- joint clean integration commit `bfd9d83073cb929ea12de4267005023749023df5`;
- integration CI `34754713285`: success;
- post-main CI `34754974676`: success.

## Active unresolved front

There are **42 not-yet-counted P-IDs**.

Active source-facing proof lanes:
- **P-COMP-07** — `formal/pcomp07-composition-window@9337f0d58ebb283a1560ba947671ecf2688d0b59`. Source theorem remains exact: compact interval, continuity-derived attained threshold boundaries, monotone/antitone diagnostics, and interval-or-empty joint feasible set. Current engineering blocker is the pinned Mathlib real-topology import chain; no boundary witness has been added as an assumption.
- **P-ALI-02** — `formal/pali02-parent-value@a6dd0fe8d06c31abd1c950608698452e2ced3c94`; feature CI `34756045489` running at this ledger creation. The source-facing theorem now uses `PiLp 2`, real `HasGradientAt` certificates and an actual `HasDerivAt` trajectory, so `dJ_P/dt` is produced by the chain rule rather than assumed.

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
