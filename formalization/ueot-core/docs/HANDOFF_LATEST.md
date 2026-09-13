# UEOT Core 3 Lean — Fallback Handoff Snapshot

> GitHub Issue #56 is the live cross-chat construction state. This file is the
> fallback archival snapshot on `main` and is updated at meaningful lifecycle
> transitions.

## Current lifecycle snapshot

- counted coverage staged by this ledger: **68/106**;
- not yet counted: **38**;
- proof main before this docs checkpoint:
  `b3e1c152e42b4e2a2b7001776214ecaaa35aae18`;
- newest staged promotion: **P-KL-03**;
- clean-integration CI `34762400971`: success;
- post-main CI `34763070439`: success;
- source semantic audit: complete;
- prohibited-proof audit: clean;
- **68/106 becomes full-green only after this ledger/HANDOFF checkpoint is integrated to main and its own main CI succeeds.**

## P-KL-03 — staged counted promotion

Frozen source §22.3 is preserved as a finite-horizon KL chain rule for genuinely
history-dependent path kernels. The general theorem contains the distinct
initial-law term `D_KL(μ0 || ν0)`; the same-initial theorem is an explicit
corollary. No homogeneous-Markov weakening was used.

- feature branch `formal/pkl03-path-chain`;
- clean integration branch `formal/pkl03-main-integration-v3`;
- clean integration commit `d4126fbb3a9d7cd288d261de8898ee103eee85a0`;
- integration CI `34762400971`: success;
- promotion PR #57 used rebase integration;
- main proof commit `b3e1c152e42b4e2a2b7001776214ecaaa35aae18`;
- post-main CI `34763070439`: success;
- exact integration diff: theorem file + one top-level import;
- canonical theorem family:
  `UEOT.V3.PathKLChain.p_kl_03_same_initial`,
  `UEOT.V3.PathKLChain.p_kl_03_general`, and alias `p_kl_03`.

## Active proof lane — P-EVO-02

Frozen target: finite label `T`, independent of `(F,F')`, copied without error,
with exact identity
`I((F,T);(F',T)) = I(F;F') + H(T)`.

Current feature implementation:
- branch `formal/pevo02-shared-label`;
- theorem `UEOT.V3.EvolutionSharedLabel.p_evo_02`;
- independence encoded structurally by `ρ.prod (copyJoint τ)`;
- exact copy encoded by the diagonal copy law;
- `sharedRepack` only regroups `((F,F'),(T,T))` into `((F,T),(F',T))`;
- first CI `34762544028` failed only on Lean/API wiring;
- repaired head `9969ed9c4a8fdd11eec26908c0f2b7a0a89b3916` fixes `AEMeasurable`, namespace exposure and a propositional coordinate-regrouping goal without changing the source identity;
- repaired CI `34763101765` is the current feature gate;
- feature green never increments coverage.

## Source-audit lane — P-KL-02

Frozen §22.2 is stronger than an event data-processing lower bound. It requires
the exact event I-projection over all `Q ≪ P0` with `Q(A) ≥ p`:

- if `p ≤ q := P0(A)`, infimum `0`, optimizer `P0`;
- if `p > q`, infimum exactly `d_Bern(p || q)`;
- explicit optimizer reweights `A` and `Aᶜ` by the source ratios;
- prove probability, absolute continuity, exact event probability and exact KL;
- retain the `p = 1` boundary.

Existing `PathEventKL.p_kl_01`, `InformationEventBernoulli`, and
`InformationBernoulliKL` are the intended lower-bound/event-law infrastructure;
P-KL-02 must add sharp attainment rather than restate P-KL-01.

## Exact next actions

1. integrate this 68/106 ledger/HANDOFF checkpoint and require its own main CI;
2. collect P-EVO-02 CI `34763101765`; if red, repair only the exact Lean/API error without changing §25.3 semantics;
3. if P-EVO-02 is feature-green, prohibited-proof/source audit it, then clean-integrate **only** `EvolutionSharedLabel.lean` plus the top-level import from the latest full-green main;
4. in parallel, implement P-KL-02 from the latest full-green main using the explicit event-tilt optimizer and all source boundary cases;
5. feature green never increments coverage; each promotion requires integration, post-main and ledger gates.

## Guards

- do not reopen counted P-IDs absent source mismatch/CI regression;
- no `sorry`, `admit`, `native_decide`, unsourced `axiom`;
- P-QSD-01 and P-QSD-03 must never be swapped;
- P-REF-03 requires arbitrary signal spaces;
- P-DDH-04/05 require genuine rank/singular-value infrastructure;
- P-BRG-01 includes concentration/extinction/maximizer-ratio clauses;
- P-KL-04/05 must remain at their frozen CTMC/Girsanov level.

## Recovery order

1. `UEOT_CORE3_LEAN_OPERATIONS.md`;
2. Issue #56;
3. `PID_STATUS.yaml`;
4. `FORMALIZATION_STATE.md`;
5. `V3_COVERAGE_STATUS.md`;
6. live main/branches/CI.
