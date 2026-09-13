# UEOT Core 3 Lean — Fallback Handoff Snapshot

> GitHub Issue #56 is the live cross-chat construction state when available.
> This file is the fallback archival snapshot on `main` and is updated at
> meaningful lifecycle transitions.

## Current lifecycle snapshot

- authoritative full-green baseline before this checkpoint: **69/106**;
- this branch stages **70/106** after P-KL-02 completed all proof-side and
  post-main gates;
- remaining not-yet-counted P-IDs after staging: **36**;
- proof main before ledger merge: `60ac78273200f5152a5e8d8286c840697e69bb51`;
- newest staged promotion: **P-KL-02**;
- P-KL-02 full feature CI `34768634473`: success;
- P-KL-02 clean-integration PR #62 CI `34769135038`: success;
- P-KL-02 proof main commit `60ac78273200f5152a5e8d8286c840697e69bb51`;
- P-KL-02 post-main CI `34769394882`: success;
- source semantic audit: complete;
- prohibited-proof audit: clean.

**Do not call 70/106 full-green until this ledger/recovery branch passes PR CI,
lands on `main`, and the resulting main CI succeeds.**

## P-KL-02 — completed proof contract

Frozen §22.2 is implemented literally over all probability laws `Q ≪ P0` with
`Q(A) ≥ p`, for `q=P0(A)`, `0<q<1`, `0≤p≤1`:

- `p≤q`: global infimum `0`, baseline `P0` attains it;
- `p>q`: global infimum `dBern(p||q)`;
- explicit RN optimizer `(p/q)1_A + ((1-p)/(1-q))1_{Aᶜ}`;
- optimizer probability normalization, AC, exact event mass, RN density and
  exact KL are proved;
- endpoint `p=1` is retained.

Canonical theorem:
`UEOT.V3.PathEventIProjection.p_kl_02`.

Evidence:
- full-contract feature `formal/pkl02-event-iprojection@cb78b0df87ef64fc0bc61e1e320ff901247d00cd`;
- feature CI `34768634473`: success;
- clean integration `formal/pkl02-clean-int-cb78@d30d31e15f38b349488edf4a5b12c94bace70031`;
- clean PR #62 CI `34769135038`: success;
- proof main `60ac78273200f5152a5e8d8286c840697e69bb51`;
- proof post-main CI `34769394882`: success.

No homogeneous-Markov surrogate, lower-bound-only weakening, or dropped `p=1`
boundary is used.

## Next promotion lane — P-API-01

Frozen §28.3 has already completed its feature proof:

- feature branch `formal/papi01-process-interface-fresh`;
- head `0f76d04a4dcc34b2d2aaa806d5803e4823561bbc`;
- feature CI `34769177051`: success;
- diff against the 69/106 full-green base is exactly
  `UEOT/V3/ProcessInterface.lean` plus one top-level import;
- source semantic audit: complete;
- prohibited-proof audit: clean.

The exact clause composes the contravariant protocol lifts and covariant
measurable path readouts. The approximate clause gives
`TV ≤ min 1 (εAB + εBC)` by inserting the intermediate pushed law, applying
P-MET-01, and then the TV triangle inequality. It deliberately does **not** add
the control-interface structures that frozen §28.4 says require separate data.

### Exact next action for P-API-01

Only after 70/106 becomes full-green:
1. create a fresh clean-integration branch from that new main;
2. transplant only `ProcessInterface.lean` and its one `UEOT.lean` import;
3. compare against the new main and require behind=0;
4. run official PR CI;
5. merge safely and require post-main CI;
6. then ledger-sync 71/106 and require ledger main CI.

Feature green alone never increments coverage.

## Independent audit lane — P-ALG-01

Frozen §28.5 is source-locked as an exact finite partition-refinement theorem.
Given a finite state set, common finite action set, exact transition matrices,
rewards and output labels, the initial partition is equality of output plus the
complete action-reward vector. Each refinement splits current blocks by all
action/block transition masses.

The source theorem requires all of:
- finite termination;
- terminal controlled stability/lumpability;
- coarsest stable partition among refinements of the initial partition;
- preservation of output, reward and every action's one-step quotient law;
- preservation of corresponding finite-horizon output laws by induction.

Pinned Mathlib has `Finpartition` and refinement infrastructure, but the UEOT
repository has no existing complete lumpability/refinement implementation. Treat
this as a genuine medium proof lane, not a short wrapper. Exact equality must not
be replaced by floating tolerance clustering.

## Grounded non-quick fronts

- P-ALI-01: global exact-one-form / closed-loop integral theorem on connected smooth manifolds; Euclidean curl-free weakening is forbidden.
- P-DDH-02/03: finite exponential-family calculus and KL variational duality.
- P-KL-04/05: CTMC compensator / Girsanov-level stochastic analysis.
- P-EVO-03/04: Perron--Frobenius asymptotics / martingale foundations.
- P-REF-03: arbitrary signal-space conditional expectation.
- P-DDH-04/05: genuine rank/stacked-Jacobian and singular-value perturbation.
- P-QSD-01/03/04: source-locked distinct non-A results.
- P-BRG-01: includes extinction/concentration/maximizer-relative-mass clauses.

P-EVO-03 specifically requires the full K-PF-01 primitive-matrix asymptotic
package; pinned Mathlib exposes `Matrix.IsPrimitive` but no directly reusable
complete Perron--Frobenius power-convergence theorem was found. Do not replace
this with an assumed-convergence hypothesis and count it as the source theorem.

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
2. Issue #56 when available;
3. `PID_STATUS.yaml`;
4. `FORMALIZATION_STATE.md`;
5. `V3_COVERAGE_STATUS.md`;
6. live main/branches/CI.
