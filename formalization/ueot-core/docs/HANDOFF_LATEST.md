# UEOT Core 3 Lean — Fallback Handoff Snapshot

> GitHub Issue #56 is the live cross-chat construction state when available.
> This file is the fallback archival snapshot and is updated at meaningful
> lifecycle transitions.

## Current lifecycle snapshot

- source P-IDs: **106**;
- authoritative full-green baseline before this ledger checkpoint: **72/106**;
- full-green 72 baseline: `main@8d3124b03b6e04cdde8fc5c42d76751967d043c1`;
- full-green 72 main CI: `34795931776` — success;
- this branch stages **73/106** after P-REF-01 completed all proof-side and
  post-main gates;
- P-REF-01 proof main: `1c4de9fc60b653e8c3594bba1a01a0eed510578a`;
- P-REF-01 post-main CI: `34804335400` — success;
- remaining not-yet-counted P-IDs after staging: **33**;
- active uncounted proof lanes: **P-REF-02** and **P-REF-03**.

**Do not call 73/106 full-green until this ledger/recovery branch passes PR CI,
lands on `main`, and the resulting main CI succeeds.**

## P-REF-01 — completed proof contract

Frozen §27.1 is implemented at source strength:

- reflexive state `Z=(X,S)`;
- arbitrary complete-history-dependent randomized causal policy;
- initial probability law + controlled Markov kernel + fixed causal policy
  uniquely determine the infinite `Z` path law;
- existence uses pinned Mathlib Ionescu--Tulcea trajectory machinery;
- uniqueness is certified from all recursively generated finite prefixes and
  projective-limit uniqueness, not from a definition-only wrapper;
- measurable structural modification
  `S_{t+1}=F(S_t,X_t,a_t,xi_t)` is an ordinary noise-driven controlled Markov
  kernel specialization while retaining arbitrary causal policies;
- any further compression `phi(Z)` must separately satisfy action-wise
  controlled strong lumpability; reflexivity itself does not imply closure.

Canonical source-facing theorems:
- `UEOT.V3.ReflexivePRef01.p_ref_01`;
- `UEOT.V3.ReflexivePRef01.p_ref_01_structureModification`;
- `UEOT.V3.ReflexivePRef01.p_ref_01_compression_closure_iff_kernel`;
- `UEOT.V3.ReflexivePRef01.p_ref_01_compression_closure_iff_pathLaw`.

Evidence:
- final strengthened feature `formal/pref01-source-assembly-v2@8649c0763ac2326177812209bab3f32ad92680f7`;
- feature CI `34803657950`: success;
- clean integration `formal/pref01-main-integration-v1@85148ee2e9cba8afa5e23406a51c09515d45e052`;
- PR #69 CI `34804007035`: success;
- proof main `1c4de9fc60b653e8c3594bba1a01a0eed510578a`;
- post-main CI `34804335400`: success;
- source semantic audit: complete;
- prohibited-proof audit: clean.

The final wrapper drops unnecessary `StandardBorelSpace` typeclass assumptions
because the proved theorem only requires the supplied measurable Markov kernels.
This is stronger than the Core-wide Standard-Borel default and does not weaken
the frozen source theorem.

## Active lane — P-REF-02

Frozen §27.2 requires a full finite belief-state sufficiency/control theorem.
Current branch `formal/pref02-belief-core-v1` has reached:

1. finite latent parameter/state model and stochastic transition/observation
   matrices;
2. normalized joint beliefs on `(theta,x)`;
3. predictive next-state mass and observation evidence;
4. positive-evidence Bayes posterior;
5. explicit `modelConflict` on zero evidence;
6. normalized predictive observation law;
7. a one-step `BeliefStep` whose observation law and update depend only on `(b,a)`.

Green first-layer head:
`322938a5352814c1fe5c6bf095e4a5e40e627b4e`, CI `34804267113` success.

Current second-layer head:
`871a33cb831148c655d7f4a1d708b58843ffff09`, CI `34804586631`.

Exact next work after that layer is green:
1. add bounded latent-state/action reward and expected `beliefReward(b,a)`;
2. prove the one-step discounted Bellman quantity depends only on `(b,a)`;
3. build finite-horizon belief-state dynamic programming recursively;
4. use the bounded geometric tail for `0 <= beta < 1` to state/prove the
   discounted belief-control rewrite at the frozen source boundary;
5. expose source-facing `p_ref_02` only after all three frozen conclusions
   (observation law, belief update law, discounted-control rewrite) are present;
6. semantic/prohibited audit, then clean integration from the then-latest
   full-green main.

Zero-denominator observations must remain an explicit model conflict; never
replace them by an arbitrary posterior extension.

## Parallel lane — P-REF-03

Branch: `formal/pref03-free-information-v1`.
Head: `42683e5f3efe385ccc95d556cf7ffe9b10edfeac`.
CI: `34804496967`.

The implementation preserves the frozen theorem's arbitrary signal-space scope
by representing the information as an arbitrary sub-sigma-algebra. Only the
action set is finite. For integrable action payoffs, the informed pointwise
supremum of conditional expectations dominates every fixed action, and the
conditional-expectation integral identity supplies the value inequality.

If this feature gate is green, run a source/prohibited audit and clean-integrate
only from the then-latest full-green main. Feature green alone does not count.

## Grounded non-quick fronts

- P-ALI-01: global exact-one-form / closed-loop integral theorem on connected smooth manifolds; Euclidean curl-free weakening is forbidden.
- P-DDH-02/03: finite exponential-family calculus and KL variational duality.
- P-KL-04/05: CTMC compensator / Girsanov-level stochastic analysis.
- P-EVO-03/04: Perron--Frobenius asymptotics / martingale foundations.
- P-DDH-04/05: genuine rank/stacked-Jacobian and singular-value perturbation.
- P-QSD-01/03/04: source-locked distinct non-A results.
- P-BRG-01: includes extinction/concentration/maximizer-relative-mass clauses.

P-EVO-03 specifically requires the full K-PF-01 primitive nonnegative-matrix
Perron--Frobenius asymptotic package; do not count an assumed-convergence
surrogate.

## Guards

- do not reopen counted green P-IDs absent source mismatch/CI regression;
- feature green never increments coverage;
- no `sorry`, `admit`, `native_decide`, or unsourced `axiom`;
- preserve frozen source strength; do not replace hard clauses by convenient
  finite/toy/Markov-only surrogates;
- P-QSD-01 and P-QSD-03 must never be swapped;
- P-REF-03 requires arbitrary signal spaces;
- P-DDH-04/05 require genuine rank/singular-value infrastructure;
- P-BRG-01 includes concentration/extinction/maximizer-ratio clauses;
- P-KL-04/05 must remain at their frozen CTMC/Girsanov level.

## Recovery order

1. `UEOT_CORE3_LEAN_OPERATIONS.md`;
2. Issue #56 when available;
3. this `HANDOFF_LATEST.md` snapshot;
4. `PID_STATUS.yaml`;
5. `FORMALIZATION_STATE.md`;
6. `V3_COVERAGE_STATUS.md`;
7. live main/branches/CI reconciliation.
