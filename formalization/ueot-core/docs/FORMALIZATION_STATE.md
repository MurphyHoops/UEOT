# UEOT Core Lean — Live Formalization State

> Recovery entry point. Machine-readable lane state is `PID_STATUS.yaml`.
> Integrated source-count truth is `V3_COVERAGE_STATUS.md`. GitHub Issue #56
> carries the live cross-chat construction log when available.

Last synchronized: **2026-09-14**

## Environment

- canonical source: `UEOT_Core_Mathematics_v3.0_Complete.md`
- source P-IDs: **106**
- canonical source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`
- Lean: **4.33.1**
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- official target: `lake build UEOT`
- integration branch: `main`
- exact canonical bytes in public repo: pending synchronization

## Current staged checkpoint

| operational state | count |
|---|---:|
| integrated proved, staged by this checkpoint | **73** |
| active proof | **2** |
| source audit | **0** |
| blocked | **0** |
| pending/unclassified | **31** |
| total | **106** |

The authoritative full-green baseline before this ledger branch is **72/106** at
`main@8d3124b03b6e04cdde8fc5c42d76751967d043c1`, CI `34795931776` success.
P-REF-01 has completed all proof-side gates and this branch stages 73/106. Do
not call 73/106 full-green until this ledger branch passes PR CI, lands on
`main`, and the resulting main CI succeeds.

## Newly staged proof — P-REF-01

Frozen §27.1 is implemented without a deterministic-policy or Markov-policy
weakening. The source-facing theorem surface is:

- `UEOT.V3.ReflexivePRef01.p_ref_01`;
- `UEOT.V3.ReflexivePRef01.p_ref_01_structureModification`;
- `UEOT.V3.ReflexivePRef01.p_ref_01_compression_closure_iff_kernel`;
- `UEOT.V3.ReflexivePRef01.p_ref_01_compression_closure_iff_pathLaw`.

The construction uses arbitrary history-dependent randomized causal policies,
pinned Mathlib Ionescu--Tulcea trajectory kernels, recursive finite-history laws,
and projective-limit uniqueness. The structural update
`S_{t+1}=F(S_t,X_t,a_t,xi_t)` is a specialization through a measurable
noise-driven controlled kernel; it does not restrict the policy. Compression
closure remains a separate action-wise strong-lumpability obligation.

Evidence:
- strengthened feature `formal/pref01-source-assembly-v2@8649c0763ac2326177812209bab3f32ad92680f7`;
- feature CI `34803657950`: success;
- clean integration `formal/pref01-main-integration-v1@85148ee2e9cba8afa5e23406a51c09515d45e052`;
- PR #69 CI `34804007035`: success;
- proof main `1c4de9fc60b653e8c3594bba1a01a0eed510578a`;
- proof post-main CI `34804335400`: success;
- frozen-source semantic audit: complete;
- prohibited-proof audit: clean.

The source-facing result is valid on arbitrary measurable spaces once the
supplied kernels are Markov. Core 3 globally defaults random-variable spaces to
Standard Borel, so this is theorem-strengthening rather than source weakening.

## Active proof — P-REF-02

Frozen §27.2 requires all of the following in a finite `Theta × X` model:

- predictive next-state and next-observation laws;
- the exact Bayes posterior on positive evidence;
- zero evidence returns `modelConflict` rather than an arbitrary posterior;
- the next observation law and updated-belief law depend only on `(b_t,a_t)`;
- bounded discounted tasks can be rewritten as a belief-state control problem.

Current branch: `formal/pref02-belief-core-v1`.

Green evidence so far:
- finite Bayes core head `322938a5352814c1fe5c6bf095e4a5e40e627b4e`;
- CI `34804267113`: success.

Current second layer:
- head `871a33cb831148c655d7f4a1d708b58843ffff09`;
- adds normalized observation law and `(b,a)`-determined `BeliefStep`;
- CI `34804586631` is the current feature gate.

The bounded-discount control rewrite is not yet discharged and P-REF-02 remains
uncounted.

## Parallel proof — P-REF-03

Frozen P-REF-03 requires arbitrary signal spaces, finite actions, and integrable
payoffs. The branch `formal/pref03-free-information-v1` represents information
by an arbitrary sub-sigma-algebra and proves the informed pointwise maximum of
conditional expected payoffs dominates every fixed action. No finite-signal
surrogate is used.

Current head: `42683e5f3efe385ccc95d556cf7ffe9b10edfeac`.
Current CI: `34804496967`.

Feature green does not increment coverage.

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

## Mandatory recovery procedure

1. Read `UEOT_CORE3_LEAN_OPERATIONS.md`, Issue #56 if available,
   `PID_STATUS.yaml`, this file, then `V3_COVERAGE_STATUS.md`.
2. Fetch live main, active branches and Actions state.
3. Never reopen counted green P-IDs without a substantive source mismatch or CI regression.
4. Read the frozen source before writing Lean and audit existing main first.
5. Feature green never increments coverage.
6. No `sorry`, `admit`, `native_decide`, unsourced `axiom`.
7. Use CI waiting time for another independent audit/proof lane.
