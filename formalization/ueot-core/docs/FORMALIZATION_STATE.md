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

## Current counted checkpoint

| operational state | count |
|---|---:|
| integrated proved, staged by this checkpoint | **70** |
| promotion-ready / integration lane | **1** |
| blocked | **0** |
| pending/unclassified | **35** |
| total | **106** |

The previous authoritative full-green checkpoint is **69/106**. This recovery
branch stages **70 proved / 36 not yet counted** after P-KL-02 completed all
proof-side and post-main gates. It must itself pass PR CI, land on `main`, and
pass the resulting main CI before 70/106 is called full-green.

The one promotion-ready lane is P-API-01. It is feature-green but **not counted**.

## Newly staged proof — P-KL-02

Frozen source §22.2 is implemented literally over every probability law
`Q ≪ P0` with `Q(A) ≥ p`, with `q=P0(A)`, `0<q<1`, `0≤p≤1`.

The source-facing theorem exposes both cases:

- `p≤q`: infimum `0`, attained by the baseline `P0`;
- `p>q`: infimum exactly `dBern(p||q)`, attained by the explicit RN tilt
  `(p/q)1_A + ((1-p)/(1-q))1_{Aᶜ}`.

The optimizer is proved to be a probability law, absolutely continuous with
respect to `P0`, to have event mass exactly `p`, to have the required RN
derivative, and to have exact KL cost. The `p=1` endpoint is retained.

Evidence:
- theorem `UEOT.V3.PathEventIProjection.p_kl_02`;
- full feature `formal/pkl02-event-iprojection@cb78b0df87ef64fc0bc61e1e320ff901247d00cd`;
- feature CI `34768634473`: success;
- clean integration `formal/pkl02-clean-int-cb78@d30d31e15f38b349488edf4a5b12c94bace70031`;
- PR #62 CI `34769135038`: success;
- proof main commit `60ac78273200f5152a5e8d8286c840697e69bb51`;
- post-main CI `34769394882`: success;
- source semantic audit complete;
- prohibited-proof audit clean.

## Previous full-green checkpoint — 69/106

P-EVO-02 is fully counted. Its feature, clean-integration, proof post-main, and
ledger gates are green; the later recovery checkpoint
`main@e3f046fcf4096a1bb6acb561afe1e31244e3aaad` passed CI `34767624927`.
Do not reopen P-EVO-02 absent a substantive source mismatch or regression.

## Promotion-ready lane — P-API-01

Frozen §28.3 exact/approximate process-interface composition has a feature-green
proof on:

- `formal/papi01-process-interface-fresh@0f76d04a4dcc34b2d2aaa806d5803e4823561bbc`;
- feature CI `34769177051`: success.

The implementation types exactly the frozen process interface: a protocol lift,
a measurable path readout, and naturality of path-law pushforward for all
declared protocols. Exact interfaces compose exactly. Approximate TV defects
compose with bound `min 1 (εAB + εBC)` by P-MET-01 plus triangle inequality.
Control actions, policy lifting, rewards and constraints are intentionally not
added here because frozen §28.4 requires those as extra control-interface data.

The feature diff is `UEOT/V3/ProcessInterface.lean` plus one top-level import and
its prohibited-proof audit is clean. It must be clean-integrated only after the
70/106 ledger checkpoint is full-green.

## Independent source audit — P-ALG-01

Frozen §28.5 is an exact finite-state partition-refinement algorithm. The source
requires finite termination, controlled stability, coarsest stable refinement,
preservation of outputs/rewards/all-action one-step quotient laws, and all
corresponding finite-horizon output laws. Mathlib provides `Finpartition` /
refinement infrastructure but no complete UEOT implementation currently exists.
No approximate floating-point grouping may be substituted for the exact theorem.

## Grounded non-quick fronts

- P-ALI-01: global exact-one-form / closed-loop integral theorem on connected smooth manifolds; Euclidean curl-free weakening is forbidden.
- P-DDH-02/03: finite exponential-family calculus and KL variational duality.
- P-KL-04/05: CTMC compensator / Girsanov-level stochastic analysis.
- P-EVO-03/04: Perron--Frobenius asymptotics / martingale foundations.
- P-REF-03: arbitrary signal-space conditional expectation.
- P-DDH-04/05: genuine rank/stacked-Jacobian and singular-value perturbation.
- P-QSD-01/03/04: source-locked distinct non-A results.
- P-BRG-01: includes extinction/concentration/maximizer-relative-mass clauses.

P-EVO-03 specifically requires the full K-PF-01 primitive nonnegative-matrix
Perron--Frobenius asymptotic package. Do not count an assumed-convergence
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
