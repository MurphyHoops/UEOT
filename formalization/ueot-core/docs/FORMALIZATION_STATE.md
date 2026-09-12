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
| integrated proved | **52** |
| active proof | **1** |
| source audit | **0** |
| blocked | **1** |
| pending unclassified | **52** |
| total | **106** |

The authoritative source-level ledger is now **52 proved / 54 pending**.

This corrects a governance conflation that had kept the count artificially at
50: source-theorem proof status and public-repository source-artifact
reproducibility are separate properties. P-INFO-02 and P-INFO-04 were directly
re-audited against the canonical source object and already had source-faithful
main theorems with green post-main CI, so they are now counted proved. The exact
canonical Markdown bytes still need to be synchronized into the public repo so
third parties can independently recompute the frozen SHA-256.

Audit evidence:
`docs/SOURCE_AUDIT_EVIDENCE_2026-09-13.md`.

## P-STAT-06 [PROVED / CLOSED]

Canonical theorem:
`UEOT.V3.HilbertMeanSourceFeatureRaw.source_feature_tail_exact_radius_raw_assumptions`.

Promotion evidence: PR #40, main `d17d0e78ec7bf9cd35b1d314afa93aaeecdcb092`,
post-main CI `34685534516` success. Do not reopen absent a real CI regression or
source mismatch.

## P-INFO-02 [PROVED / COUNTED]

Frozen target:

`E TV(P(Y|H), P(Y|M,U)) <= sqrt(I(H;Y|M,U)/2)`.

The predictive-kernel/Pinsker/Jensen chain is complete, imported and integrated.
Canonical theorem:
`UEOT.V3.InformationPInfo02.p_info_02_ennreal`.

Promotion evidence:

- canonical source semantics re-audited on 2026-09-13;
- all-cases PR #46;
- main `c1d0d94b7d01a5d6f370d2de4f40e8c1674bcd8f`;
- post-main CI `34692828935`: success.

`[Nonempty Y]` is a Mathlib `condKernel` statement-elaboration requirement,
not an extra physical assumption; existence of the probability law on `H×Y`
implies nonemptiness.

Public source artifact synchronization remains pending only as a reproducibility
task. Do not reopen the proof stack absent a real source mismatch or CI
regression.

## P-INFO-04 [PROVED / COUNTED]

P-INFO-04 contains two frozen source clauses and both are closed in Lean and
re-audited against the canonical source object.

### Multiway sharp Fano

Canonical theorem:
`UEOT.V3.InformationPInfo04.p_info_04`.

The proof uses the actual correctness event and KL data processing:

`KL(P_JY || P_J⊗P_Y)` → correctness-event Bernoulli KL → exact sharp Fano.

No MAP substitution is used. Promotion evidence: PR #47, main
`94e16dfb9cc9a2db6e000d8f5394c1b07869ce40`, post-main CI `34693509298`
success.

### Conditional binary source clause

Frozen target:

`I(M;B|U) >= H(B|U) - h2(epsilon)`

for a measurable decoder with error `P_e <= epsilon <= 1/2`.

Canonical theorem:
`UEOT.V3.InformationConditionalBinaryMutualEntropy.p_info_04_conditional_binary`.

Machine-checked architecture:

1. genuine disintegration `P(M,B|U)` and fiber independence reference;
2. arbitrary-decoder sharp Fano at the actual decoded index;
3. binary posterior absolute continuity;
4. exact `Fin 2` KL scalarization, including reference probabilities 0 and 1;
5. posterior mean/tower identity;
6. unconditional binary `I(X;B)=H(B)-H(B|X)` and finite fiber MI;
7. nested disintegration over `U` and `M`;
8. global conditional KL decomposition into fiber mutual informations;
9. posterior-entropy Fubini lift;
10. finite bridge `I(M;B|U)=ofReal(H(B|U)-H(B|M,U))`;
11. separate `CMI=top` branch, so no finite-CMI source assumption is added.

Verification evidence:

- compose CI `34705230951`: success;
- clean branch `formal/pinfo04-conditional-clean-v2`;
- clean commit `8c76777e78e8d7f73b0d71397f8c81aeaa6e9c54`;
- clean CI `34705560077`: success;
- PR #51 CI `34706303512`: success;
- main merge `e19eee7082418f1826650316b533c0380a9a451f`;
- post-main CI `34706528781`: success.

`[Nonempty M]` is a Mathlib `condKernel` elaboration requirement implied by
existence of the source probability law, not a new physical axiom.

**No further P-INFO-04 proof work is allowed** unless a real regression or
source mismatch appears. Public source-byte synchronization remains a separate
reproducibility task.

## P-INFO-03 [ACTIVE PROOF]

Frozen target:
`R_obj(0)=H(C|U)` for discrete
`C=P(Y∈·|H,U)` with `H(C|U)<∞`, allowing random encoders
`P(M|H,U)` that cannot access future `Y`.

The exact source proof is:

1. zero average TV implies the predictive core `C` is recoverable from `(M,U)`;
2. conditional data processing gives
   `I(H;M|U) >= I(C;M|U)=H(C|U)`;
3. attainability is achieved by `M=C` with decoder outputting the canonical
   predictive kernel.

Current verified foundation:

- `UEOT.V3.InformationConditionalDiscreteEntropy` defines genuine countable
  conditional entropy through `U`-disintegration and a measurable ENNReal
  singleton-probability Shannon `tsum`;
- official full-target CI `34706765170`: **success**.

Current active construction:

- generic KL conditional mutual information interface;
- generic conditional KL fiber decomposition;
- random-encoder joint-law geometry at kernel level;
- recoverable countable-discrete information identity;
- compatibility bridge from the new fiber Shannon `tsum` to the existing
  `discreteShannonEntropy` representation.

Active branch: `formal/pinfo03-countable-conditional`.
Latest known head: `9a152cace0831cca498cdf489a06466b36cf2e98`.
Generic-CMI CI `34707351959` is the current diagnostic run; an isolated branch
`formal/pinfo03-generic-cmi-isolated` independently validates that layer so
later downstream failures cannot obscure its status.

Remaining source-critical obligations:

1. machine-check generic conditional mutual information and KL decomposition;
2. prove exact compatibility between fiber Shannon `tsum` and existing
   `discreteShannonEntropy`;
3. machine-check the random-encoder joint law;
4. formalize the zero-TV predictive-core identification/recoverability bridge;
5. prove the conditional DPI lower bound;
6. prove attainability and expose the exact source-facing `R_obj(0)` theorem;
7. clean-port -> clean CI -> PR -> main -> post-main.

## P-INT-01 [BLOCKED]

Frozen target is the structured-sufficiency iff bridge
`Y_f^+ ⟂ H | (M,U) ↔ C^f = Ψ(M,U) a.s.`. It remains blocked on the **general
countable conditional-information interface** being completed by P-INFO-03.
Do not create a duplicate independence/KL stack.

## Public canonical-source synchronization [REPRODUCIBILITY TASK]

The exact canonical bytes are not yet present in the public repository. This is
still required for a fully self-contained third-party reproduction package:

1. copy the exact canonical bytes without regeneration;
2. independently recompute SHA-256;
3. verify equality to
   `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`.

This task is **not** a mathematical proof obligation and no longer suppresses a
P-ID that has otherwise passed direct canonical source audit and the complete
Lean promotion chain.

## Execution order from this checkpoint

1. Finish P-INFO-03 as one coherent proof chain; do not split into competing
   information-theory stacks.
2. Reuse its general conditional-information interface to unblock P-INT-01.
3. In parallel, perform a full source-to-main audit of the remaining 52
   unclassified P-IDs to distinguish already-integrated source-facing theorems
   from genuine missing mathematics.
4. Keep public canonical-source synchronization as a separate reproducibility
   lane; never fabricate or regenerate the canonical file.
5. Promote P-IDs only after exact semantic source matching and full main CI
   evidence; do not optimize for easy counts.

## Mandatory recovery procedure

1. Read `PID_STATUS.yaml`, then this file, then `V3_COVERAGE_STATUS.md`.
2. Fetch current `main` SHA and relevant Actions runs.
3. Distinguish mathematical completion, source semantic audit, official import
   reachability, CI green, main integration, post-main green, and public source
   artifact reproducibility.
4. Read the frozen source contract before writing Lean.
5. Prove only missing obligations and reuse integrated infrastructure.
6. New proof modules must be reachable from `UEOT` / `UEOT.V3`.
7. Feature green is not coverage; count only after the complete source-theorem
   promotion chain passes.
8. While CI runs, use time on another real proof gap or source audit.
9. If documentation and merged green Lean disagree, repair documentation before
   opening another independent proof stack.

## Repository truth hierarchy

1. frozen canonical source specification;
2. `docs/V3_COVERAGE_STATUS.md` — counted integrated proof coverage;
3. `docs/PID_STATUS.yaml` — machine-readable per-P-ID state;
4. `docs/SOURCE_AUDIT_EVIDENCE_2026-09-13.md` — current external-source audit record;
5. `docs/FORMALIZATION_STATE.md` — human recovery state;
6. `UEOT/V3.lean` — official import reachability;
7. `docs/PARALLEL_FORMALIZATION_ROADMAP.md` — execution order.
