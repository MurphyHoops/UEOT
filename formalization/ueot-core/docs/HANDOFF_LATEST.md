# UEOT Core 3 Lean — Latest Handoff

> Dynamic construction-site state. Read this after `UEOT_CORE3_LEAN_OPERATIONS.md`, then verify all SHAs and CI statuses against live GitHub before acting.

updated: `2026-09-13T16:59+08:00`

## Canonical project state

- repo: `MurphyHoops/UEOT`
- integration branch: `main`
- frozen source: `UEOT_Core_Mathematics_v3.0_Complete.md`
- source P-IDs: `106`
- official target: `lake build UEOT`
- Lean: `4.33.1`
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- live main checked for this handoff: `4c2e20e493e0137c90fc0229f73cdc95ae3a29a0`
- counted coverage: `54/106`

Coverage must remain 54/106 until P-INT-01 is clean-integrated into latest main, post-main CI is green, and ledgers are synchronized.

## Active P-ID — P-INT-01

Core 3 source-facing scope:

- general Standard-Borel variables;
- `H=(H^S,H^E)`;
- `M=f(H^S)`;
- `U=g(H^E)`;
- `Z=(M,U)`;
- predictive closure / conditional independence iff canonical predictive law factors through `Z`;
- countable intervention/protocol family uses one common version/common conull set.

Feature branch: `formal/pint01-factorization-iff`

Verified feature head: `3943391af4d459a370ab840d1b15babcae26f82a`

Latest official full-target CI: `34747270058` — **success**.

At this checkpoint feature vs main: ahead 24, behind 1. Do NOT merge the long development history wholesale.

## Final validated delta

Only these 7 target files are required for clean integration:

1. `formalization/ueot-core/UEOT.lean`
2. `formalization/ueot-core/UEOT/V3/InformationPInt01.lean`
3. `formalization/ueot-core/UEOT/V3/InformationPInt01Common.lean`
4. `formalization/ueot-core/UEOT/V3/InformationPredictiveFactorization.lean`
5. `formalization/ueot-core/UEOT/V3/InformationPredictiveFactorizationCanonical.lean`
6. `formalization/ueot-core/UEOT/V3/InformationPredictiveFactorizationForward.lean`
7. `formalization/ueot-core/UEOT/V3/InformationPredictiveFactorizationReverse.lean`

Machine-checked content already green:

- generic Standard-Borel factorization framework;
- canonical predictive-law / regular-conditional bridge;
- witness canonicalization through `P(Y|Z)`;
- forward implication;
- reverse implication;
- structured single-protocol theorem;
- countable common-protocol/common-conull-set theorem;
- common measurable decoder packaging.

Do not reprove these absent a real frozen-source mismatch or regression.

## Important pinned API facts

- P-INT-01 must remain general Standard-Borel; do not import P-INFO-03's discrete/countable core restriction.
- Source `Psi : Z -> P(Y)` is represented by a Markov kernel `Kernel Z Y`.
- Reuse pinned Mathlib conditional-independence infrastructure, including `condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight` where applicable.
- The successful protocol-joint conditional-kernel route uses disintegration/conditional-kernel uniqueness; do not rely on a guessed unavailable `Measure.condKernel_compProd` name.
- For pinned `Kernel.prodMkRight`, use explicit argument order such as `Kernel.prodMkRight H q0` when type inference is ambiguous.
- Structured `M` and `U` need the required Standard-Borel assumptions.
- Reuse existing `PredictionAE` common-factorization/common-version infrastructure rather than duplicating it.

## Exact next action

The P-INT-01 feature lane is frozen. Next chat should immediately perform clean integration:

1. fetch live latest `main`;
2. inspect/use `formal/pint01-main-integration`; if stale, recreate a clean branch from latest main;
3. replay only the 7 validated files above and preserve main-only imports;
4. compare integration vs main for unrelated changes/accidental deletions;
5. prohibited-proof audit: `sorry`, Lean `admit`, `native_decide` used as bypass, unsourced axioms;
6. run full `lake build UEOT` on integration;
7. if green, integrate to `main` with clean history;
8. run post-main full CI;
9. only if post-main is green, synchronize `PID_STATUS.yaml`, `V3_COVERAGE_STATUS.md`, `FORMALIZATION_STATE.md`, and this file;
10. then promote `54/106 -> 55/106`.

If integration fails, fix only the first real integration/compiler error. Do not reopen already-green mathematical architecture unless the failure proves a real semantic dependency problem.

## Immediately after P-INT-01

Do a full source-to-main audit of the remaining 51 currently unclassified P-IDs before opening many new proof stacks.

Classify each:

- A: source-facing theorem already exists on main;
- B: substantial proof exists, wrapper/alignment gap;
- C: bridge theorem missing;
- D: genuinely new mathematics required.

Prioritize A -> B -> C -> D, adjusted by dependency unlock and reuse value. Maintain `PID_AUDIT_MATRIX.yaml` and `LEAN_API_NOTES.md` as the audit/engineering knowledge base.

## Efficiency rule

Use:

`module check -> affected-stack check -> milestone full CI`.

Do not use GitHub full CI as a Lean REPL. Feature green should transition directly to clean integration rather than accumulating speculative improvements.

## Reconciliation note

At this handoff, `PID_STATUS.yaml` and `FORMALIZATION_STATE.md` still contain an older P-INT-01 head/CI snapshot. Those stale fields must not override live GitHub or this handoff. The next valid promotion should synchronize them.

If a new chat finds different live GitHub SHAs/CI, live GitHub wins and this file should be refreshed after reconciliation.
