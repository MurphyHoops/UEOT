# UEOT Core v3.0 — Parallel Lean Completion Roadmap

This is the execution plan for completing all 106 frozen source P-IDs in
`UEOT_Core_Mathematics_v3.0_Complete.md`.

Machine-readable live state belongs in `PID_STATUS.yaml`. Human recovery state
belongs in `FORMALIZATION_STATE.md`. The authoritative integrated source count
belongs in `V3_COVERAGE_STATUS.md`.

## 1. Promotion gate

A P-ID is counted `proved` only after: exact source audit, source-faithful Lean
closure, official import reachability, feature full-target CI, minimal clean
port, clean-port CI, PR CI, serialized `main` integration, post-main
`lake build UEOT`, prohibited-proof audit, and ledger synchronization.

The exact frozen source artifact is still absent from the public repository, so
mathematically complete information P-IDs remain uncounted until their final
literal source-match gate can be executed against the canonical bytes/hash.

## 2. Current checkpoint — 2026-09-12

- integrated proved: **50/106**
- P-STAT-06: **PROVED/CLOSED**
- P-INFO-02: **mathematically complete; source-artifact blocked**
- P-INFO-04: **PROOF; multiway integrated, conditional binary active**
- P-INFO-03: **SOURCE_AUDIT**
- P-INT-01: **BLOCKED** on the canonical conditional-information bridge

## 3. Priority lanes

### Lane A — P-INFO-04 conditional binary [highest priority]

The multiway sharp Fano theorem is already integrated on `main` and passed
post-main CI. Do not reopen it.

Active branch: `formal/pinfo04-conditional-binary`.

Completed layers:

1. true disintegration `P(M,B|U)`;
2. fiberwise reference `P(M|U)×P(B|U)`;
3. genuine binary conditional entropy `H(B|U)`;
4. arbitrary-decoder sharp pointwise Fano;
5. arbitrary-decoder conditional Fano after integration and Jensen;
6. source geometry `(U,(M,B)) -> ((U,M),B)`;
7. posterior `P(B|U,M)`;
8. source epsilon inequality `H(B|M,U) <= h2(epsilon)` under
   `P_e <= epsilon <= 1/2`.

Remaining source-critical work:

1. machine-check the latest source-facing stack in the official graph;
2. prove the finite-binary information identity
   `I(M;B|U)=H(B|U)-H(B|M,U)` without introducing an `∞-∞` subtraction;
3. derive the frozen lower bound
   `I(M;B|U) >= H(B|U)-h2(epsilon)`;
4. clean-port only the verified delta from latest `main`;
5. clean CI -> PR -> main -> post-main.

Do not make a fully general extended-real kernel-KL decomposition a prerequisite
unless the finite-binary bridge genuinely needs it. The binary entropy route is
both source-faithful and mathematically safer.

### Lane B — P-INFO-02 [no further proof work]

Canonical theorem:
`UEOT.V3.InformationPInfo02.p_info_02_ennreal`.

The predictive-kernel/Pinsker/Jensen chain is complete, imported, merged, and
post-main green. The all-cases theorem includes infinite conditional
information. Do not reopen Pinsker, kernel KL, or wrapper layers.

The only remaining gate is repository synchronization of the exact frozen
source bytes followed by literal statement/hash audit. `[Nonempty Y]` is a
Mathlib disintegration implementation requirement that is mathematically
implied by existence of the probability experiment; do not spend another proof
lane on hiding this typeclass from theorem elaboration.

### Lane C — P-INFO-03 [next mathematical lane]

Start only after the P-INFO-04 binary conditional interface is stable.

Target:
`R_obj(0)=H(C|U)` for countable-discrete predictive core `C`, allowing random
encoders.

Build by extending, not duplicating, the conditional disintegration stack:

1. countable-discrete conditional entropy `H(C|U)` as an actual fiber average;
2. measurability/integrability of the entropy fibers under the source
   finite-conditional-entropy hypothesis;
3. random-encoder predictive rate-distortion interface;
4. zero-TV recoverability of `C` from `(M,U)`;
5. conditional DPI lower bound;
6. attainability with `M=C`.

Do not define `H(C|U)` as `H(C)-I(C;U)` in the general source theorem.

### Lane D — P-INT-01 [blocked, then immediately next]

Once P-INFO-03/P-INFO-04 establish one canonical conditional-information
interface, use that interface for the frozen conditional-independence iff/bridge.
Do not create a second KL/entropy/independence stack.

### Lane E — remaining pending families [source-audit pool]

While a proof lane waits on CI, source-audit one additional P-ID family, but do
not begin implementation until its exact proof contract and reuse map are
recorded in `PID_STATUS.yaml`.

Prefer families that reuse already integrated machinery over new foundational
stacks. Main promotion remains serialized even when proof development is
parallel.

## 4. Concurrency model

The productive parallel layout from this checkpoint is:

- **Thread 1:** P-INFO-04 conditional source closure;
- **Thread 2:** P-INFO-03 countable-discrete source/dependency audit;
- **Thread 3:** governance/source-artifact synchronization and exact-hash gate;
- **Thread 4:** one carefully selected remaining P-ID source audit only.

Do not run four independent foundational implementations. The purpose of
parallelism is to hide CI/audit latency while preserving one canonical
information-theory stack.

## 5. Merge train

`source audit -> proof contract -> missing lemmas only -> canonical source theorem -> official import -> feature CI -> clean port -> clean CI -> PR CI -> serialized main integration -> post-main CI -> exact-source check -> ledger sync`.

Helpers, unimported modules, feature-green branches, or mathematically equivalent
but source-mismatched statements do not increment coverage.

## 6. Stop conditions / anti-duplication rules

- P-STAT-06 is frozen closed.
- P-INFO-02 proof infrastructure is frozen unless a real CI regression or
  source mismatch appears.
- P-INFO-04 multiway direct Fano is frozen integrated; only the conditional
  clause remains active.
- No posterior/MAP replacement may be used to weaken arbitrary-decoder Fano.
- No second conditional-information formalism may be created for P-INT-01.
- No regenerated substitute may stand in for the canonical frozen source file.

## 7. Completion condition

UEOT Core v3.0 is machine-complete only at **106 proved / 0 partial / 0 pending**,
with full `lake build UEOT` green on `main`, exact source-to-ledger consistency,
transitive prohibited-proof/axiom audit green, and no P-ID counted through a
helper theorem alone.
