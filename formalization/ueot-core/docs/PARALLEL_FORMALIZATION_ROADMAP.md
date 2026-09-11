# UEOT Core v3.0 — Parallel Lean Completion Roadmap

This is the execution plan for completing all 106 source P-IDs in
`UEOT_Core_Mathematics_v3.0_Complete.md`.

Live branch/CI state belongs in `FORMALIZATION_STATE.md`; the authoritative
source-level count belongs in `V3_COVERAGE_STATUS.md`.

## 1. Promotion gate

A P-ID is `proved` only after all of the following hold:

1. exact frozen source statement/hypotheses identified;
2. Lean theorem source-faithful or any source correction explicitly audited;
3. theorem reachable from the official `UEOT` target;
4. feature full-target CI green;
5. minimal clean-port onto newest green Lean-affecting `main`;
6. clean-port CI green;
7. PR CI green;
8. serialized main integration;
9. post-main `lake build UEOT` green;
10. no `sorry`, UEOT-specific axiom, `native_decide`, or hidden weakening;
11. authoritative ledgers synchronized.

Helpers and isolated green files do not increment source coverage.

## 2. Current checkpoint

As of 2026-09-12:

- proved: **49**
- partial: **0**
- pending: **57**
- total: **106**
- latest proved P-ID: **P-INV-05**
- current integrated Lean head: `7d52e949b9788a32e3c5ce7ab9eec0f4ad85e58d`
- post-main CI run `34626175917`: success

P-INV-01 through P-INV-05 are closed. P-STAT-06 infrastructure is integrated
but that P-ID remains pending until the exact frozen simultaneous RKHS radius
theorem is closed.

## 3. Branch classes

- **HOT** — actively changing proof lane.
- **PROMOTION** — source-complete minimal clean port waiting for serialized main integration.
- **WARM** — source-audited next packet with no duplicated proof work.
- **ARCHIVE** — merged/superseded/historical evidence only.

Never rebase stale branches merely to make their names look current; clean-port
only the verified source-matched delta.

## 4. Current parallel wave

### Lane A — P-STAT-06 RKHS/MMD concentration [HOT]

Integrated green infrastructure on `main`:

- exact `2/N` one-sample replacement sensitivity;
- centered Hilbert off-diagonal cancellation;
- empirical squared-norm expansion;
- `E||mean Z_i||^2 <= 1/N`;
- exact first-moment bridge `E||mean Z_i|| <= 1/sqrt(N)`;
- conditional-sub-Gaussian Azuma wrapper;
- exact parameter normalization `N*(1/N^2)=1/N`;
- scalar tail `exp(-N*epsilon^2/2)`.

Active source-closure branch: `formal/pstat06-union-closure`.

Current closure sequence:

1. machine-check the finite `L` union wrapper in the exact `alpha/L` form;
2. build the concrete Doob increments for the RKHS norm statistic from the
   `2/N` bounded-difference theorem;
3. prove the conditional Hoeffding/sub-Gaussian increment hypotheses;
4. combine with the first-moment `1/sqrt(N)` term;
5. substitute `t = sqrt(2*log(L/alpha)/N)`;
6. expose exact source-facing
   `max_j ||muHat_j-mu_j|| <= (1 + sqrt(2*log(L/alpha)))/sqrt(N)`;
7. clean promotion, PR CI and post-main verification.

Do not count the integrated infrastructure alone as P-STAT-06.

### Lane B — information packet [WARM]

Open a fresh source audit for P-INFO-02, P-INFO-03 and P-INFO-04. Reuse the
already integrated information/KL/entropy modules and establish one canonical
conditional-information interface rather than creating another entropy stack.

Execution order:

1. identify exact frozen statements and dependency order;
2. map each source notion to the existing `Information*` modules;
3. prove the smallest missing reusable lemmas;
4. expose source-facing wrappers one P-ID at a time;
5. promote independently through the full gate.

### Lane C — P-INT-01 structured sufficiency [WARM]

Start only after the P-INFO audit fixes the canonical conditional-information
interface. Reuse prediction, Markov-boundary and information infrastructure.
The critical rule is to prove the frozen iff/bridge statement rather than a
one-direction surrogate.

### Lane D — next inverse/identifiability packet [WARM]

P-INV-01..05 are now fully promoted. Select the next inverse-family source P-ID
only after a fresh source/dependency audit. Reuse both the Fisher intersection
library and the predictable-OLS concentration library; do not rebuild a second
linear-algebra or concentration stack.

## 5. Next WARM pool

Priority after the current wave:

1. P-INFO-02/03/04;
2. P-INT-01;
3. remaining inverse/identifiability packet after P-INV-05;
4. remaining QSD/persistence theorems, separating finite Perron/Markov results
   from diffusion/spectral analysis;
5. finite implementation/composition packet;
6. finite control/quotient packet before continuous HJB/spectral GOA work;
7. KL/variational/dual-drive packet;
8. evolution/reflexivity/final assembly only after prerequisites are closed.

## 6. Dependency factories for the remaining 57

### Factory G — statistics / inverse problems

P-STAT / P-INV remainder. Reuse finite concentration, Fisher, predictable-OLS,
variation and response-defect infrastructure already on main.

### Factory H — implementation / composition

P-ID / P-OMG / P-COMP remainder. Separate finite hypergraph/Booleanization
proofs from prediction-information parent-emergence claims.

### Factory I — information / structural interfaces

P-INFO / P-INT remainder. One canonical KL/MI/conditional-information layer;
no duplicate entropy stacks.

### Factory J — control / quotient / GOA

Dependency direction is fixed:
process -> predictive state -> dynamic quotient -> policy/value -> GOA.

### Factory K — KL / variational / dual-drive

Separate exact algebraic gauge theorems, finite Markov path-KL, and genuinely
analytic/Girsanov statements.

### Factory L — evolution / reflexivity / final assembly

P-EVO, remaining P-BRG/P-REF, then P-API/P-ALG/P-CORE assembly. Assembly
statements never mask missing prerequisites.

## 7. Concurrency discipline

- one P-ID family owns one module or tight module group;
- feature branches edit `UEOT/V3.lean` only for their own import reachability;
- only synchronization commits edit source-coverage ledgers;
- shared infrastructure is proved and merged once, never duplicated across
  stale branches;
- proof development is parallel; main promotion is serialized;
- aim for 3–5 genuinely independent HOT/WARM lanes, not artificial branch count.

## 8. CI hierarchy

### L1 — feature branch

Compile the official `UEOT`/`UEOT.V3` target with the new module imported.

### L2 — clean promotion

Use newest green Lean-affecting main, minimal delta, full build, source-facing
theorem, semantic audit and prohibited-proof audit.

### L2.5 — PR verification

Run the official full target on the actual PR head/base combination before
integration.

### L3 — post-main

Run the full build/audits. Coverage changes only after success.

## 9. Merge train

For every P-ID:

`source audit -> helpers -> source wrapper -> official import -> feature CI -> clean port -> clean CI -> PR CI -> serialized main integration -> post-main CI -> ledger sync`.

While one lane waits in CI, another lane continues proof development.

## 10. Completion condition

UEOT Core v3.0 is machine-complete only at:

- **106 proved / 0 partial / 0 pending**;
- full `lake build UEOT` green on main;
- source-to-ledger consistency green;
- transitive axiom/prohibited-proof audit green;
- no source P-ID counted through a helper theorem alone.
