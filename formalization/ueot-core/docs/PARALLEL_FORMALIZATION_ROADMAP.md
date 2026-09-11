# UEOT Core v3.0 — Parallel Lean Completion Roadmap

This is the execution plan for completing all 106 source P-IDs in
`UEOT_Core_Mathematics_v3.0_Complete.md`.

Live branch/CI state belongs in `FORMALIZATION_STATE.md`; the authoritative
source-level count belongs in `V3_COVERAGE_STATUS.md`.

## 1. Promotion gate

A P-ID is `proved` only after all of the following hold:

1. exact frozen source statement/hypotheses identified;
2. Lean theorem source-faithful or explicitly stronger;
3. theorem reachable from the official `UEOT` target;
4. feature full-target CI green;
5. minimal clean-port onto newest green Lean-affecting `main`;
6. clean-port CI green;
7. serialized main integration;
8. post-main `lake build UEOT` green;
9. no `sorry`, UEOT-specific axiom, `native_decide`, or hidden weakening;
10. authoritative ledgers synchronized.

Helpers and isolated green files do not increment source coverage.

## 2. Current checkpoint

As of 2026-09-11:

- proved: **48**
- partial: **0**
- pending: **58**
- total: **106**
- latest proved P-ID: **P-INV-03**
- current integrated Lean head containing P-INV-03 and P-STAT-06 infrastructure:
  `dd77d56dd2c5d35440e4f3023ac7a22ab94830c3`
- post-main CI run `34576124342`: success

P-INV-03 is closed. P-STAT-06 infrastructure is integrated but the P-ID remains
pending until the exact frozen simultaneous RKHS radius theorem is closed.

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

1. machine-check finite `L` union wrapper in the exact `alpha/L` form;
2. build the concrete Doob increments for the RKHS norm statistic from the
   `2/N` bounded-difference theorem;
3. prove the conditional Hoeffding/sub-Gaussian increment hypotheses;
4. combine with the first-moment `1/sqrt(N)` term;
5. substitute `t = sqrt(2*log(L/alpha)/N)`;
6. expose exact source-facing
   `max_j ||muHat_j-mu_j|| <= (1 + sqrt(2*log(L/alpha)))/sqrt(N)`;
7. clean promotion and post-main verification.

Do not count the integrated infrastructure alone as P-STAT-06.

### Lane B — P-INV-05 predictable-design OLS concentration [HOT]

Active branch: `formal/pinv05-predictable-ols`.

Frozen target:
`||thetaHat-thetaStar||_2 <= (sigma*B/kappa) * sqrt(2*d*log(2*d/alpha)/N)`
except on an event of probability at most `alpha`.

Green layers:

- matrix-free Gram action/quadratic identity;
- finite-dimensional Cauchy-Schwarz;
- deterministic normal-equation/coercivity bound
  `(N*kappa)^2 ||err||_2^2 <= ||Z||_2^2`;
- coordinate threshold `|Z_j| <= R` implies `||Z||_2^2 <= d*R^2`;
- deterministic squared-error threshold bridge.

Under current CI:

- one-coordinate two-sided sub-Gaussian tail;
- finite-`d` union bound;
- failure-budget wrapper.

Critical remaining source bridge:

1. for predictable random multiplier `phi_tj` measurable with respect to
   `F_{t-1}`, prove `phi_tj * xi_t` is conditionally sub-Gaussian with parameter
   bounded by `(sigma*B)^2` from `|phi_tj| <= B`;
2. sum the conditional parameters to `N*(sigma*B)^2`;
3. instantiate the coordinate union bound with the exact
   `sqrt(2*N*(sigma*B)^2*log(2d/alpha))` score threshold;
4. feed that threshold into the deterministic Gram bound;
5. simplify to the frozen Euclidean rate and expose `p_inv_05`;
6. clean-port onto latest main and promote.

Important semantic guard: the predictable multiplier is random/adapted, not a
constant design coefficient. Mathlib's constant-scaling sub-Gaussian lemma
cannot be used as a silent replacement for this bridge.

### Lane C — information/structural interfaces [WARM]

Next independent lane after a source audit:

- P-INFO-02/03/04 first, reusing the already integrated information/KL/entropy
  layer;
- then P-INT-01 structured sufficiency iff, reusing prediction and information
  modules rather than defining a second conditional-independence stack.

This lane may be opened while A/B compile because it has low code ownership
conflict.

## 5. Next WARM pool

Priority after the current wave:

1. remaining inverse/identifiability packet after P-INV-05;
2. P-INFO-02/03/04;
3. P-INT-01;
4. remaining QSD/persistence theorems, separating finite Perron/Markov results
   from diffusion/spectral analysis;
5. finite implementation/composition packet;
6. finite control/quotient packet before continuous HJB/spectral GOA work;
7. KL/variational/dual-drive packet;
8. evolution/reflexivity/final assembly only after prerequisites are closed.

## 6. Dependency factories for the remaining 58

### Factory G — statistics / inverse problems

P-STAT / P-INV remainder. Reuse finite concentration, Fisher, variation and
response-defect infrastructure already on main.

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
- only main synchronization commits edit source-coverage ledgers;
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

### L3 — post-main

Run full build/audits. Coverage changes only after success.

## 9. Merge train

For every P-ID:

`source audit -> helpers -> source wrapper -> official import -> feature CI -> clean port -> clean CI -> serialized main integration -> post-main CI -> ledger sync`.

While one lane waits in CI, another lane continues proof development.

## 10. Completion condition

UEOT Core v3.0 is machine-complete only at:

- **106 proved / 0 partial / 0 pending**;
- full `lake build UEOT` green on main;
- source-to-ledger consistency green;
- transitive axiom/prohibited-proof audit green;
- no source P-ID counted through a helper theorem alone.
