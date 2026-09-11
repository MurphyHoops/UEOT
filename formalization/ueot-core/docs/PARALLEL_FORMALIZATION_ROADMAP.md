# UEOT Core v3.0 — Parallel Lean Completion Roadmap

This is the execution plan for completing all 106 source P-IDs in
`UEOT_Core_Mathematics_v3.0_Complete.md`.

Live branch/CI state belongs in `FORMALIZATION_STATE.md`; the authoritative
source-level count belongs in `V3_COVERAGE_STATUS.md`.

## 1. Non-negotiable promotion gate

A P-ID is `proved` only when all of the following hold:

1. the exact frozen source statement and hypotheses are identified;
2. the Lean theorem has the same semantics or explicitly stronger assumptions;
3. the source-facing theorem is reachable from the official `UEOT` target;
4. feature-branch full-target CI is green;
5. the proof is clean-ported onto the newest green Lean-affecting `main`;
6. clean-port CI and PR CI are green;
7. the PR is serialized into `main`;
8. post-main `lake build UEOT` is green;
9. there is no `sorry`, UEOT-specific axiom, `native_decide`, or hidden source weakening;
10. only then are the two state ledgers synchronized.

A helper theorem, isolated green file, or mathematically plausible sketch never
increments coverage.

## 2. Current checkpoint

As of 2026-09-11:

- proved: **46**
- partial: **0**
- pending: **60**
- total: **106**
- latest proved P-ID: **P-INV-02**
- latest Lean-affecting proved checkpoint: `cbfe8eff494a558f113d2e79136655b9ddb61ca7`
- current main may be ahead by docs-only synchronization commits; that does not
  invalidate a clean proof branch based on the same Lean tree.

## 3. Branch classes

The repository contains many historical `formal/**` branches. They are not all
active work.

- **HOT** — actively changing proof lane, expected to merge.
- **PROMOTION** — source-complete clean port in the serialized merge train.
- **WARM** — next packet selected after source audit, no duplicated proof work.
- **ARCHIVE** — merged, superseded, or historically useful only.

A stale branch is never rebased merely to make its name look current. Reuse its
lemmas by clean-porting only the source-matched minimal delta.

## 4. Current parallel wave

### Lane A — P-INV-04 promotion [PROMOTION]

Branch: `formal/pinv04-promote`

Frozen claim: in the noiseless full-parameter linear model, the fixed design
uniquely identifies the parameter iff its Gram matrix is positive definite.

Current implementation uses the equivalent quadratic form
`sum_t (phi_t^T v)^2`; `p_inv_04` proves injectivity iff strict positivity for
all nonzero `v`. The old development branch was green but behind main, so the
proof has been clean-ported to a branch created from current main with only the
module and one official import.

Promotion rule: merge only after clean CI + PR CI, then post-main CI and ledger
update.

### Lane B — P-INV-03 Fisher accumulation [HOT]

Branch: `formal/pinv03-fisher-intersection`

Frozen claim:

- conditionally/independently generated experiment scores with zero mean have
  additive Fisher information;
- for PSD Fisher blocks, `ker(sum I_e) = intersection_e ker(I_e)`.

Machine-checked already:

- abstract PSD kernel-intersection mechanism;
- independent centered experiment score coordinates have zero cross Fisher
  integrals.

Remaining source closure:

1. finite score-sum / Fisher-entry expansion;
2. use zero cross terms to prove `I_total = sum_e I_e`;
3. instantiate the PSD kernel theorem with those Fisher blocks;
4. expose a single source-facing `p_inv_03` wrapper;
5. run clean promotion train.

Do **not** promote the abstract intersection lemma alone.

### Lane C — P-STAT-06 RKHS/MMD concentration [HOT]

Branch: `formal/pstat06-mmd-concentration`

Frozen target:
`max_j ||muHat_j-mu_j|| <= (1 + sqrt(2*log(L/alpha)))/sqrt(N)`
with probability at least `1-alpha`.

Machine-checked layers already include:

- exact `2/N` one-sample replacement sensitivity;
- centered Hilbert off-diagonal cancellation;
- empirical squared-norm expansion;
- `E||mean Z_i||^2 <= 1/N`;
- direct Hilbert first-moment bound;
- Azuma/Hoeffding scalar tail algebra.

Current integration repair: normalize the constant sub-Gaussian parameter sum
in the imported Azuma layer. After this compiles, finish the explicit
bounded-difference/Doob bridge and the finite `L` union bound. No replacement by
an assumed McDiarmid theorem without a source-semantic audit.

## 5. Next WARM pool

Open new lanes only as current HOT/PROMOTION lanes vacate slots. Maintain 4–6
active proof lanes, but do not create branches just to fill a quota.

Priority order:

1. **P-INV-05 and remaining inverse/identifiability packet** after P-INV-04;
2. **P-INFO-02/03/04** using the already integrated information infrastructure;
3. **P-INT-01** structured sufficiency iff, reusing P-PRED-01 and information
   modules rather than duplicating them;
4. **remaining QSD/persistence theorems**, split finite Perron/Markov results
   from diffusion/spectral analysis;
5. **finite composition / object implementation packet** before analytic parent
   emergence theorems;
6. **finite control/quotient packet** before continuous HJB/spectral GOA work.

Old branches containing useful experiments are evidence sources only. Every new
promotion candidate starts from current green main and ports the smallest
source-matched delta.

## 6. Dependency factories for the remaining 60

### Factory G — finite certification and inverse problems

P-STAT / P-INV remainder. Reuse finite concentration, total variation,
response-defect and Fisher infrastructure already on main.

### Factory H — implementation / composition

P-ID / P-OMG / P-COMP remainder. Separate finite set-hypergraph/Booleanization
proofs from prediction-information parent emergence.

### Factory I — information / structural interfaces

P-INFO / P-INT remainder. One canonical KL/MI layer only; no duplicate entropy
or conditional-independence definitions.

### Factory J — control / quotient / GOA

P-CTL, P-QUO and P-GOA remainder. Dependency direction is fixed:
process -> predictive state -> dynamic quotient -> policy/value -> GOA.

### Factory K — KL / variational / dual-drive

P-KL, P-DDH and P-ALI remainder. Distinguish exact algebraic gauge statements,
finite Markov path-KL, and genuinely analytic/Girsanov theorems.

### Factory L — evolution / reflexivity / final assembly

P-EVO, P-BRG, P-REF remainder, then P-API / P-ALG / P-CORE integration
statements. Assembly theorems never mask missing prerequisites.

## 7. File ownership and concurrency

- one P-ID family owns one module or a tightly scoped module group;
- feature branches edit `UEOT/V3.lean` only for their own imports;
- only main synchronization commits edit the source coverage ledger;
- reusable infrastructure needed by two lanes is split, proved, and merged
  first rather than cherry-picked between stale branches;
- proof development is parallel, main promotion is serialized.

## 8. CI hierarchy

### L1 — feature branch

Compile the official `UEOT`/`UEOT.V3` target with the new module imported.
This catches the common failure mode “file exists but was never elaborated”.

### L2 — clean promotion / PR

Require newest green Lean-affecting main, full build, source-facing theorem,
semantic audit, and prohibited-proof audit. Docs-only main movement does not
force proof replay when the Lean tree is unchanged and the PR is conflict-free.

### L3 — post-main

Run full build and audits. Coverage changes only after success.

## 9. Merge train

For every P-ID independently:

`source audit -> helpers -> source wrapper -> official import -> feature CI -> clean port -> clean CI -> PR CI -> serialized squash merge -> post-main CI -> ledger sync`.

While a lane waits in CI, another lane continues proof development. A failed CI
is treated as a concrete proof/integration task, not as a reason to stop the
other lanes.

## 10. Completion condition

UEOT Core v3.0 is machine-complete only at:

- **106 proved / 0 partial / 0 pending**;
- full `lake build UEOT` green on main;
- source-to-ledger consistency green;
- transitive axiom/prohibited-proof audit green;
- no source P-ID counted through a helper theorem alone.

The objective is not maximum branch count. It is maximum rate of independently
auditable source theorems reaching a green, source-faithful `main`.
