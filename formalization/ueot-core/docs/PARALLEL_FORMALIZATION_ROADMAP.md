# UEOT Core v3.0 — Parallel Lean Completion Roadmap

This is the execution plan for completing all 106 frozen source P-IDs in
`UEOT_Core_Mathematics_v3.0_Complete.md`.

## 1. Promotion gate

A P-ID is counted `proved` only after:

1. direct semantic audit against the canonical frozen source object;
2. source-faithful Lean closure;
3. official `UEOT.V3`/`UEOT` import reachability;
4. relevant full-target feature CI;
5. clean-port / clean CI when applicable;
6. serialized `main` integration;
7. green post-main `lake build UEOT`;
8. prohibited-proof / unsourced-axiom audit;
9. ledger synchronization.

Public canonical-source byte synchronization is a separate reproducibility task;
it is not allowed to masquerade as a mathematical proof gate.

## 2. Current checkpoint — 2026-09-13

- integrated proved: **54/106**
- pending: **52/106**
- P-INFO-03: **PROVED / COUNTED**
- P-INT-01: **ACTIVE PROOF**
- remaining unclassified audit population: **51 P-IDs**
- public canonical source-byte sync: **pending reproducibility task**

P-INFO-03 was promoted only after final proof CI `34744325632`, clean integration
CI `34744658528`, main commit
`57e987a18a5dd8feca224b91e3e78b93c2a44de8`, post-main CI `34744919310`, and
prohibited-proof audit. Its conditional/disintegration infrastructure now
unblocks P-INT-01.

## 3. Priority lanes

### Lane A — P-INT-01 [highest proof priority]

Frozen source target, Predictive Factorization Characterization Theorem 5.1:
for Standard-Borel variables and `Z=(M,U)`,

`Y ⟂ H | Z`

iff there exists measurable

`Psi : Z -> P(Y)`

such that the canonical predictive state

`C*=L(Y|H)=Psi(Z)` almost surely.

Non-negotiable scope:

- general Standard-Borel theorem;
- do **not** impose P-INFO-03's countable canonical-core restriction;
- `Psi` is represented by a Markov kernel `Kernel Z Y`;
- conditional independence must use the real regular-conditional semantics,
  not a newly defined slogan or a finite-protocol surrogate;
- do not duplicate the general conditional-information/disintegration stack.

Planned proof chain:

1. define source-faithful `PredictiveFactorization` by a Markov kernel pulled
   back along the measurable statistic `Z=(M,U)`;
2. identify `condDistrib Y H` with the canonical joint-law `condKernel`;
3. use pinned Mathlib theorem
   `condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight`;
4. prove that conditioning on `(Z,H)` is equivalent to conditioning on `H`
   because `Z` is a measurable function of `H`;
5. derive conditional independence -> canonical-law factorization;
6. derive factorization -> conditional independence;
7. expose exact source-facing iff theorem;
8. full-target CI -> clean main integration -> post-main CI -> ledger sync.

Active branch: `formal/pint01-factorization-iff`.
Base main commit: `57e987a18a5dd8feca224b91e3e78b93c2a44de8`.
Initial active head: `d0829f75ce8e8d7ee251f5644478f3b75b1e445a`.
Initial full-target CI: `34745077495` in progress.

### Lane B — source-to-main audit of remaining 51 P-IDs

This lane remains mandatory. For each remaining P-ID classify exactly:

- **Class A:** source theorem already exists on main; perform exact semantic
  audit and promotion evidence collection;
- **Class B:** infrastructure exists, but a specific source-facing bridge or
  boundary case is missing;
- **Class C:** genuinely unformalized mathematics / definitions.

Required audit record per P-ID:

1. frozen source statement and assumptions;
2. candidate main theorem(s);
3. formula and quantifier match;
4. boundary / measurability / integrability / finiteness match;
5. exact mismatch, if any;
6. CI/main evidence;
7. classification A/B/C and next action.

**Do not create a new proof module until this audit says the source theorem is
actually missing.**

### Lane C — P-INT-01 Mathlib/API reuse audit

In parallel with the main proof branch, inspect pinned Mathlib at
`0df444a360eaa60ab8c11dca51a86af692955474` for exact conditional-distribution
and disintegration identities. Prefer library theorems over manual reproofs.
The first confirmed high-leverage bridge is
`condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight`.

### Lane D — canonical source artifact reproducibility

1. synchronize exact source bytes without regeneration;
2. independently recompute frozen SHA-256;
3. keep the artifact immutable and third-party reproducible.

This lane changes reproducibility status, not theorem count by itself.

## 4. Closed / frozen lanes

Do not reopen without a substantive source mismatch or CI regression:

- P-STAT-06;
- P-INFO-02;
- P-INFO-03;
- P-INFO-04;
- P-ID-02.

P-INFO-03 canonical theorem:
`UEOT.V3.InformationPredictiveRateZero.predictiveObjectRateZero_eq_sourceEntropy`.

## 5. Concurrency model

- **Thread 1:** P-INT-01 proof chain;
- **Thread 2:** full source-to-main audit of the remaining 51 P-IDs;
- **Thread 3:** pinned-Mathlib API/reuse audit for P-INT-01;
- **Thread 4:** public canonical-source reproducibility.

Parallelism hides CI latency and separates independent obligations. It must not
create competing foundational implementations.

## 6. Merge train

`source audit -> proof contract -> existing-main audit -> missing lemmas only -> source-facing theorem -> official import -> full-target CI -> clean port as needed -> main -> post-main CI -> ledger sync`.

The explicit `existing-main audit` step remains mandatory because it previously
prevented duplicate work and recovered already-complete source theorems from a
stale ledger.

## 7. Completion condition

UEOT Core v3.0 is machine-complete only at **106 proved / 0 partial / 0 pending**,
with full `lake build UEOT` green on `main`, source-to-theorem semantic
consistency, transitive prohibited-proof/axiom audit green, and no P-ID counted
through helper theorems alone.

Full third-party repository reproducibility additionally requires the exact
canonical source artifact and independently verified frozen SHA-256.
