# UEOT Core v3.0 — Parallel Lean Completion Roadmap

This is the execution plan for completing all 106 frozen source P-IDs in
`UEOT_Core_Mathematics_v3.0_Complete.md`.

Machine-readable live state belongs in `PID_STATUS.yaml`. Human recovery state
belongs in `FORMALIZATION_STATE.md`. The authoritative integrated source count
belongs in `V3_COVERAGE_STATUS.md`.

## 1. Promotion gate

A P-ID is counted `proved` only after all of the following hold:

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

## 2. State semantics

Do not collapse all unfinished work into `pending`.

- **SOURCE_AUDIT** — frozen statement and existing-library coverage are being mapped.
- **PROOF** — at least one source-essential missing lemma remains.
- **INTEGRATION** — proof is complete but official import/clean-port work remains.
- **PROMOTION** — source-complete clean port is moving through CI/PR/main.
- **BLOCKED** — dependency or source ambiguity prevents correct proof work.
- **PROVED** — passed the full gate and is counted in `V3_COVERAGE_STATUS.md`.
- **ARCHIVE** — merged/superseded/historical evidence only.

`pending` in the coverage ledger means "not yet counted proved". It MUST NOT be
interpreted as "mathematics not yet proved".

Before writing Lean for any P-ID, read its proof contract in `PID_STATUS.yaml`
and prove only the listed `missing` obligations.

## 3. Current checkpoint — 2026-09-12

- integrated proved: **49/106**
- P-STAT-06: **PROMOTION**, not proof work
- P-INFO-02/03/04: **SOURCE_AUDIT**
- P-INT-01: **BLOCKED** on canonical conditional-information interface

### Lane A — P-STAT-06 [PROMOTION ONLY]

The mathematical/source chain is complete, including concrete Doob increments,
conditional Hoeffding/sub-Gaussian control, exact first-moment shift, exact
radius, finite-L simultaneous closure, heterogeneous raw-sample union, and raw
feature pushforward assumptions.

Promotion evidence:

- feature head `5a5cb89d600059525cb775c9561aa50d031da38d`;
- feature full-repo CI `34684444280`: success;
- clean-port `formal/pstat06-clean-port`;
- clean-port head `2338d5fe7a5e9ae8a08cdfd469d0eacd35a80205`;
- clean-port CI `34684655595`: success;
- PR #40 opened against `main`;
- PR CI `34685272294`: running at the time of this synchronization.

Unless CI exposes a real Lean defect or a frozen-statement audit finds a
substantive mismatch, do not add another Doob/Hoeffding/MGF/radius/union/feature
wrapper for P-STAT-06.

Promotion train only:

`PR CI -> merge main -> post-main CI -> ledger sync -> 50/106`.

### Lane B — P-INFO-02/03/04 [SOURCE_AUDIT]

Frozen proof contracts:

**P-INFO-02**

- assumptions: standard-Borel `H,Y,M,U`, with `M,U` history functions;
- `epsilon = I(H;Y | M,U)`;
- target: average TV predictive defect `<= sqrt(epsilon/2)`;
- route: conditional MI as average conditional KL -> Pinsker -> Jensen;
- existing reusable stack: `InformationCore`, `InformationStatistic`;
- current missing obligation: canonical conditional-kernel TV expectation bridge
  plus one source-facing wrapper.

**P-INFO-03**

- canonical core `C = P(Y in . | H,U)` is discrete and `H(C|U)<infinity`;
- target: `R_obj(0) = H(C|U)`;
- random encoders are allowed;
- route: zero TV -> `C` recoverable from `(M,U)` -> conditional data processing
  lower bound -> attainability by `M=C`;
- existing reusable stack: `InformationCore`, `InformationDiscreteEntropy`,
  `InformationMemoryBound`;
- current missing obligation: the actual predictive-rate-distortion interface
  for random encoders and conditional entropy. This is the deepest information
  packet and must not be replaced by another deterministic-statistic wrapper.

**P-INFO-04**

- `J` uniform on `K>=2` identities, decoded from `Y_T` with error `e`;
- target: `I(J;Y_T) >= log K - h2(e) - e*log(K-1)`;
- route: standard Fano proof via error indicator;
- source also contains the conditional binary identity-information lower bound;
- current missing obligation: source-matched Fano theorem/wrapper.

Recommended proof order after audit:

1. P-INFO-02;
2. P-INFO-04;
3. P-INFO-03;
4. only then unblock P-INT-01.

### Lane C — P-INT-01 [BLOCKED]

Do not start another conditional-independence formalism. Reuse the canonical
conditional-information interface created by P-INFO-02/03 and the existing
prediction/Markov-boundary stack. The frozen target is an iff/bridge statement,
not a one-direction surrogate.

### Lane D — other pending families [SOURCE AUDIT POOL]

QSD/persistence, implementation/composition, control/quotient, KL/variational,
and final assembly work should enter PROOF only after a source/dependency audit
records a concrete missing obligation in `PID_STATUS.yaml`.

## 4. Concurrency discipline

- proof development may be parallel; main promotion is serialized;
- one P-ID family owns one module or tight module group;
- no second entropy/KL/concentration stack when an integrated one already exists;
- while one lane waits in CI, work on another lane's source audit or actual
  missing lemma; repeated CI polling is not proof progress;
- do not rebase stale experimental branches merely to make them look current;
  clean-port only the verified source-matched delta.

## 5. Merge train

For every P-ID:

`source audit -> proof contract -> only missing helpers -> canonical source theorem -> official import -> feature CI -> clean port -> clean CI -> PR CI -> serialized main integration -> post-main CI -> ledger sync`.

## 6. Completion condition

UEOT Core v3.0 is machine-complete only at:

- **106 proved / 0 partial / 0 pending**;
- full `lake build UEOT` green on `main`;
- source-to-ledger consistency green;
- transitive axiom/prohibited-proof audit green;
- no P-ID counted through a helper theorem alone.
