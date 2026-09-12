# UEOT Core v3.0 — Parallel Lean Completion Roadmap

This is the execution plan for completing all 106 frozen source P-IDs in
`UEOT_Core_Mathematics_v3.0_Complete.md`.

Machine-readable live state belongs in `PID_STATUS.yaml`. Human recovery state
belongs in `FORMALIZATION_STATE.md`. The authoritative integrated source count
belongs in `V3_COVERAGE_STATUS.md`.

## 1. Promotion gate

A P-ID is counted `proved` only after:

1. direct semantic audit against the canonical frozen source object;
2. source-faithful Lean closure;
3. official import reachability;
4. relevant feature full-target CI;
5. minimal clean port and clean CI where applicable;
6. PR CI;
7. serialized `main` integration;
8. green post-main `lake build UEOT`;
9. prohibited-proof / unsourced-axiom audit;
10. ledger synchronization.

**Public source-artifact reproducibility is separate.** The exact canonical
Markdown bytes are still absent from the public repository, so third parties
cannot yet recompute the frozen SHA-256 from the repo alone. This remains an
important packaging/reproducibility task, but it does not negate a theorem that
has been directly source-audited against the canonical object and passed the
full Lean promotion chain. The repository must never claim SHA reverification
until exact raw bytes are actually available and hashed.

Audit evidence for the 2026-09-13 information promotions is
`docs/SOURCE_AUDIT_EVIDENCE_2026-09-13.md`.

## 2. Current checkpoint — 2026-09-13

- integrated proved: **52/106**
- P-STAT-06: **PROVED/CLOSED**
- P-INFO-02: **PROVED/COUNTED**
- P-INFO-04: **PROVED/COUNTED**
- P-INFO-03: **ACTIVE PROOF**
- P-INT-01: **BLOCKED** on the general conditional-information interface
- public canonical source-byte sync: **pending reproducibility task**

## 3. Priority lanes

### Lane A — P-INFO-03 countable zero-distortion complexity [highest priority]

Frozen target:

`R_obj(0)=H(C|U)`

for the discrete canonical predictive core `C=P(Y|H,U)` with
`H(C|U)<∞`, allowing random encoders `P(M|H,U)` that cannot access future `Y`.

The exact source proof contract is:

1. zero average TV implies the predictive core `C` is recoverable from `(M,U)`;
2. conditional DPI gives
   `I(H;M|U) >= I(C;M|U)=H(C|U)`;
3. choose `M=C` and decode the canonical predictive kernel to attain equality.

Verified foundation:

- `InformationConditionalDiscreteEntropy` gives a genuine `U`-disintegration
  definition of countable `H(C|U)` via a measurable ENNReal Shannon `tsum`;
- full-target CI `34706765170`: success.

Current active layers:

- generic KL conditional mutual information;
- generic conditional KL fiber decomposition;
- random-encoder joint-law geometry;
- recoverable discrete information identity;
- exact bridge from the fiber Shannon `tsum` to the existing
  `discreteShannonEntropy` representation.

Non-negotiable source constraints:

- `InformationStatistic` is deterministic-statistic infrastructure and cannot
  represent the source random encoder;
- random encoding must remain a Markov-kernel/joint-law object;
- `H(C|U)` must be genuine disintegration, never `H(C)-I(C;U)`;
- the zero-TV-to-recoverability step must explicitly identify the predictive
  law; it cannot silently replace the source decoder kernel by a `C`-valued
  decoder.

Active branch: `formal/pinfo03-countable-conditional`.
Latest known head: `9a152cace0831cca498cdf489a06466b36cf2e98`.
Current diagnostic CI: `34707351959`.
An isolated validation lane `formal/pinfo03-generic-cmi-isolated` prevents
later downstream failures from obscuring the generic-CMI layer.

Execution order inside Lane A:

1. freeze generic CMI once isolated official CI is green;
2. freeze generic conditional KL decomposition;
3. prove countable Shannon representation compatibility;
4. machine-check random-encoder joint law;
5. formalize source-faithful zero-TV predictive-core recoverability;
6. prove conditional DPI lower bound;
7. prove attainability by `M=C`;
8. expose exact source-facing `R_obj(0)=H(C|U)` theorem;
9. clean-port -> clean CI -> PR -> main -> post-main -> ledger sync.

### Lane B — P-INT-01 [blocked, immediately after P-INFO-03 interface]

Frozen target:

`Y_f^+ ⟂ H | (M,U) ↔ C^f = Ψ(M,U) a.s.`

for the common countable intervention version.

P-INT-01 must reuse P-INFO-03's general conditional-information and
predictive-core identification infrastructure. Do not create a second
conditional independence/KL/entropy stack.

### Lane C — remaining-52 source-to-main audit [parallel, rigorous]

This is **not** a quick-win lane. Its purpose is to classify each remaining
unclassified P-ID by actual proof state:

- **Class A:** source-facing theorem already exists on `main`; needs only exact
  source semantic audit and promotion evidence;
- **Class B:** substantial infrastructure exists; a small, explicit proof
  obligation is missing;
- **Class C:** source definition/theorem is genuinely unformalized or needs new
  mathematics.

For every P-ID, record the frozen statement, candidate Lean theorem(s), exact
mismatch if any, and next proof obligation. Do not infer completion from module
names alone. This audit is what prevents the project from spending weeks
re-proving statements already present on `main` or, conversely, counting merely
related helpers as source theorems.

### Lane D — public canonical-source synchronization [reproducibility]

The canonical source is known by name and frozen manifest SHA, but its exact raw
bytes are not mounted in the current repository/runtime filesystem. Required
steps:

1. synchronize the exact canonical bytes without regeneration;
2. independently recompute SHA-256
   `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`;
3. preserve the canonical file as an immutable source artifact.

This lane no longer changes proof counts by itself. It changes repository
reproducibility status.

## 4. Concurrency model

The efficient rigorous layout is:

- **Thread 1:** P-INFO-03 proof chain, with isolated CI for each foundational
  layer before downstream composition;
- **Thread 2:** source-to-main audit of the remaining 52 P-IDs, classifying
  actual proof gaps rather than searching for easy counts;
- **Thread 3:** P-INT-01 dependency audit only until the P-INFO-03 interface is
  stable;
- **Thread 4:** public-source artifact reproducibility task.

Parallelism is used to separate independent obligations and hide CI latency, not
to create competing foundational implementations.

## 5. Merge train

`source audit -> proof contract -> missing lemmas only -> canonical source theorem -> official import -> feature CI -> clean port -> clean CI -> PR CI -> serialized main integration -> post-main CI -> ledger sync`.

Public-source byte synchronization is tracked alongside this train but is not
inserted as a false mathematical proof prerequisite.

Helpers, unimported modules, feature-green branches, or mathematically equivalent
but source-mismatched statements do not increment coverage.

## 6. Stop conditions / anti-duplication rules

- P-STAT-06 is frozen closed.
- P-INFO-02 is proved and counted; proof infrastructure is frozen unless a real
  CI regression or source mismatch appears.
- P-INFO-04 is proved and counted; multiway and conditional-binary proof
  infrastructure are frozen; no MAP replacement, second Fano stack or duplicate
  binary KL layer.
- P-INFO-03 random encoders must be represented at kernel/joint-law level, not
  silently replaced by deterministic `M=f(H)` statistics.
- P-INFO-03 conditional entropy must use genuine disintegration; no general
  source theorem may define it as `H(C)-I(C;U)`.
- No second conditional-information formalism may be created for P-INT-01.
- No regenerated substitute may stand in for the canonical frozen source file.
- Never move a P-ID to proved merely because a similarly named module exists;
  exact source-statement matching remains mandatory.

## 7. Completion condition

UEOT Core v3.0 is machine-complete only at **106 proved / 0 partial / 0 pending**,
with full `lake build UEOT` green on `main`, exact source-to-ledger semantic
consistency, transitive prohibited-proof/axiom audit green, and no P-ID counted
through a helper theorem alone.

Full third-party repository reproducibility additionally requires the exact
canonical source artifact to be present in the public repo with independently
verified frozen SHA-256.
