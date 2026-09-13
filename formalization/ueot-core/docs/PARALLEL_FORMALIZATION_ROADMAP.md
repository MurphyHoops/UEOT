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
6. PR CI;
7. serialized `main` integration;
8. green post-main `lake build UEOT`;
9. prohibited-proof / unsourced-axiom audit;
10. ledger synchronization.

Public canonical-source byte synchronization is a separate reproducibility task;
it is not allowed to masquerade as a mathematical proof gate.

## 2. Current checkpoint — 2026-09-13

- integrated proved: **53/106**
- pending: **53/106**
- P-ID-02: **PROVED / COUNTED** after source audit of existing main proof
- P-INFO-03: **ACTIVE PROOF**
- P-INT-01: **BLOCKED** on P-INFO-03 interfaces
- remaining unclassified audit population: **51 P-IDs**
- public canonical source-byte sync: **pending reproducibility task**

## 3. Priority lanes

### Lane A — P-INFO-03 [highest proof priority]

Frozen target:
`R_obj(0)=H(C|U)` for discrete canonical predictive core
`C=P(Y|H,U)` with `H(C|U)<∞`, while permitting genuinely randomized encoders
`P(M|H,U)` that cannot access future `Y`.

Non-negotiable proof chain:

1. genuine countable conditional entropy by `U`-disintegration;
2. kernel-level random-encoder joint law;
3. zero average TV implies the predictive-law code is recoverable from `(M,U)`;
4. measurable law-code inverse recovers the discrete core label;
5. conditional data processing gives
   `I(H;M|U) >= I(C;M|U)=H(C|U)`;
6. define the source-faithful zero-distortion feasible class / rate objective;
7. attain equality by `M=C`;
8. expose exact source-facing `R_obj(0)=H(C|U)`.

Already independently verified:

- generic CMI official CI: run `34707458047` success;
- countable conditional entropy, generic conditional KL decomposition,
  random-encoder geometry, recoverable discrete identity, conditional
  recoverability and zero-TV infrastructure have passed through the active
  full graph in previous runs.

Active branch: `formal/pinfo03-countable-conditional`.
Current head at this synchronization:
`3ad766b6f50590e70caed8ac293067f2146d68d2`.
Current full-target CI: `34734186954` in progress.

The last observed downstream failures were concrete elaboration defects, not a
mathematical collapse:

- law-code decoder: invalid field notation / missing classical decidability;
- conditional statistic layer: `mutualInfo` namespace mismatch.

Both were repaired. No second information-theory stack should be created.

### Lane B — source-to-main audit of remaining 51 P-IDs

This lane is now mandatory, not optional. P-ID-02 demonstrated that a theorem
can be fully source-faithful, merged and post-main green while a stale ledger
still labels it pending.

For each remaining P-ID classify exactly:

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

### Lane C — P-INT-01 dependency lane

Frozen target:
`Y_f^+ ⟂ H | (M,U) ↔ C^f = Psi(M,U) a.s.`.

Until P-INFO-03 stabilizes the general countable conditional-information and
predictive-core recovery interfaces, this lane is audit/reuse only. No duplicate
conditional independence/KL stack.

### Lane D — canonical source artifact reproducibility

1. synchronize exact source bytes without regeneration;
2. independently recompute frozen SHA-256;
3. keep the artifact immutable and third-party reproducible.

This lane changes reproducibility status, not theorem count by itself.

## 4. Closed / frozen lanes

Do not reopen without a substantive source mismatch or CI regression:

- P-STAT-06;
- P-INFO-02;
- P-INFO-04;
- P-ID-02.

For P-ID-02 the canonical main implementation is
`UEOT.V3.DevelopmentTransport`; a duplicate `DevelopmentPipeline` implementation
was explicitly abandoned after the audit found the complete existing proof.

## 5. Concurrency model

- **Thread 1:** P-INFO-03 proof chain;
- **Thread 2:** full source-to-main audit of the remaining 51 P-IDs;
- **Thread 3:** P-INT-01 dependency/reuse audit;
- **Thread 4:** public canonical-source reproducibility.

Parallelism hides CI latency and separates independent obligations. It must not
create competing foundational implementations.

## 6. Merge train

`source audit -> proof contract -> existing-main audit -> missing lemmas only -> source-facing theorem -> official import -> full-target CI -> clean port as needed -> PR -> main -> post-main CI -> ledger sync`.

The explicit `existing-main audit` step is now mandatory because it prevented a
second P-ID-02 implementation and recovered a real completed theorem from a
stale ledger.

## 7. Completion condition

UEOT Core v3.0 is machine-complete only at **106 proved / 0 partial / 0 pending**,
with full `lake build UEOT` green on `main`, source-to-theorem semantic
consistency, transitive prohibited-proof/axiom audit green, and no P-ID counted
through helper theorems alone.

Full third-party repository reproducibility additionally requires the exact
canonical source artifact and independently verified frozen SHA-256.
