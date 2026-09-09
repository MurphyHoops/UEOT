# UEOT Core v3.0 — Parallel Lean Formalization Roadmap

This document is the execution plan for completing the machine-checked
formalization of all 106 source P-IDs in `UEOT_Core_Mathematics_v3.0_Complete.md`.

## Global invariant

The source manuscript is authoritative. A Lean theorem is allowed to promote a
P-ID to `proved` only after all of the following hold:

1. the exact source statement and hypotheses are identified;
2. the Lean declaration has matching or explicitly stronger semantics;
3. the declaration is imported by the official `UEOT` target;
4. pinned Lean/Mathlib CI passes on the feature branch;
5. the branch is merged into `main`;
6. the post-merge `lake build UEOT` passes;
7. no `sorry`, `sorryAx`, UEOT-specific proof axiom, `native_decide`, or
   source weakening was introduced;
8. the coverage ledger is updated with commit/run evidence.

A green helper lemma does not by itself promote a source P-ID.

## Integration model

- `main` is the green integration branch.
- Proof development uses disjoint feature branches.
- Each lane should prefer new modules over editing a shared large module.
- Every feature branch imports its new module from `UEOT.V3` so CI checks the
  official target rather than an isolated file.
- Pull requests are draft while proofs are under construction.
- CI may run concurrently; merges into `main` are serialized.
- After every merge, the next source-status promotion waits for a green
  post-merge build.
- Coverage/documentation updates are integration work and should not be used to
  make an unfinished theorem appear complete.

## Current checkpoint

After the P-MET-01, P-MET-02 and P-DYN-01 closures:

- proved: 22
- partial: 0
- pending: 84
- total: 106

The absence of `partial` means every remaining source item is now an explicit
proof obligation rather than a half-promoted claim.

## Active Wave A — independent foundational lanes

| Lane | Branch / module direction | Source targets | Immediate objective |
|---|---|---|---|
| A1 Process | `formal/v3-coverage-wave2` | P-PROC-01 | construct the concrete growing history state `Z_t=(t,H_t)`, prove measurable advance and dispatch time-indexed kernels into one homogeneous Markov kernel |
| A2 Covariance | `formal/pfac01-covariance` | P-FAC-01 | transport kernels, readouts, path laws, predictive sufficiency and values under a bimeasurable bijection |
| A3 Prediction update | `formal/ppred03-recursion` | P-PRED-03 | Bayes continuation update, positive-probability branch, product/countable coordinate measurability |
| A4 Information core | integrated KL core + follow-up branches | P-INFO-01..03 | define MI/CMI from measure-theoretic KL and derive deterministic-statistic chain identities |
| A5 Information packing | `formal/pinfo-packing` | P-INFO-04..05 | TV half-separation, finite packing cardinality, Fano/entropy lower bounds |
| A6 Structured interface | `formal/pint-structure` | P-INT-01..03 | predictive sufficiency/conditional-independence bridge and Markov-boundary uniqueness |
| A7 Persistence/recovery | `formal/persistence-recovery` | P-PER-01..04, P-REC-01 | finite-state viability/persistence foundations and discrete recovery drift |
| A8 Integration | `main` | all completed lanes | serial merge, post-merge CI, source audit, coverage promotion |

## Wave B — stochastic dynamics and recovery

Start once the relevant Wave A interfaces are green:

- P-DYN-02 continuous-time generator criterion
- P-DYN-03 same-policy path-error propagation
- P-DYN-04 cross-scale quotients of one underlying process
- P-REC-02 generator/Lyapunov recovery
- P-REC-03 hitting-time canonical potential
- P-REC-04 drift-to-recovery-time theorem
- P-QSD-01..04 conditional stabilization, finite Perron and spectral versions

These share probability-process infrastructure but should be split into
continuous-time, discrete-time and spectral branches to avoid file contention.

## Wave C — identity, destruction, complexity and invariants

Parallel families:

- P-ID-01..02
- P-OMG-01..02
- remaining P-COMP-01..07 obligations
- remaining P-STAT-01..09 obligations
- remaining P-INV-01..05 obligations

Finite/combinatorial versions should be separated from analytic/probabilistic
versions. Existing proved CAR/RES/STAT declarations are reused rather than
reimplemented.

## Wave D — control, quotient and agency

After predictive/dynamic interfaces are stable:

- P-CTL-01..03
- remaining P-QUO-01..05 obligations
- P-GOA-01..04

The dependency direction is fixed:

`world/process -> predictive state -> closed/approximate dynamics -> feasible
policy set -> value/Bellman -> quotient/agency conclusions`.

No control theorem may redefine upstream predictive or dynamic semantics.

## Wave E — information geometry, alignment and evolution

Independent sublanes where possible:

- P-KL-01..05
- P-DDH-01..05
- P-ALI-01..03
- P-EVO-01..04
- remaining P-BRG / P-REF obligations

The KL lane should reuse `UEOT.V3.InformationCore` and pinned Mathlib KL
chain/data-processing theorems.

## Wave F — final assembly

Only after all prerequisite P-IDs are source-proved:

- P-API-01
- P-ALG-01
- P-CORE-01

This wave is an assembly/audit phase, not a place to hide missing mathematics.
The final completion gate is:

- 106 proved
- 0 partial
- 0 pending
- full `lake build UEOT` success
- source/coverage consistency audit success
- transitive axiom audit success

## Per-lane work packet

Every active lane should maintain this order:

1. source excerpt and exact types;
2. Mathlib API reconnaissance;
3. minimal reusable core lemmas;
4. exact source-facing wrapper;
5. negative/edge-case audit;
6. official import;
7. branch CI;
8. merge;
9. main CI;
10. coverage promotion.

This order permits aggressive parallel proof development while keeping source
claims, Lean semantics and verification evidence synchronized.
