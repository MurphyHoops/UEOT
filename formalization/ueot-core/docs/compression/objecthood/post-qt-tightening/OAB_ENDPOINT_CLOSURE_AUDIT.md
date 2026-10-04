# O-A/O-B — Post-QT / Post-GCR endpoint closure audit

Status: **LOCAL PASS**
Track: O
Risk tier: L1 additive, uncounted
Canonical base: `main@3cbec434411980af701d0342bbdd9531e1a9a813`

## Scientific result

Two previously distributed consequences are now exposed as terminal APIs without
changing any historical theorem.

1. For a fixed `RecurrentHomeostasisSystem` and fixed potential, the canonical
   RH certificate attains the greatest certified `homeostaticMarginReal` among
   all existing `FaultBurdenCertificate`s. Consequently, its margin is positive
   iff some RH1 certificate has positive margin.
2. The strongest existing same-parent semantic + eventual-permanent repair
   endpoint accepts the full `GeneralCausalAlmostSureRepairable` premise using
   the already-proved GCR6 equivalence.
3. A failing deletion satisfying that same broad repairability premise therefore
   has a minimal destructive witness, the existing Track-X same-parent semantic
   bound, and almost-sure eventual-permanent restoration by the unchanged
   canonical stationary repair architecture.

## Boundary

The canonical optimality statement is certificate-relative only. It does not
optimize over repair potentials, repair laws, carriers, fault kernels or parent
selection, and it is not a necessary-and-sufficient physical phase-transition
claim.

The general-causal endpoint is restricted to the already proved finite
controlled-PMF GCR semantics. It introduces no new repair policy or path law.

## Validation

- focused Lean compile of both new modules: PASS;
- module build: PASS;
- proof-escape scan: CLEAR;
- representative `#print axioms`: only `propext`, `Classical.choice`,
  `Quot.sound`;
- `git diff --check`: PASS;
- counted core impact: NONE.
