# Primitive-Defect Optimal-Policy GOA Closure Audit

Status: **LOCAL PASS**

Track: S

Risk tier: L1 additive, uncounted

Base stage: primitive reward/span closure local commit `e3ca0bf`

## Result

The strongest moving optimal-policy near-GOA closure is now available without
an external `D_n -> 0` certificate and without a uniform optimal-value-span
hypothesis.

The terminal hypotheses are primitive or structural:

- one finite common micro model;
- weighted representation-gauge mismatch tends to zero;
- exact reference reward/transition defects;
- moving reward defect tends to zero;
- moving transition defect tends to zero;
- a positive uniform source optimal-action gap;
- source greedy closed-loop Dobrushin coefficient below one.

From these, the new endpoint proves eventual unique quotient relabeling carrying
the target model's own greedy policy and the near-GOA invariant-law certificate.
The tail version proves that its stationary-law TV radius becomes arbitrarily
small.

The removed span hypothesis is derived by the preceding primitive reward/span
closure, not silently assumed.

## Boundary

A common literal micro model remains essential to this theorem.  The result does
not claim stability when the underlying micro model itself changes, nor does it
remove the source action-gap or contraction conditions.

No counted generator or frozen source theorem is changed.

## Validation

- focused Lean compile: PASS;
- proof-escape scan: CLEAR;
- `git diff --check`: PASS;
- counted core impact: NONE.
