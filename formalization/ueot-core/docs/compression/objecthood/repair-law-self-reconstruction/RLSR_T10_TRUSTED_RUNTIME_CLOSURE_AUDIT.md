# RLSR-T10 — explicit trust-budget / regress audit

Status: **LOCAL PASS**

## Why this is needed

RLSR7 correctly proved a finite repair dependency graph, but represented all
external assumptions by one abstract `trustedSubstrate` node.  After T1--T9 the
actual strengthened architecture distinguishes four externally supplied inputs:

1. execution/interpreter semantics;
2. codec encode/decode semantics;
3. ambient physical dynamics `P`;
4. object/target specification `K` (or the selected-parent specialization).

## Strengthened trust accounting

`TrustedRepairContext` packages exactly those four inputs and contains **no
correct `Program` value**.  Its preferred runtime is the mode-free
`safeRepairKernel`.

The refined dependency graph makes all four trusted nodes rank zero, mutable
repair-program organization rank one, and repaired controller/physical
organization rank two.  Lean proves every edge strictly increases rank,
well-foundedness, absence of any dependency edge into a trusted node, existence
of a genuine two-step repair-of-repair chain, and impossibility of an infinite
repair regress.

## Boundary

This is still relative self-reconstruction: interpreter/codec semantics,
ambient physical law and the object specification are explicit theorem inputs.
The result is stronger because that trust budget is now enumerated rather than
hidden behind one aggregate node, not because those inputs themselves have been
made self-reconstructing.

## Validation

- focused Lean compile/build of `TrustedRuntimeClosure.lean`: PASS;
- refined dependency well-foundedness and no-infinite-regress theorem: PASS;
- umbrella `All.lean` compile: PASS;
- `git diff --check`: PASS.
