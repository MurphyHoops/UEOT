# RLSR6 — joint physical/controller/program recovery audit

Status: **LOCAL PASS**

## Architecture

RLSR6 upgrades the scratch preflight from a conjunctive proof sequence to an
explicit autonomous two-mode kernel:

1. `restoreProgram`: decode current mutable replicas, rewrite the representation
to a consistent codeword, bind the ordinary controller to that decoded program,
and **do not move physical state**;
2. `executeProgram`: use that decoded internal program to select the physical
action and map the physical transition back into the recovered joint state.

The runtime kernel never receives a separately selected correct repair policy.

## Scientific strengthening

The explicit `JointRecoveryBasin` requires exactly the two kinds of surviving
information needed by the mechanism:

- a single-replica corruption of some behaviorally valid program codeword;
- physical membership in that same program's own finite-expected-hitting basin.

`jointRecoveryBasin_recovers` then supplies exact first-step organizational
reconstruction, almost-sure eventual-permanent physical recovery, and closure of
the fully recovered joint target.  `jointRepairKernel_restored` proves that the
post-reconstruction joint kernel is literally the physical kernel driven by the
reconstructed program, embedded back into joint state.

## Boundary

The theorem still assumes the trusted interpreter/decoder substrate and a
single-replica representation fault.  It does not model recurrent corruption of
the representation while executing, nor does it infer a valid repair program
when the surviving representation decodes to an invalid one.

## Validation

- focused Lean compile/build of `JointRecovery.lean`: PASS;
- no new warning emitted from the RLSR6 module after theorem-surface cleanup;
- `git diff --check`: PASS.
