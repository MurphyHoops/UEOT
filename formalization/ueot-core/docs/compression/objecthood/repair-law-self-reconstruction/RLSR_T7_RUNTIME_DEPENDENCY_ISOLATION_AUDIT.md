# RLSR-T7 — runtime dependency isolation audit

Status: **LOCAL PASS**

## Motivation

After T1--T6 the preferred RLSR architecture was already the mode-free
`safeRepairKernel`, but its source file still imported the historical two-mode
`JointRecovery` module only to reuse the program-specific physical-recovery
adapter theorems that happened to live there.

That dependency was semantically backwards: a preferred runtime should not
depend on its superseded compatibility runtime.

## Refactor

The following declarations were moved unchanged into the new neutral adapter
module `ProgramPhysicalRecovery.lean`:

- `RepairProgramRecoverableAt`;
- `repairProgramRecoverableAt_iff`;
- `reconstructedProgram_eventually_hits_ae`;
- `reconstructedProgram_eventually_always_target_ae`.

`JointRecovery.lean` now imports this adapter and retains its legacy runtime
surface.  `SafeJointRecovery.lean` imports the adapter directly and no longer
imports `JointRecovery.lean`.

Thus the dependency direction is now:

```text
ProgramRecovery
      |
      v
ProgramPhysicalRecovery
   |               |
   v               v
legacy Joint    preferred SafeJoint
Recovery        Recovery
```

rather than preferred runtime -> legacy runtime.

## API / proof preservation

No theorem was renamed and no statement was weakened or strengthened by this
refactor.  The moved declarations remain in the same namespace, so downstream
T3/T4/T5 theorem code sees the same API.

Focused validation after rebuilding stale `.olean` files:

- `ProgramPhysicalRecovery.lean`: PASS;
- `JointRecovery.lean`: PASS;
- `SafeJointRecovery.lean`: PASS;
- `TightenedSameParentRestoration.lean`: PASS;
- `SafeJointPathLaw.lean`: PASS;
- `RepairLawSelfReconstruction.All`: PASS with zero focused output.

## Scientific verdict

This is architectural compression, not new physics/mathematics.  It makes the
post-audit theorem DAG accurately reflect the scientific verdict already stated
in T6: the two-mode runtime is retained only as a historical/compatibility
surface, while the mode-free safe runtime is the preferred RLSR architecture.
