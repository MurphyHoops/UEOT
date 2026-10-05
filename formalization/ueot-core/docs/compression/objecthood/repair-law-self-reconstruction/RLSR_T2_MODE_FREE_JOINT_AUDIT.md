# RLSR-T2 — mode-free joint recovery audit

Status: **LOCAL PASS**

## Why the old RLSR6 interface was not ideal

The first RLSR6 joint state carried a mutable `restoreProgram/executeProgram` mode.
Its theorem was correct only on the declared basin where that bit was already
`restoreProgram`.  The same state also stored a controller, while execute mode
selected the physical action directly from `T.execute r`, bypassing that stored
controller as a causal actuator.

Neither fact invalidated the old theorem, but both weakened the architectural claim.

## Strengthened kernel

`safeRepairKernel` reuses the RLSR1 `SelfReconstructingState` specialization and
contains no mutable scheduler bit.  Before every physical transition it:

1. decodes current repair-program representation;
2. rewrites it to canonical encoded form;
3. rebinds the ordinary controller to the decoded program;
4. reads the physical action from that rebuilt controller;
5. performs the physical transition and carries the repaired organization forward.

Thus the actual causal chain is `program -> controller -> physical`.

For triple repetition, Lean proves exact masking of arbitrary one-replica replacement
plus arbitrary stored-controller corruption in the same transition.  Because the
canonicalization happens on every step, the theorem also exposes one-step masking of
a fresh single-replica program fault during execution; a full stochastic recurrent
fault-process theorem remains a later path-level strengthening.
