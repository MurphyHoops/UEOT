# RLSR1 — internal repair-program representation audit

Status: **LOCAL PASS**

Base stage: RLSR0 local commit `810238c`

## Result

`SelfReconstructingState X Controller Representation` makes the repair-program
representation an explicit mutable coordinate beside physical state and ordinary
controller state.  `Representation` is not identified with executable `Program`:
that separation is required for later redundant/error-correcting encodings.

`executedRepairController` merely interprets a supplied decoded program through
the trusted substrate.  It contains no externally selected repair policy.

## Independent re-derivation / optimization

The RLSR0-RLSR2 scratch preflight used `repairProgram : Program` directly.  That
is too narrow for the intended redundancy theorem because a codeword is not the
same type as the decoded program.  RLSR1 therefore strengthens the architecture
by separating `Representation` from `Program` at the type level.

This prevents a later proof from silently treating the mutable redundant state
as though it were already the correct executable program.

No counted/core surface is changed.
