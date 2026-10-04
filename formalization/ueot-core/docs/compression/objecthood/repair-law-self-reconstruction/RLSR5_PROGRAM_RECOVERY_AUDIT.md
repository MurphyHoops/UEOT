# RLSR5 — repair-program recovery dynamics audit

Status: **LOCAL PASS**

## Result

The trusted triple decoder is now a runtime PMF kernel on mutable program
representation.  The exact basin is

`ProgramReconstructionBasin = { e | decoded(e) is behaviorally valid }`.

Lean proves both directions:

`one reconstruction step stays in the valid redundant target`
**iff** `e` belongs to that basin.

Valid codewords are fixed points/absorbing targets.  The RLSR4 single-replica
fault class is proved to lie inside this exact basin and is reconstructed exactly
to the original codeword.

## Independent audit / optimization

The scratch preflight only proved the single-corruption sufficient theorem.
That leaves the scientific recovery domain implicit.  RLSR5 strengthens it to
an exact basin characterization, which makes later joint recovery assumptions
explicit and prevents accidental universalization to observations whose decoded
program is invalid.

No external correct program is used at runtime: the kernel depends only on the
current representation through `tripleProgramDecode`.
