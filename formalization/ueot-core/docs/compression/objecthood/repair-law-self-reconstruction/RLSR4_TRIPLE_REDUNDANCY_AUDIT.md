# RLSR4 — finite redundancy source audit

Status: **LOCAL PASS**

## Constructive result

For an arbitrary repair-program type with decidable equality, three mutable
replicas and the trusted equality-majority decoder exactly recover the source
program after replacement of any one replica by any arbitrary program.

The theorem is generic in the program type; it is not a Boolean-only toy.

## Independent negative check

Two literal replicas cannot solve the same exact arbitrary-single-replacement
problem without extra information.  For distinct `r1`, `r2`, the pair obtained
by replacing copy 0 of the `r1` codeword with `r2` is exactly the same pair as
replacing copy 1 of the `r2` codeword with `r1`.  The file proves that no
deterministic decoder can be exact on both sources.

Thus three copies are not merely convenient in this benchmark: they are the
first repetition-code size that removes this exact collision under one arbitrary
replica replacement.

This remains a benchmark, not a universal coding optimality theorem over all
possible non-repetition encodings or side information.
