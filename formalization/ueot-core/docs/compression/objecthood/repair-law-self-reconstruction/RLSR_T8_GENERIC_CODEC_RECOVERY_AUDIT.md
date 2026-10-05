# RLSR-T8 — generic codec recovery / identity-basin audit

Status: **LOCAL PASS**

## Why this tightening matters

The original RLSR5 `ProgramReconstructionBasin` was a correct triple-code
validity basin, but its name could be read as if every member reconstructs one
specific original source program.  Those are different statements.

T8 lifts reconstruction to any `TrustedRepairCodec` and separates:

1. `CodecValidityBasin`: the current representation decodes to some valid repair
   program;
2. `CodecExactSourceBasin codec r`: it decodes exactly to designated source `r`;
3. `CodecDynamicsSourceBasin ... r`: it decodes to any program in the same
   carrier-level physical transition class as `r`.

Lean proves exact one-step characterization of the generic validity basin,
exact-source -> dynamics-source, dynamics-source -> validity when the source is
valid, and exact source-codeword reconstruction from any corruption relation a
codec declares correctable.

## Scientific consequence

The triple repetition construction is now conceptually only one concrete codec /
fault-model instance.  The RLSR reconstruction semantics itself is no longer
tied to three replicas.  This leaves room for stronger finite codes without
changing the upper Objecthood/runtime/path-law layers.
