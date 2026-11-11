# UEOT Physics

Physics is the primary realization and falsification stress test for UEOT.

This layer must not treat “UEOT interpretation” as equivalent to derivation. Every result should state which part comes from generic UEOT Core, which part is supplied by a sector-selection principle or standard physical input, and which part is still conjectural.

## Target sectors

- `foundations/` — typed Core→physics interface
- `qm/` — finite- and infinite-dimensional quantum theory
- `many-body-open/` — open systems, statistical mechanics and many-body theory
- `qft/` — relativistic free and interacting quantum fields
- `rg-eft/` — Wilsonian RG and effective field theory
- `spacetime-gravity/` — relativistic spacetime and gravity program
- `phenomenology/` — measurable consequences
- `interfaces/` — explicit added axioms, constants, symmetry assumptions and bridge contracts

## Mandatory typing discipline

Object-RG, process coarse-graining, and Wilsonian RG remain distinct constructions unless a bridge theorem relates them.

Quantum-specific structure must not be claimed as a consequence of generic UEOT Core when an additional quantum-sector selection principle is required.

## Validation

Known-theory recovery and new predictions belong in `validation/`. A physics document is incomplete if it cannot identify what calculation, benchmark, or experiment would pressure it.

## Copyright and research reuse

For the third formal book `qm/book/UEOT_PHYSICS.{md,tex,pdf}` and the
separate physics research, Lean source, Python kernel, experiments and data,
see [Physics licensing](LICENSING.md) and
[book-version rights](qm/book/PUBLICATION_RIGHTS.md). Historically licensed
CC BY 4.0 expression remains available under its earlier grant. Future
original research explanations remain open under the root policy; no code,
third-party material or formal-book addition is silently relicensed.
