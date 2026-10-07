# Scientific Closure Source Manifest

Program-start base (historical provenance):
`main@f779f7c12f68ab5571e3550edfca475ae61465ee`.

This manifest records the frozen inputs used when the local program began.  It
is intentionally not rewritten when the promotion branch is later rebased onto
a newer canonical `main`.

## Project planning sources

| File | SHA-256 | Role |
|---|---|---|
| `CORE_V3_OPEN_PORT_MATRIX.md` | `f71ba345602ee750116b0481dce7d78cf212a0fb02bccac79d482703ada0b20a` | C1–C7 package contracts, inputs, acceptance and stop conditions |
| `CORE_V3_POST_CORE_SCIENTIFIC_CLOSURE.md` | `669ec5667575c9dbe75645fa2c00501e4cfbec68ca8a3420825f4b6d08f41569` | Core-v3 scientific-state audit and reclassification |
| `THEORY_COMPLETION_ROADMAP_V2.md` | `64ab8d688f7ddfc7c739dd4af3b7760eba362190cd8897a605644b0fbd95cd07` | execution order, G1/G2 review gates, risk/stop rules |

These are planning/source documents, not evidence that the planned tasks were
already executed. Their older repository snapshots are treated as historical
inputs; current-state claims below are rechecked against the program base.

## Current repository facts rechecked at program start

- Core v3 source coverage: **106/106 FULL-GREEN**;
- unique P-IDs: **106**;
- partial: **0**;
- pending: **0**;
- compression dispositions: **11 generated + 89 retained_adapter + 6 retained_boundary = 106**;
- counted generators: **M-QD-01, M-TC-01, M-PE-01, M-OI-01**;
- old Theory Completion status: **P0–P12 CLOSED / PROGRAM_COMPLETE**;
- reproducibility hygiene boundary still recorded by canonical status docs:
  exact canonical source bytes in public repo are pending synchronization.

No C-package may overwrite these historical/canonical states merely to simplify
its own narrative.
