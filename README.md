# UEOT — Universal Evolutionary Object Theory

UEOT is being developed as a **unified derivational research program**: a domain-neutral theory of objects and evolution, a machine-checked mathematical core, explicit bridges into physics, and empirical tests capable of falsifying the resulting claims.

The repository is no longer organized primarily as a manuscript or as a collection of parallel disciplines. Its active structure is organized by **epistemic role and dependency**:

```text
Constitution / canonical claims
            ↓
      UEOT Core specification
            ↓
   machine formalization (Lean)
            ↓
 explicit bridge theorems + declared sector inputs
            ↓
      Physics / UEOT-QM / QFT / gravity
            ↓
   benchmarks, experiments, falsification
            ↓
 applications and cross-domain extensions
```

## Core objective

The project aims to determine how far a single UEOT object/process framework can be made mathematically precise, formally verified, physically predictive, and empirically vulnerable.

This imposes four disciplines:

1. **Core before analogy.** Domain applications do not define the core.
2. **Proof before promotion.** A theorem is not marked proved until its source statement is semantically matched and the imported Lean target builds.
3. **Bridges are explicit.** Generic UEOT, quantum-specific assumptions, physical constants, symmetry inputs, and effective-theory assumptions must not be silently identified.
4. **Validation closes the loop.** Physical extensions must terminate in benchmarks, observables, data, or falsification criteria.

## Active repository layers

| Path | Role |
|---|---|
| `constitution/` | governance, canonical invariants, claim-control and glossary |
| `core/` | active domain-neutral UEOT theory and mathematical specifications |
| `formalization/` | machine-checked formal libraries and proof ledgers |
| `physics/` | physical realization programs: QM, QFT, many-body, spacetime/gravity |
| `validation/` | benchmarks, experiments, data interfaces, falsification reports |
| `research/` | RFCs, audits, prior-art reviews, open problems and migration work |
| `applications/` | engineering and downstream cross-domain uses |
| `publications/` | papers, monograph snapshots and release artifacts |
| `archive/` | superseded or historical material retained for provenance |

Existing `book/`, `domains/`, `source/`, and `council/` directories are retained during non-destructive migration. They are not deleted merely to make the repository look cleaner.

See [Project Architecture](./docs/PROJECT_ARCHITECTURE.md) for the target structure and migration rules.

## Formal verification

The active Lean package is under:

- [formalization/ueot-core](./formalization/ueot-core)
- [v3 coverage ledger](./formalization/ueot-core/docs/V3_COVERAGE_STATUS.md)

The source-level completion gate is based on the UEOT Core v3 proposition inventory, not on Lean theorem count or Lake job count.

## Physics status

Physics is treated as the strongest stress test of UEOT, not as a decorative application. The active top-level `physics/` layer is intended to separate:

- generic UEOT consequences,
- quantum-sector selection assumptions,
- standard physical inputs,
- bridge theorems,
- derived observables,
- unresolved conjectures.

In particular, Object-RG, process coarse-graining, and Wilsonian RG must remain separately typed unless an explicit bridge theorem connects them.

## Truth-state vocabulary

Repository claims should use explicit maturity labels:

- **canonical** — accepted governance/core statement
- **proved** — source-matched and machine-checked theorem
- **partial** — a strict subset or weakened form is machine-checked
- **pending** — formal target exists or is identified but not proved
- **conjecture** — mathematically/physically proposed but not established
- **empirical** — supported or rejected by a stated data/experiment pipeline
- **deprecated** — retained for provenance but no longer active

A green CI build certifies imported Lean code only. It does not by itself certify semantic coverage of every natural-language UEOT claim.

## Historical manuscript

The original manuscript remains preserved:

- [UEOT_v3_top.pdf](./UEOT_v3_top.pdf)
- [LaTeX source archive](./UEOT_v3_top%5B1%5D.zip)

These are historical/publication artifacts. They do not override newer canonical Core specifications, formal proof ledgers, or explicit research resolutions.

## Branch policy

Active development is performed on `main`. The GitHub repository setting may still display `master` as the default branch until that repository setting is changed; no independent theory-development line should be maintained on `master`.

## License

Repository-authored manuscript material is released under the terms described in [LICENSE](./LICENSE). Third-party bundled source files retain their own licenses.
