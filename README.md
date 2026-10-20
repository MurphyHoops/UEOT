# UEOT — Universal Evolutionary Object Theory

UEOT studies objects, persistence, evolution and purpose through **two independently maintained books**, a machine-checked mathematical core, and explicit scientific interfaces. The books develop different kinds of argument and can each be read on their own.

## The two books

| Work | Scope | Read |
|---|---|---|
| **客体、演化与意义 — 一种开放的统一自然哲学** | Philosophical arguments about process, relation, identity, life, purpose, meaning, freedom and a shared world; six parts and thirty chapters | [Markdown](./philosophy/UEOT_PHILOSOPHY.md) · [PDF](./philosophy/UEOT_PHILOSOPHY.pdf) · [LaTeX](./philosophy/UEOT_PHILOSOPHY.tex) |
| **UEOT 数学著作** | Definitions, assumptions, proofs, counterexamples, algorithms and explicit Lean correspondences; the complete original Core together with later mathematical developments | [Markdown](./mathematics/UEOT_MATHEMATICS.md) · [PDF](./mathematics/UEOT_MATHEMATICS.pdf) · [LaTeX](./mathematics/UEOT_MATHEMATICS.tex) |

Philosophy develops and defends concepts and normative arguments. Mathematics tests precise statements, derives their consequences and exhibits their limits. A theorem can require a philosophical claim to be revised; the interpretation of that theorem still needs an argument. Scientific applications add their own identification, measurement and empirical obligations.

The historical [43-page philosophical paper](./UEOT_v3_top.pdf) is preserved, and the exact [Core Mathematics v3.0 source](./mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md) is now synchronized byte for byte. The maintained books have their own version history; neither silently replaces a frozen historical source.

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
| `philosophy/` | independent philosophical book, print edition and original-source provenance |
| `mathematics/` | independent mathematical book, proofs and frozen Core source |
| `constitution/` | governance, canonical invariants, claim-control and glossary |
| `core/` | active domain-neutral UEOT theory and mathematical specifications |
| `formalization/` | machine-checked formal libraries and proof ledgers |
| `physics/` | physical realization programs: QM, QFT, many-body, spacetime/gravity |
| `validation/` | benchmarks, experiments, data interfaces, falsification reports |
| `research/` | RFCs, audits, prior-art reviews, open problems and migration work |
| `applications/` | engineering and downstream cross-domain uses |
| `publications/` | papers, monograph snapshots and release artifacts |
| `archive/` | superseded or historical material retained for provenance |

The superseded `book/` dossiers have been consolidated into a [small historical archive](./philosophy/source/legacy/README.md). Original-paper extracts now live with the philosophy source. The former `source/paper/` links were redundant with the preserved root artifacts and have been retired. Meaningful domain, council and architectural materials remain in place.

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

A successful Lean build certifies the imported code under its stated assumptions. An automatic governance-only CI result does not report a Lean run. Neither result alone certifies semantic coverage of every natural-language UEOT claim.

## Historical manuscript

The original manuscript remains preserved:

- [UEOT_v3_top.pdf](./UEOT_v3_top.pdf)
- [LaTeX source archive](./UEOT_v3_top%5B1%5D.zip)

The original LaTeX files are also available in [philosophy/source/original](./philosophy/source/original/README.md). Source hashes and the directory migration are recorded in [SOURCE_PROVENANCE.json](./philosophy/source/SOURCE_PROVENANCE.json).

## Branch policy

Active development is integrated through `main`. Complete and verify a coherent local change before submitting the necessary commits and PRs. The Core cloud build has a manual entry; the local build and evidence workflow is described in [Compression Operations](./formalization/ueot-core/docs/compression/COMPRESSION_OPERATIONS.md).

## License

Repository-authored manuscript material is released under the terms described in [LICENSE](./LICENSE). Third-party bundled source files retain their own licenses.
