# UEOT — Universal Evolutionary Object Theory

UEOT studies objects, persistence, evolution and purpose through **three independently maintained books**, a machine-checked mathematical core, and explicit scientific interfaces. The books develop different kinds of argument and can each be read on their own.

## Three independently maintained books

| Work | Scope | Read |
|---|---|---|
| **客体、演化与意义 — 一种开放的统一自然哲学** | Philosophical arguments about process, relation, identity, life, purpose, meaning, freedom and a shared world; six parts and thirty chapters | [Markdown](./philosophy/UEOT_PHILOSOPHY.md) · [PDF](./philosophy/UEOT_PHILOSOPHY.pdf) · [LaTeX](./philosophy/UEOT_PHILOSOPHY.tex) |
| **UEOT 数学著作** | Definitions, assumptions, proofs, counterexamples, algorithms and explicit Lean correspondences; the complete original Core together with later mathematical developments | [Markdown](./mathematics/UEOT_MATHEMATICS.md) · [PDF](./mathematics/UEOT_MATHEMATICS.pdf) · [LaTeX](./mathematics/UEOT_MATHEMATICS.tex) |
| **《UEOT物理学》 v3.9** | Physical assumptions, quantum/QFT derivations, falsifiable predictions, proof status and limits; maintained separately from Core mathematics | [Markdown](./physics/qm/book/UEOT_PHYSICS.md) · [PDF](./physics/qm/book/UEOT_PHYSICS.pdf) · [LaTeX](./physics/qm/book/UEOT_PHYSICS.tex) |

Philosophy develops concepts and normative arguments; mathematics verifies conditional claims and their limits; physics separately records sector-specific assumptions, derivations, and falsifiable tests. The three books remain independent reading works, not mutually interchangeable certificates.

The historical [43-page philosophical paper](./UEOT_v3_top.pdf) is preserved, and the exact [Core Mathematics v3.0 source](./mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md) is now synchronized byte for byte. The maintained books have their own version history; neither silently replaces a frozen historical source.

## Core objective

The project aims to determine how far a single UEOT object/process framework can be made mathematically precise, formally verified, physically predictive, and empirically vulnerable.

This imposes four disciplines:

1. **Core before analogy.** Domain applications do not define the core.
2. **Explicit proof status.** Written mathematical proofs and machine-checked results have distinct evidence. Formal promotion requires semantic matching to the source statement and an actually checked public Lean target.
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

**Current Core status — 2026-11-11:** start at the [current state and reading route](./core/status/CURRENT.md), then the [Lean package](./formalization/ueot-core/README.md). Core content is **CLASSIFIED_CORE_CLOSED** within its stated conditional scope; empirical support remains **UNVERIFIED**.

| Layer | Adopted state and evidence |
|---|---|
| Frozen Core Mathematics v3.0 | [106/106 FULL-GREEN source contracts](./formalization/ueot-core/docs/V3_COVERAGE_STATUS.md); the exact source is synchronized. Later results do not increase this frozen P-ID count. |
| Whole Core conditional mathematics and decision contracts | The whole conditional contract and the finite-wallet, decision-representation and S/G mechanism-decision results remain completed under their registered assumptions. [Current contract map](./core/status/CURRENT.md#completed-contracts-and-their-evidence) |
| Same-source Core definitive theory | [Classified claims, real regenerative source, permitted control, inheritance and representation](./formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_theory_closure_v1/README.md). Growth optimality is one sourced purpose branch; philosophical and normative arguments retain their own justification. |
| PR #446: finite hardening | [Task-dependent 2/3/4 representation and the public-response rank-three boundary](./mathematics/review/CORE_DEFINITIVE_FREEZE_2026-11-11/README.md) have written proofs and exact checks; no new complete dedicated Lean endpoints were claimed for them. |
| PR #447: exact growth and internal attainment | [Completed, publicly imported extension](./formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_growth_classification_v1/README.md): three Lean modules prove the optimal factor max(1, λ₀, λ₁), full permitted-history population bounds and the two existing internal programs' attainment iff conditions on the strictly positive probability domain. |

The growth extension's formal contract uses finite-time positive exponential bounds and the least common positive upper base. Root-limit/limsup interpretations are written analysis consequences. Its scope does not enlarge the original selection-feedback contract, assert almost-sure survival, or establish natural universality.

The [2026-10-26 audit](./mathematics/review/MATHEMATICAL_CLOSURE_AUDIT_2026-10-26.md) is preserved as a historical checkpoint. Its unpublished-candidate and next-step descriptions are not the current task queue. Completed Core contracts are not reopened merely because an older roadmap says OPEN; new research needs a stated question and bounded completion conditions.

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
- **written proof** — an explicit mathematical argument whose dedicated formal endpoint has not necessarily been added
- **philosophical argument** — a reasoned conceptual or normative claim, assessed independently of a Lean build
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

Active development is integrated through `main`. Complete and verify a coherent local change before submitting the necessary commits and PRs. Current Core validation is local under the [branch-governance policy](./docs/REPOSITORY_BRANCH_GOVERNANCE.md#11-ci-efficiency-rules) and [Compression Operations](./formalization/ueot-core/docs/compression/COMPRESSION_OPERATIONS.md). Documentation-only maintenance checks its changed content and links; unchanged proof evidence is reused with matching source identities. Historical CI receipts remain historical, and an absent cloud run is not a successful build.

## Copyright, research licensing and publication

This repository uses **layered licensing**. The earlier CC BY 4.0 grant
remains valid for historically licensed research expression, including
material already published in the three books. Future original **open
scientific research prose and figures** are generally CC BY 4.0 where the
contributor has the rights to grant it; future *new book edition content*,
Lean/Python code, raw data and third-party assets have separately
identified terms.

The physics sector is not excluded: see its
[license map](./physics/LICENSING.md) and the
[《UEOT物理学》 edition-rights record](./physics/qm/book/PUBLICATION_RIGHTS.md).
Current Lean or research-code files have **not** been blanket-relicensed
to Apache-2.0. Existing book contents have **not** become exclusive.

Start at [LICENSE](./LICENSE), [LICENSE_SCOPE.md](./LICENSE_SCOPE.md),
[COPYRIGHT.md](./COPYRIGHT.md), and the
[original notice archive](./LICENSES/README.md). Future publication
and software releases must carry their own precise rights metadata.
