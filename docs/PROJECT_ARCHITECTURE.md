# UEOT Project Architecture

## 1. Architectural objective

UEOT develops a unified account of objects and their evolution through philosophical argument, mathematical theory, formal proof and empirical investigation. These activities inform one another while retaining distinct standards of justification.

Two independently maintained books organize the present work. The philosophical book develops a continuous argument about process, objects, identity, purpose, value and knowledge. The mathematical book develops precise definitions, assumptions, theorems, counterexamples and unresolved obligations. Lean supplies machine-checked evidence for the formal statements. Model and empirical work determine which interpretations apply to particular systems.

The feedback is substantive: a philosophical distinction can motivate a new mathematical question; a theorem or counterexample can require a philosophical revision. Neither book is reduced to a directory of the other book's results. Governance records source identity and change decisions without turning an adopted position into a theorem or an empirical result.

The structure makes every mathematical or scientific claim answer four questions:

1. What is its source specification?
2. What assumptions does it depend on?
3. What has actually been proved?
4. What observation could confirm, constrain, or falsify it?

## 2. Current top-level responsibilities

| Path | Current responsibility |
|---|---|
| `constitution/` | Canonical invariants and change control |
| [philosophy/](../philosophy/README.md) | Independently maintained philosophical book and its source history |
| [mathematics/](../mathematics/README.md) | Independently maintained mathematical book and immutable mathematical sources |
| [core/](../core/README.md) | Domain-neutral specification registry, bridges, models and status |
| `formalization/` | Lean and other machine verification |
| `physics/` | Physical realization programs |
| `validation/` | Benchmarks, experiments, data and falsification |
| `research/` | RFCs, audits, prior art and open problems |
| `applications/` | Engineering and downstream domain applications |
| [publications/](../publications/README.md) | Dated publication and release snapshots |
| `archive/` | Superseded snapshots and historical material |
| `docs/` | Repository-wide architecture and contributor documentation |
| `.github/` | CI and repository automation |

### The two independently maintained books

The current philosophical manuscript is
[philosophy/UEOT_PHILOSOPHY.md](../philosophy/UEOT_PHILOSOPHY.md).
The current mathematical manuscript is
[mathematics/UEOT_MATHEMATICS.md](../mathematics/UEOT_MATHEMATICS.md).
Each book has its own argument, version, sources and generated reading formats.
Cross-references explain how a mathematical result bears on a philosophical
claim, including the assumptions required by the interpretation.

The exact frozen Core v3.0 source lives at
[mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md](../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md).
It remains distinct from the maintained mathematical book. The original
philosophical LaTeX source lives under
[philosophy/source/original/](../philosophy/source/original/README.md), extracted
historical texts under `philosophy/source/extracted/`, and the former book
scaffolding under [philosophy/source/legacy/](../philosophy/source/legacy/README.md).
The former root `book/` and `source/` layouts have been retired.

### 2.1 `constitution/`

This remains the governance root while existing change-control rules reference it.

Authoritative responsibilities:

- constitutional invariants,
- canonical claim registry,
- glossary for protected terms,
- change-control process,
- methodological constraints.

A constitution statement is not automatically a mathematical theorem.

### 2.2 `core/`

This is the domain-neutral theory registry and coordination layer. Full
mathematical exposition lives in `mathematics/`; the identity of the frozen
specification is recorded by
[core/specifications/manifest.yaml](../core/specifications/manifest.yaml).

Internal responsibilities:

```text
core/
├── specifications/      # specification identities, manifests and source pointers
├── propositions/        # stable proposition/P-ID registry and dependency graph
├── bridges/             # domain-neutral bridge statements
├── models/              # canonical models/countermodels
├── status/              # coverage, consistency and release state
└── README.md
```

The Core must stay independent of any one application domain. A physical or biological example may motivate a definition, but it cannot silently become part of the generic theorem.

The [current Core status](../core/status/CURRENT.md) records 106/106 proved
source P-IDs for frozen v3.0. The compression disposition is 11 generated,
89 retained adapters and 6 retained boundaries. Four registered generators
therefore do not constitute a rederivation of every source contract. Completion
of these conditional contracts does not by itself establish an unconditional
unified theory or empirical confirmation of the program.

### 2.3 `formalization/`

Machine verification is a separate epistemic layer.

Current active package:

```text
formalization/ueot-core/
├── UEOT/
├── docs/
├── lakefile.lean
├── lake-manifest.json
└── lean-toolchain
```

Rules:

- all official modules must be imported by the default build target or explicitly checked by CI;
- `sorry`, `sorryAx`, and UEOT-specific proof axioms are forbidden for proved status;
- theorem count is not source coverage;
- proposition status is promoted only after semantic matching to the source P-ID;
- dependency locks are preserved.

Future sector libraries should be separate packages or clearly separated namespaces, for example `formalization/ueot-qm/`, rather than smuggling physical axioms into the generic Core.

### 2.4 `physics/`

Physics is a first-class realization layer because it is the most demanding test of the unification program.

Planned structure:

```text
physics/
├── foundations/         # Core → physical-object/process interface
├── qm/                  # finite/infinite-dimensional quantum theory
├── many-body-open/      # statistical, open and many-body systems
├── qft/                 # relativistic free/interacting fields
├── rg-eft/              # Wilsonian RG and EFT, explicitly typed
├── spacetime-gravity/   # relativistic spacetime/gravity program
├── phenomenology/       # measurable consequences
├── interfaces/          # bridge assumptions and external physical inputs
└── README.md
```

Every sector document must distinguish:

- **Core-derived** structure;
- **bridge theorem**;
- **sector-selection axiom/principle**;
- **standard physical input**;
- **conjecture**;
- **derived observable**.

Object-RG, process coarse-graining, and Wilsonian RG are distinct objects unless a bridge theorem proves a relation.

### 2.5 `validation/`

No physical program is closed by explanation alone.

Planned structure:

```text
validation/
├── benchmarks/          # known-theory recovery tests
├── experiments/         # experimental protocols
├── data/                # data schemas, provenance, adapters; not uncontrolled dumps
├── pipelines/           # reproducible analysis code
├── falsification/       # explicit null tests and failure criteria
├── reports/             # dated results
└── README.md
```

Validation reports must identify theory version, proposition/claim IDs, assumptions, dataset or device provenance, statistical procedure, and pass/fail interpretation.

### 2.6 `research/`

This is where unresolved work belongs before promotion.

```text
research/
├── rfcs/
├── audits/
├── prior-art/
├── open-problems/
├── derivations/
└── migration/
```

Research notes may be aggressive and exploratory, but they must not masquerade as canonical Core.

### 2.7 `applications/`

Downstream engineering and cross-domain applications live here only after their dependency on Core/physics is explicit.

Examples include AI architectures, QCVV tooling, control/treasury systems, biology, cognition, and socioeconomic models.

Applications may contribute counterexamples or empirical pressure back upstream; they do not redefine the Core by analogy.

### 2.8 `publications/`

Publications preserve **dated snapshots of a theory state**: papers, figures
and release artifacts intended for citation or distribution. Ongoing book
development takes place in `philosophy/` and `mathematics/`. A book edition may
be released here with its provenance while its maintained source remains in
the corresponding book directory.

The [publication guide](../publications/README.md) identifies the maintained
books and the metadata required to interpret a snapshot. A release records
its source version and commit, relevant mathematical and formalization state,
and any model or validation reports it relies on. A paper may simplify or lag
the maintained theory; its claims are assessed against the state it cites.

### 2.9 `archive/`

Superseded material is retained for provenance. Archiving means “not active,” not “wrong” and not “delete.”

## 3. Claim and truth-state model

Every important claim should eventually carry:

- stable ID,
- layer,
- maturity,
- dependencies,
- source location,
- formal theorem(s), if any,
- physical inputs, if any,
- validation target, if any.

Allowed maturity states:

```text
canonical
proved
partial
pending
conjecture
empirical
deprecated
```

These states are deliberately not a single linear scale. For example, an empirical claim can be well tested without being a theorem, and a mathematical theorem can be proved while its physical interpretation remains conjectural.

## 4. Promotion gates

### 4.1 Core theorem → proved

Required:

1. exact source statement identified;
2. Lean statement semantically matched;
3. theorem imported into an official build target;
4. pinned build passes;
5. no prohibited axioms;
6. coverage ledger updated.

### 4.2 Core → physics bridge

Required:

1. domain/codomain types stated;
2. every added physical assumption listed;
3. generic Core and sector-specific principle separated;
4. bridge theorem or explicit conjecture label;
5. known-theory benchmark identified.

### 4.3 Physics claim → empirical

Required:

1. observable defined;
2. competing/null model stated;
3. data/experiment provenance stated;
4. uncertainty/statistics procedure fixed;
5. failure criterion stated in advance where possible.

## 5. Source migration and historical provenance

The active book layout is now `philosophy/` and `mathematics/`. Source migration
preserves original bytes or records how historical material was consolidated.
Historical RFCs and decisions retain their original wording and paths; their
references describe the repository state in which they were written.

| Historical path or artifact | Current role or destination |
|---|---|
| `constitution/` | remains active governance |
| `formalization/` | remains active machine-verification layer |
| `domains/formal-foundations/` | legacy precursor; active work moves to `core/` + `formalization/` |
| `domains/physics-cosmos/` | legacy precursor; active work moves to `physics/` |
| other `domains/*` | migrate gradually to `applications/domains/` if retained |
| `book/` | retired root layout; historical scaffolding consolidated in `philosophy/source/legacy/` |
| `source/extracted/` | historical extracted texts moved to `philosophy/source/extracted/` |
| `source/paper/` | retired source entry; original LaTeX is under `philosophy/source/original/` |
| Core Mathematics v3.0 source | exact hash-matched original installed in `mathematics/source/core-v3.0/`; identity registered in `core/specifications/manifest.yaml` |
| root PDF/ZIP | preserved at their historical addresses for compatibility and provenance |
| `council/` | preserve because constitution currently references its decisions; future decision system may live under `research/` or governance |

The [philosophical source provenance](../philosophy/source/SOURCE_PROVENANCE.json)
and [Core specification manifest](../core/specifications/manifest.yaml)
identify the retained sources. New work should use the current book paths;
archival references continue to document earlier states.

## 6. Current development order

1. Develop the remaining mathematical connections from the completed frozen
   Core contracts, using the existing proof infrastructure and explicit
   assumptions.
2. Check each connection through concrete models, counterexamples and the
   distinction between an existence theorem and an executable construction.
3. Integrate precise proofs and open obligations into the mathematical book,
   then reconsider the philosophical arguments they support or constrain.
4. Develop philosophical questions and objections in their own right, and
   translate mathematical consequences into explicit research problems.
5. Validate implementation changes locally before publishing the necessary
   commits and PRs; release each book with its own version and provenance.

The central objective is a progressively stronger UEOT mathematical theory and
philosophical account, with each claimed advance supported by the appropriate
argument, proof or observation.
