# UEOT Project Architecture

## 1. Architectural objective

UEOT should be organized as a **derivation-and-validation system**, not as a set of equally authoritative domain essays.

The repository architecture therefore follows the dependency chain

```text
governance
   ↓
domain-neutral core
   ↓
formal proof
   ↓
sector bridges + explicit added assumptions
   ↓
physical theories
   ↓
empirical validation
   ↓
applications / publications
```

The purpose of the structure is to make every serious claim answer four questions:

1. What is its source specification?
2. What assumptions does it depend on?
3. What has actually been proved?
4. What observation could confirm, constrain, or falsify it?

## 2. Target top-level structure

```text
UEOT/
├── constitution/        # canonical invariants and change control
├── core/                # domain-neutral theory and source specifications
├── formalization/       # Lean and other machine verification
├── physics/             # UEOT physical realization programs
├── validation/          # benchmarks, experiments, data and falsification
├── research/            # RFCs, audits, prior art, open problems
├── applications/        # engineering and downstream domain applications
├── publications/        # papers, monograph, releases
├── archive/             # superseded snapshots and historical material
├── docs/                # repository-wide architecture and contributor docs
├── .github/             # CI and repository automation
└── README.md
```

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

This is the **source-of-truth theory layer** below governance.

Planned internal structure:

```text
core/
├── specifications/      # complete natural-language/mathematical specifications
├── propositions/        # stable proposition/P-ID registry and dependency graph
├── bridges/             # domain-neutral bridge statements
├── models/              # canonical models/countermodels
├── status/              # coverage, consistency and release state
└── README.md
```

The Core must stay independent of any one application domain. A physical or biological example may motivate a definition, but it cannot silently become part of the generic theorem.

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

Publications are **snapshots of a theory state**, not the source of truth.

Target structure:

```text
publications/
├── papers/
├── book/
├── figures/
└── releases/
```

A paper can lag or simplify the active Core. Release metadata should record the exact theory/formalization commit it represents.

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

## 5. Migration from the current repository

Migration is intentionally non-destructive.

| Current path | Target role |
|---|---|
| `constitution/` | remains active governance |
| `formalization/` | remains active machine-verification layer |
| `domains/formal-foundations/` | legacy precursor; active work moves to `core/` + `formalization/` |
| `domains/physics-cosmos/` | legacy precursor; active work moves to `physics/` |
| other `domains/*` | migrate gradually to `applications/domains/` if retained |
| `book/` | migrate gradually to `publications/book/` |
| `source/paper/` | migrate gradually to `publications/papers/` or release source |
| root PDF/ZIP | preserve until release migration is complete |
| `council/` | preserve because constitution currently references its decisions; future decision system may live under `research/` or governance |

No old material should be deleted until links, provenance, and replacement destinations have been verified.

## 6. Immediate implementation order

1. stabilize UEOT Core v3 source specifications in `core/specifications/`;
2. complete and synchronize the Lean Core package;
3. create explicit Core↔Physics interfaces;
4. synchronize the current UEOT-QM/QFT development into `physics/`;
5. attach benchmark/falsification targets in `validation/`;
6. migrate publication/domain legacy material last.

This ordering reflects the central objective: **a unified theory earns authority from derivation, proof and empirical closure—not from breadth of analogy.**
