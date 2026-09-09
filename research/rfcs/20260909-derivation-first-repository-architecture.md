# RFC: Derivation-First UEOT Repository Architecture

Date: 2026-09-09
Status: proposed for architect resolution
Scope: repository architecture, governance wording, active source-of-truth routing

## Problem

The repository was originally organized around a manuscript, book chapters,
domain councils, and parallel disciplinary extensions. That structure no longer
matches the active UEOT research program.

The current mainline now contains a mathematically specified UEOT Core, a Lean
formal-verification program, a large physics/UEOT-QM development line, and
experimental/benchmark work. Treating these as peer "domains" hides the actual
dependency structure and creates source-of-truth ambiguity.

## Proposed rule

Adopt an epistemic/derivational architecture:

```text
constitution / canonical claims
        ↓
domain-neutral UEOT Core
        ↓
machine formalization
        ↓
explicit bridge theorems + declared sector inputs
        ↓
physics and other realization layers
        ↓
validation / falsification
        ↓
applications and publications
```

New active top-level roles:

- `core/`
- `formalization/`
- `physics/`
- `validation/`
- `research/`
- `applications/`
- `publications/`
- `archive/`

`constitution/` remains the governance root.

## Canonical-source change

The historical paper remains a publication artifact and philosophical origin,
but it should no longer be described as the sole canonical mathematical source.

For mathematical claims, the active Core specification and its stable claim/P-ID
registry are the source layer. Lean proofs certify formal statements; they do not
replace source specifications. Physics documents must declare added physical
inputs and cannot silently strengthen generic Core.

## Truth-state discipline

Adopt explicit status labels:

- canonical
- proved
- partial
- pending
- conjecture
- empirical
- deprecated

A green build is necessary but not sufficient for source-level proved status.

## Cross-domain impact

### Formal foundations

The old `domains/formal-foundations/` becomes a historical precursor.
Active mathematical work moves to `core/` and `formalization/`.

### Physics

The old `domains/physics-cosmos/` becomes a historical precursor.
Active work moves to `physics/`, with separate typed sectors and bridge inputs.

### Biology, mind, society, meaning

These remain valuable downstream research programs, but should migrate under
`applications/` or explicitly typed realization layers rather than sharing
authority with the generic Core.

### Publications

Papers and book chapters become snapshots of theory state, not the upstream
source of truth.

## Migration constraints

1. no destructive mass move;
2. no deletion of historical materials;
3. preserve provenance and inbound links;
4. migrate active references first;
5. archive only after replacement paths are verified;
6. keep one active development line on `main`.

## Expected benefit

The repository will make UEOT's strongest claim testable in engineering terms:
whether a single generic theory can survive formal proof, explicit physical
bridging, known-theory recovery, and empirical falsification without relying on
cross-domain analogy.

## Requested resolution

Approve the derivation-first architecture and authorize corresponding updates to
the constitution/method documents and legacy domain-state markers.
