# Architect Resolution: Derivation-First UEOT Repository Architecture

Date: 2026-09-09
Resolution status: approved
RFC: `research/rfcs/20260909-derivation-first-repository-architecture.md`

## Decision

The UEOT repository adopts a derivation-first architecture organized by
epistemic role and dependency rather than by parallel disciplinary domains.

The active dependency chain is:

```text
constitution / canonical claims
        ↓
domain-neutral Core
        ↓
formal verification
        ↓
explicit bridges + declared sector inputs
        ↓
physics / realization layers
        ↓
validation / falsification
        ↓
applications / publications
```

## Canonical routing

- `constitution/` remains the governance root.
- `core/` becomes the active domain-neutral theory/specification layer.
- `formalization/` remains the machine-proof layer.
- `physics/` becomes the active physics realization layer.
- `validation/` becomes the benchmark/experiment/falsification layer.
- `research/` is the staging layer for RFCs, audits, prior art and open work.
- `applications/` is downstream.
- `publications/` contains theory snapshots.
- `archive/` preserves superseded material.

## Source-of-truth discipline

The historical manuscript remains preserved and citable but no longer overrides
newer Core mathematical specifications, formal coverage ledgers, or explicitly
approved research resolutions.

A mathematical theorem is promoted to `proved` only when:

1. the source statement is identified;
2. the Lean statement is semantically matched;
3. the theorem is included in an official build target;
4. the pinned build passes;
5. prohibited proof holes/axioms are absent;
6. the coverage ledger is updated.

## Physics discipline

Physics extensions must separately identify:

- generic Core-derived structure;
- bridge theorem;
- sector-selection principle;
- standard physical input;
- conjecture;
- derived observable.

Object-RG, process coarse-graining, and Wilsonian RG are not interchangeable by
name.

## Migration decision

The migration is non-destructive. Existing `book/`, `domains/`, `source/`,
and `council/` material remains in place until replacement paths and provenance
are verified.

## Follow-up

1. update constitution/method wording to reflect canonical routing;
2. mark legacy domain state files as historical precursors;
3. synchronize current Core specifications into `core/specifications/`;
4. synchronize current UEOT-QM/QFT work into `physics/`;
5. attach validation targets to physics claims;
6. migrate publication artifacts last.

## Unresolved

- GitHub still reports `master` as the repository default branch setting even
  though active development is on `main`.
- The complete UEOT Core v3.0 source specification still needs to be synchronized
  into the public repository without altering its exact content.
