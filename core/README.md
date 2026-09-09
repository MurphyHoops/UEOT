# UEOT Core

This directory is the active home of the **domain-neutral UEOT theory**.

The Core should contain only structures that are intended to apply before selecting a particular physical, biological, cognitive, social, or engineering realization.

## Planned contents

- `specifications/` — canonical mathematical and conceptual specifications
- `propositions/` — stable P-ID/claim registry and dependency graph
- `bridges/` — generic bridge statements whose endpoints are explicitly typed
- `models/` — canonical models, countermodels and examples
- `status/` — consistency, coverage and release state

## Separation rule

A theorem may use examples from physics or other domains, but a domain-specific axiom must not be imported into the generic Core without being explicitly reclassified.

Machine proofs of Core statements live under `formalization/`, not here. The natural-language/mathematical source statement remains independently auditable.

## Current migration state

The current Core v3 mathematical source referenced by the Lean coverage ledger has not yet been fully synchronized into this new directory. Until synchronization is complete, the coverage ledger under `formalization/ueot-core/docs/` records the active source identity and proof status.
