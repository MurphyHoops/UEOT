# UEOT Core

This directory is the active home of the **domain-neutral UEOT theory**.

The Core should contain only structures that are intended to apply before selecting a particular physical, biological, cognitive, social, or engineering realization.

## Contents

- `specifications/` — canonical mathematical and conceptual specifications
- `propositions/` — stable P-ID/claim registry and dependency graph
- `bridges/` — generic bridge statements whose endpoints are explicitly typed
- `models/` — canonical models, countermodels and examples
- `status/` — consistency, coverage, release state, and theory-evolution maintenance

## Separation rule

A theorem may use examples from physics or other domains, but a domain-specific axiom must not be imported into the generic Core without being explicitly reclassified.

Machine proofs of Core statements live under `formalization/`, not here. The natural-language/mathematical source statement remains independently auditable.

## Theory evolution and Lean feedback

UEOT Core is maintained bidirectionally: the current canonical source constrains Lean formalization, while proof failures, counterexamples, stronger machine-checked lemmas, and rigorous results recovered from historical versions feed back into an explicit versioned audit.

Maintenance documents:

- `status/EVOLUTION_MAINTENANCE.md` — Core invariants, formalization-feedback classes, source-version rules, and merge discipline;
- `status/HISTORICAL_RECOVERY_QUEUE.md` — useful historical derivations classified as already integrated, Lean regression guards, next-version candidates, sector-only results, or rejected overclaims;
- `status/CURRENT.md` — current route and active proof lanes. Source-level proof counts are intentionally not duplicated there; `formalization/ueot-core/docs/V3_COVERAGE_STATUS.md` is authoritative.

Historical versions are immutable derivation archives. Recovering a result means importing it with provenance and independent revalidation, not silently rewriting v3 or copying later sector assumptions into the generic Core.

## Current migration state

The current Core v3 mathematical source referenced by the Lean coverage ledger has not yet been fully synchronized into this new directory. Until synchronization is complete, the coverage ledger under `formalization/ueot-core/docs/` records the active source identity and proof status.
