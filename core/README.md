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

## Source and maintained books

The exact [Core Mathematics v3.0 source](../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md)
is synchronized and retains the SHA-256 and 106 P-IDs recorded in
`specifications/manifest.yaml`. [Current state](./status/CURRENT.md) points to the
authoritative coverage and compression records.

The [mathematical book](../mathematics/UEOT_MATHEMATICS.md) develops the definitions,
proofs and formal correspondences. The independent
[philosophical book](../philosophy/UEOT_PHILOSOPHY.md) develops the conceptual and
normative arguments. Their interfaces are explicit, and each book can evolve
without rewriting the other's kind of claim.
