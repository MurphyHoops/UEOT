# UEOT Core Compression Coverage

This file is the human-readable counted-status view for the post-106
compression mission. It is **not** the Core v3 source-proof ledger and never
changes the completed **106/106 FULL-GREEN** source status.

## Frozen baseline

- Core v3 source P-IDs: **106**
- Core v3 source proofs: **106/106 FULL-GREEN**
- mission-start main: `29d946422f02bb025bd5d450acc434486ecdb422`
- canonical source SHA-256:
  `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`

## Compression evidence state

| metric | count |
|---|---:|
| source P-IDs analyzed | 3 / 106 |
| schema-classified P-IDs | 3 / 106 |
| fully Lean-rederived P-IDs | 2 / 106 |
| counted compressed P-IDs | 0 / 106 |
| confirmed irreducible/domain adapters | 0 / 106 |
| counted meta-generators | 0 |

No compression result is counted yet because the new governance/CI lifecycle
has not completed a main + ledger promotion.

## Current generator evidence

### M-QD-01 — Quotient Descent

State: **LEAN_GREEN, not counted**

- generic surjective fibre-compatible descent and uniqueness: Lean proved;
- P-DYN-01: partial specialization only;
- preserved boundary: set-level descent does not establish measurable kernel
  descent.

### M-TC-01 — Transport Certificate Calculus

State: **CROSS_FAMILY_GREEN, not counted**

- generic exact two-stage composition: Lean proved;
- generic approximate two-stage defect bound: Lean proved;
- heterogeneous additive finite-chain accumulation: Lean proved;
- P-API-01: full exact + approximate source-facing rederivation;
- P-ID-01: full source-facing supremum rederivation.

## Counting rule

A generator or mapping is counted only after the complete compression
lifecycle:

`SCHEMA -> LEAN -> SOURCE MATCH -> ASSUMPTION AUDIT -> FEATURE CI ->
CLEAN INTEGRATION -> PR CI -> MAIN CI -> LEDGER PR -> LEDGER MAIN CI -> COUNTED`.

Hypotheses, partial mappings and local-only builds are never counted.
