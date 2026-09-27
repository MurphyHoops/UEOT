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
| source P-IDs analyzed | 6 / 106 |
| schema-classified P-IDs | 6 / 106 |
| fully Lean-rederived P-IDs | 3 / 106 |
| counted compressed P-IDs | 0 / 106 |
| final dispositions assigned | 0 / 106 |
| generated final dispositions | 0 / 106 |
| retained domain adapters | 0 / 106 |
| retained boundary/no-go results | 0 / 106 |
| unresolved final dispositions | 106 / 106 |
| counted meta-generators | 0 |

Mission state: **ACTIVE**. Minimal core state: **OPEN**. Ablation:
**NOT STARTED**.

The final-disposition counts are derived from per-P-ID entries in
`COMPRESSION_LEDGER.yaml`; they are not free-standing progress estimates.
Current Lean rederivations remain evidence but are not yet final dispositions
because their separate counted promotion lifecycle has not completed.

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
- generic exact commuting-factor transport: Lean proved;
- generic approximate two-stage defect bound: Lean proved;
- heterogeneous additive finite-chain accumulation: Lean proved;
- P-API-01: full exact + approximate source-facing rederivation;
- P-ID-01: full source-facing supremum rederivation.
- P-DYN-04: full reachable-image approximate + exact source-facing
  rederivation;
- P-DYN-03: audited, but **not** fully generated — the frozen theorem includes
  the sharp multiplicative `1 - ∏(1-ε_t)` path-coupling certificate beyond the
  current additive chain calculus;
- P-STAT-09: audited, but **not** fully generated — its TV half is transport
  shaped while its Radon--Nikodym density-ratio half uses a distinct
  multiplicative order mechanism.

## Counting rule

A generator or mapping is counted only after the complete compression
lifecycle:

`SCHEMA -> LEAN -> SOURCE MATCH -> ASSUMPTION AUDIT -> FEATURE CI ->
CLEAN INTEGRATION -> PR CI -> MAIN CI -> LEDGER PR -> LEDGER MAIN CI -> COUNTED`.

Hypotheses, partial mappings and local-only builds are never counted.
