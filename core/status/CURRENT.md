# UEOT Core — Current State

Date: 2026-09-10
Active mathematical specification: UEOT Core Mathematics v3.0
Formal package: `formalization/ueot-core/`

## Role

This file identifies the current domain-neutral Core route. It does not replace
the full mathematical specification or the source-level Lean coverage ledger.

## Canonical source and proof status

The canonical mathematical baseline remains UEOT Core Mathematics v3.0 with
106 stable P-IDs. The exact source identity is pinned by
`core/specifications/manifest.yaml`.

Do **not** duplicate source-level proved/partial/pending counts in this file.
Those numbers change as proof branches merge and previously became stale here.
The authoritative detailed proof status is always:

- `formalization/ueot-core/docs/V3_COVERAGE_STATUS.md`

The complete gate remains 106/106 source-matched P-IDs, successful pinned build,
replay/axiom audit, and no proof holes.

## Bidirectional maintenance

Core maintenance is now explicitly bidirectional. Lean formalization must follow
the exact v3 statement, but failed proofs, counterexamples, hidden hypotheses,
and stronger machine-checked results feed back into a versioned Core audit.
Historical Mathematical Foundations and unified versions remain derivation
archives from which valid domain-neutral theorems and no-go results may be
recovered.

Maintenance contract:

- `core/status/EVOLUTION_MAINTENANCE.md`

No semantic change to the canonical v3 source is made silently. A real source
correction is recorded as an erratum candidate or released in a new version
with provenance and a new immutable source hash.

## Core invariants

The active Core keeps the following dependency direction:

`world/process -> candidate representation -> predictive/causal identity ->`
`persistence/realization/integrity -> admissible futures -> value/control ->`
`GOD/GOA -> evolution/learning`.

In particular:

- Omega is an identity-supporting certificate family, not a mandatory literal
  geometric loop;
- predictive sufficiency alone is not objecthood;
- a canonical predictive state does not imply a unique physical boundary;
- control/value/GOD/GOA are downstream of a sufficiently closed object model;
- parent composition requires irreducibility rather than correlation alone;
- domain-specific axioms must not leak into the generic Core.

## Active parallel formalization lanes

The current proof campaign is organized around independent source-facing lanes,
with integration serialized only after semantic review:

- P-DYN-02 — finite CTMC generator/semigroup/block-sum criterion and valid macro
  generator;
- P-INFO-01..04 — deterministic-statistic information chain and discrete
  entropy/retention consequences;
- P-FAC-01 — primitive representation covariance -> finite causal path-law
  covariance -> value invariance;
- P-PER-01 — omega-limit persistence and exact invariance under the precise v3
  time assumptions;
- P-REC-02 — Dynkin/AC/a.e. drift -> exponential recovery -> mean-square bound;
- P-PER-03 — finite viability deletion kernel -> stationary policy ->
  probability-one all-time persistence.

Each lane may add helper lemmas without changing the v3 claim. Promotion to
`proved` occurs only after exact source-semantic matching and the full
verification gate.

## Source synchronization

`core/specifications/manifest.yaml` currently records that byte-for-byte
synchronization of the exact v3 source into the new `core/specifications/`
layout is still pending. Until that migration is completed, the formalization
coverage ledger and pinned historical hash remain the source-identity authority;
a regenerated substitute must not be called canonical.
