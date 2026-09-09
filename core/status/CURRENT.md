# UEOT Core — Current State

Date: 2026-09-09
Active mathematical specification: UEOT Core Mathematics v3.0
Formal package: `formalization/ueot-core/`

## Role

This file identifies the current domain-neutral Core route. It does not replace
the full mathematical specification.

## Formal coverage

Current source-level Lean status:

- proved: 12
- partial: 6
- pending: 88
- total source P-IDs: 106

Authoritative detailed ledger:

- `formalization/ueot-core/docs/V3_COVERAGE_STATUS.md`

Recently promoted:

- P-RES-05
- P-RES-06
- P-CAR-04

P-RES-02 is currently being formalized and must not be promoted until both its
closure-operator composition and minimal-family resolution composition are
source-matched and machine-checked.

## Immediate priorities

1. complete P-RES-02;
2. complete P-RES-01 using the same closure-system layer;
3. restore the remaining previously verified Lean modules from the historical
   package;
4. return to the six partial probability/dynamics/teleology/bridge items;
5. keep the 106-item completion gate intact.

## Source synchronization

The exact UEOT Core Mathematics v3.0 source used by the formal coverage ledger
must be synchronized under `core/specifications/` byte-for-byte. Until that
migration is completed, the coverage ledger records the exact source identity
and historical hash; no regenerated substitute should be called canonical.
