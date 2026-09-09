# UEOT Core — Current State

Date: 2026-09-09
Active mathematical specification: UEOT Core Mathematics v3.0
Formal package: `formalization/ueot-core/`

## Role

This file identifies the current domain-neutral Core route. It does not replace
the full mathematical specification.

## Formal coverage

Current source-level Lean status:

- proved: 19
- partial: 1
- pending: 86
- total source P-IDs: 106

Authoritative detailed ledger:

- `formalization/ueot-core/docs/V3_COVERAGE_STATUS.md`

Recently promoted:

- P-REF-05
- P-TEL-01
- P-BRG-02
- P-PRED-02
- P-PRED-01

- P-RES-05
- P-RES-06
- P-CAR-04
- P-RES-02
- P-RES-01

P-RES-01 and P-RES-02 are now source-matched and machine-checked on the shared closure-system layer. Together with the previously proved P-RES-03..06, the complete P-RES-01..06 resolution block is now proved.

## Immediate priorities

1. restore the remaining previously verified Lean modules from the historical
   package;
4. return to the six partial probability/dynamics/teleology/bridge items;
5. keep the 106-item completion gate intact.

## Source synchronization

The exact UEOT Core Mathematics v3.0 source used by the formal coverage ledger
must be synchronized under `core/specifications/` byte-for-byte. Until that
migration is completed, the coverage ledger records the exact source identity
and historical hash; no regenerated substitute should be called canonical.


## Active parallel lanes

- P-DYN-01: general Markov strong lumpability + finite-step kernel consistency
  is currently in CI; full conditional-history equivalence is still required.
