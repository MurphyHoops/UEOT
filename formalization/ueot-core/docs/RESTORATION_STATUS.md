# UEOT Core Lean Restoration Status

Date: 2026-09-09
Branch: `main`
Package: `formalization/ueot-core/`

## Purpose

The historical v3.0 Lean package was previously verified outside the currently
reachable GitHub object history. Its reported source commit
`fa0106e67d4c4b09fe3cc193019c8eec8c6e05d3` is not retrievable from the
current repository object database.

Therefore restoration follows:

```text
preserved AI reference
        ↓
module reconstruction
        ↓
official UEOT / UEOT.V3 import
        ↓
pinned Lean + locked Mathlib CI
        ↓
current-repository restored status
```

A historical theorem is not called restored until this current CI sequence
passes.

## Source-level coverage

Restoration and source coverage are separate ledgers.

Current v3 source coverage remains:

- proved: 16
- partial: 4
- pending: 86
- total P-IDs: 106

The four partial P-IDs are:

- P-DYN-01
- P-TEL-01
- P-BRG-02
- P-REF-05

## Restored and reverified modules

| Module | Commit | Current CI evidence | Role |
|---|---|---|---|
| `UEOT/Core/Finite.lean` | `67b24f21a52eb5e8ac3c228f44d26aec7c24df32` | run `34339712702` success | finite inclusion-minimality |
| `UEOT/Core/Blocker.lean` | `a6578a572e6761703e809404905da96a3330389f` | run `34339830471` success | finite blocker duality |
| `UEOT/Core/Prediction.lean` | `558560e29532ebc2694a6ba73e60dd6b1f6ca64f` | run `34340396556` success | pointwise predictive factorization |
| `UEOT/Core/Access.lean` | `c81d8bec2b1a2529a0fe50ce2fab90049e2af80f` | run `34340485938` success | finite carriers and erasure |
| `UEOT/V3/Access.lean` | `d1906d1d83e4a83d2a7f52726d5ff183f355528c` | run `34340605242` success | measurable/common-filter carrier layer |
| `UEOT/V3/BlockerNaturality.lean` | `7e74279abe8905dc2cbfbcdec0f5fc8c6a6d4b8c` | run `34340847141` success | P-RES-03 naturality |
| `UEOT/V3/Threshold.lean` | `301afd920a16903e0d4709e5f07aa987870f202c` | run `34340916442` success | P-STAT-03/04 threshold stability |
| `UEOT/Core/Reward.lean` | `514e94af15bdab92914be5a7eb4c708fef878a96` | run `34340982238` success | finite-horizon P-TEL-01 foundation |
| `UEOT/V3/Decision.lean` | `bd613421e007871783dda5e59952ab170f0df43d` | run `34341053281` success | decision/regret foundations |
| `UEOT/V3/PredictionAE.lean` historical layer | `1dc73aef55c1bd6dc7ca851beced2c6157c7148f` | run `34341243352` success | measurable kernels/common null set |
| `UEOT/Core/Dynamics.lean` | `68d6154563cf864f61839219195c321664aba5ae` | run `34341358837` success | deterministic P-DYN-01 specialization |

### Reconstruction note

The historical `BlockerNaturality.image_hits` body was not fully visible in
the preserved single-file excerpt. It was re-derived from the surrounding
definitions and downstream theorem types. The resulting complete module passed
the pinned current CI; it is therefore a current proof, but is not described as
a byte-for-byte historical restoration.

## New formalization beyond the historical package

These changes are not mere restoration:

- P-CAR-04 metric decoder-radius theorem and official-target repair;
- P-RES-01 coarse minimality;
- P-RES-02 closure/minimal-family composition;
- P-RES-05 exact finite-clutter / push-minimal bridge;
- P-RES-06 active-fiber uniqueness;
- P-PRED-01 AE factor preorder work now in progress.

## P-PRED-01 in-flight

Exact source target:

`P-PRED-01 — common-protocol canonical minimality`.

Current newly introduced structures include:

- `AEFactors` — measurable decoder factorization modulo one reference measure;
- `canonical_ae_minimal`;
- `coordinate_ae_sufficient`;
- `AESigmaLE` — explicit sigma-factor inclusion after choosing an AE version;
- `aeFactors_sigmaLE`;
- `canonical_ae_sigma_minimal`.

These do **not** yet justify promoting P-PRED-01. The remaining source-level
obligation includes the conditional-future-law statement and final semantic
audit of the minimal mod-null sigma factor.

## Non-negotiable restoration rules

- no `sorry`, `sorryAx`, `native_decide`, or UEOT-specific axioms;
- restored modules enter an official build target;
- historical success is not substituted for current CI;
- restoring a theorem already counted as proved does not increase P-ID coverage;
- failed intermediate commits/runs remain in history;
- natural-language source strength is not weakened to make restoration easier.


## P-PRED-01 closure

P-PRED-01 is now source-matched as `proved`.

New current-repository evidence:

- `UEOT/V3/PredictionAE.lean` — AE factor preorder, mod-null sigma order,
  canonical coordinate kernels, event-level conditional expectation;
- `UEOT/V3/PredictionDependent.lean` — protocol-dependent future spaces;
- final dependent-space commit `d6ac587403ad0dd900c8752ba46fa7e2c65a8fec`;
- successful run `34343117149`.

This promotion changes source coverage; unlike restoration-only work it reduces
the partial count.


## P-PRED-02 closure

P-PRED-02 is now source-matched as `proved`.

- final dependent-protocol commit:
  `da33abaf7c079472a1d95c15d1b91c3b2b35361c`
- successful current CI run:
  `34344159704`

The formal sigma-union result does not need the source's monotonicity
assumption, so the source statement follows as a direct specialization.
