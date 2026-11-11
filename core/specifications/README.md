# UEOT Core Specifications

This directory is the active source-specification layer for domain-neutral UEOT.

## Canonical v3 source identity

The current formal-verification ledger is tied to:

- file: `UEOT_Core_Mathematics_v3.0_Complete.md`
- theory version: `3.0`
- source P-IDs: `106`
- SHA-256:
  `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`

The exact content is now synchronized at
[the frozen v3.0 source](../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md).
The supplied original was checked against the previously recorded SHA-256 before
copying; the version, 106 P-IDs and hash are unchanged. The path in
`manifest.yaml` is relative to the repository root.

The separately maintained [mathematical book](../../mathematics/UEOT_MATHEMATICS.md)
preserves this source and adds subsequent results, qualifications and Lean
correspondences under its own version. Its additions do not retroactively change
the frozen v3.0 inventory or turn the new manuscript into a new coverage receipt.

## Independent successor reference supplement

The [successor specification 1.0](successor/README.md) adds 30 separately identified
contracts for mature results beyond the frozen source. Read the
[Chinese specification](successor/UEOT_Core_Successor_Specification.md) or the
[English specification](successor/UEOT_Core_Successor_Specification.en.md), then
follow the exact source and consumer obligations for the result being used.

This is an additive **exit B** supplement, not a replacement Core v4.0 or an
`active_core` promotion. The original 106 P-IDs retain their bytes, semantics and
coverage denominator. The [per-item source map](successor/V3_PROPOSITION_INTERFACE_MAP.json)
preserves every old anchor; the [claim index](successor/CLAIM_INDEX.json) binds
successor contracts to actual defining files, public imports and evidence levels.

The [architecture decision](successor/CORE_V3_TO_CURRENT_DELTA.md),
[review record](successor/REVIEW.md) and [validation record](successor/VALIDATION.md)
state the real audit and proof scope. Book adoption is a separate action described
in [the downstream adoption list](successor/DOWNSTREAM_BOOK_ADOPTION.md).

## Integrity rule

A replacement canonical specification must either:

1. match the recorded hash exactly; or
2. receive a new version/hash and go through change control.

Formal proof status must then be re-audited against the new source.
