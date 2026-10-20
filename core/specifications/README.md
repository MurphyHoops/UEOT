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

## Integrity rule

A replacement canonical specification must either:

1. match the recorded hash exactly; or
2. receive a new version/hash and go through change control.

Formal proof status must then be re-audited against the new source.
