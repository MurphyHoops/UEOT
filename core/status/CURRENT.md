# UEOT Core — Current State

Date: 2026-09-11
Active mathematical specification: UEOT Core Mathematics v3.0
Formal package: `formalization/ueot-core/`

## Role

This file identifies the current domain-neutral Core route. It does not replace
the full mathematical specification. The authoritative source-level proof
ledger is `formalization/ueot-core/docs/V3_COVERAGE_STATUS.md`.

## Formal coverage

Current source-level Lean status:

- proved: 47
- partial: 0
- pending: 59
- total source P-IDs: 106

A P-ID is counted as proved only after source matching, official target
reachability, feature CI, clean-port/PR integration, merge to `main`, green
post-main CI, and ledger synchronization.

## Recently promoted

The newest completed invariant/identifiability promotions are:

- P-INV-01
- P-INV-02
- P-INV-04

P-INV-04 is the newest fully promoted item: noiseless fixed-design unique
identifiability over `R^d` iff the Gram quadratic form is strictly positive on
every nonzero direction. Its post-main CI is green and it is recorded in the
authoritative 47/106 ledger.

## Immediate priorities

1. complete P-INV-03 (multi-intervention Fisher accumulation and kernel
   intersection) from the already-green Fisher additivity foundation;
2. complete P-STAT-06 (simultaneous RKHS embedding concentration) from the
   already-green Hilbert first-moment and Azuma parameter layers;
3. advance P-INV-05 (predictable-design OLS concentration) on an independent
   branch from the newest green `main` checkpoint;
4. keep every promotion source-matched and preserve the 106-item completion
   gate.

## Source synchronization

The exact UEOT Core Mathematics v3.0 source used by the formal coverage ledger
must be synchronized under `core/specifications/` byte-for-byte. Until that
migration is completed, the coverage ledger records the exact source identity
and historical hash; no regenerated substitute should be called canonical.

## Active parallel lanes

- `formal/pinv03-fisher-intersection`: centered-independent score cross terms,
  Fisher-entry accumulation, and Fisher-operator additivity are green. The
  remaining mathematical bridge is to instantiate the PSD/kernel theorem for
  the actual Fisher quadratic form and expose the source-facing `p_inv_03`.
- `formal/pstat06-mmd-concentration`: exact `2/N` sensitivity, Hilbert
  second/first-moment bounds, the pinned-Mathlib Azuma wrapper, and the
  `1/N^2 -> 1/N` parameter normalization are green. The remaining work is the
  bounded-difference/Doob bridge and final finite-union source wrapper.
- `formal/pinv05-predictable-ols`: independent lane created from current
  `main`; target assumptions are predictable bounded design, conditionally
  sub-Gaussian noise, and a Gram lower bound.
