# UEOT Core — Current State

Date: 2026-09-12
Active mathematical specification: UEOT Core Mathematics v3.0
Formal package: `formalization/ueot-core/`

## Role

This file identifies the current domain-neutral Core route. It does not replace
the full mathematical specification. The authoritative source-level proof
ledger is `formalization/ueot-core/docs/V3_COVERAGE_STATUS.md`.

## Formal coverage

Current source-level Lean status:

- proved: 49
- partial: 0
- pending: 57
- total source P-IDs: 106

A P-ID is counted as proved only after source matching, official target
reachability, feature CI, clean-port CI, PR CI, merge to `main`, green post-main
CI, and ledger synchronization.

## Recently promoted

The newest completed invariant/identifiability promotions are:

- P-INV-01
- P-INV-02
- P-INV-04
- P-INV-03
- P-INV-05

P-INV-05 is the newest fully promoted item. It machine-checks predictable-design
OLS concentration from the source-time filtered stochastic assumptions through
the exact Euclidean confidence radius

`(sigma*B/kappa) * sqrt(2*d*log(2*d/alpha)/N)`.

The formal source theorem explicitly adds the standard adaptedness condition
that `xi (n+1)` is measurable with respect to `F (n+1)`. This correction is
needed for conditional-MGF iteration and is documented rather than hidden by a
final-score sub-Gaussian assumption.

Integrated main commit: `7d52e949b9788a32e3c5ce7ab9eec0f4ad85e58d`.
Post-main CI run `34626175917`: success.

## Immediate priorities

1. complete P-STAT-06 (simultaneous RKHS embedding concentration) from the
   already-integrated Hilbert moment and Azuma infrastructure;
2. source-audit and open P-INFO-02/03/04 using the canonical information stack;
3. prepare P-INT-01 after the conditional-information interface is fixed;
4. select the next remaining inverse/identifiability source P-ID only after a
   fresh dependency audit, reusing Fisher and predictable-OLS infrastructure;
5. keep every promotion source-matched and preserve the 106-item completion
   gate.

## Source synchronization

The exact UEOT Core Mathematics v3.0 source used by the formal coverage ledger
must be synchronized under `core/specifications/` byte-for-byte. Until that
migration is completed, the coverage ledger records the exact source identity
and historical hash; no regenerated substitute should be called canonical.

## Active parallel lanes

- `formal/pstat06-union-closure`: P-STAT-06 remains the main HOT probability
  lane. Integrated infrastructure includes exact `2/N` sensitivity, Hilbert
  second/first-moment bounds, conditional-sub-Gaussian Azuma control, and the
  `1/N^2 -> 1/N` parameter normalization. Remaining work is the concrete Doob
  increment bridge and exact finite-`L` source wrapper.
- P-INFO-02/03/04: WARM source-audit packet. Reuse the current information,
  entropy, KL and statistic modules; do not create a second information stack.
- P-INT-01: WARM structural bridge to follow the P-INFO audit, reusing the
  prediction/Markov-boundary/information interfaces.
- remaining inverse/identifiability packet: WARM only; P-INV-01..05 are now
  closed, so the next target must come from the still-pending frozen source
  list rather than from stale feature branches.
