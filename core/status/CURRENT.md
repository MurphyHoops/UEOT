# UEOT Core — Current State

Date: 2026-10-20

Frozen mathematical specification: UEOT Core Mathematics v3.0

Formal package: [formalization/ueot-core/](../../formalization/ueot-core/)

## Role and current reading route

This file identifies the current domain-neutral Core state. The maintained
[mathematical book](../../mathematics/README.md) develops definitions, proofs,
counterexamples and open problems. The independently maintained
[philosophical book](../../philosophy/README.md) develops the philosophical
arguments and interpretations. They inform each other through explicit
references; the mathematical specification, Lean proofs and philosophical
arguments retain their own standards of justification.

The [source specification manifest](../specifications/manifest.yaml) records
the frozen v3.0 identity. The authoritative source-level proof ledger is
[V3_COVERAGE_STATUS.md](../../formalization/ueot-core/docs/V3_COVERAGE_STATUS.md).

## Formal coverage of the frozen specification

| Source P-ID status | Count |
|---|---:|
| Proved / FULL-GREEN | 106 |
| Partial | 0 |
| Pending | 0 |
| Total unique source P-IDs | 106 |

These counts record completion of the 106 frozen source proof contracts under
their stated assumptions. Source matching, official build reachability,
prohibited-axiom checks and the promotion history are recorded in the coverage
ledger. The official package target is `lake build UEOT`.

The count does not establish an unconditional unified theory or empirical
confirmation of its interpretations. A source P-ID, a Lean declaration, a
compiler-generated constant and a book proposition are different units. New
proofs and book chapters do not silently change the frozen 106-item registry.

## Compression and retained assumptions

The [compression ledger](../../formalization/ueot-core/docs/compression/COMPRESSION_LEDGER.yaml)
classifies all 106 source P-IDs:

| Final disposition | Count |
|---|---:|
| Generated through registered rederivation routes | 11 |
| Retained adapters | 89 |
| Retained boundaries | 6 |
| Unresolved dispositions | 0 |

Four generators are counted in the declared derivation system: quotient
descent, finite quantitative transport, occupation-limit invariance and
positive eigenstructure. The 11 generated items have registered Lean
rederivations. The 89 adapters and 6 boundaries retain their stated roles and
assumptions; the ledger does not claim that four generators rederive all 106
contracts. Its minimality claim is nonredundancy within that declared
derivation system.

## Exact source synchronization

The frozen source is now installed at
[mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md](../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md).
It contains 183440 bytes and has SHA-256:

`ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`

These are the exact bytes identified by the coverage ledger and the current
manifest. The manifest records `content_sync: synced`. The ledger's earlier
source-synchronization note remains a historical checkpoint; the artifact
installation resolves that separate task without changing any proof contract.

The maintained mathematical book can develop beyond v3.0 while citing this
immutable source. Revised prose must receive its own version and provenance.
The original philosophical paper and its source history are retained under
[philosophy/source/](../../philosophy/source/), with historical root artifacts
preserved at their existing addresses.

## Current development focus

1. Strengthen the mathematical connections between source contracts,
   compression, objecthood, control, identity and statistical deployment;
   state the assumptions consumed at each connection.
2. Use explicit models and counterexamples to distinguish sufficient
   conditions, existence claims, executable constructions and empirical
   interpretations. In particular, certified deployment occupancy and
   physical failure are separate quantities.
3. Maintain the two books as independent works: use mathematical findings to
   refine philosophical arguments, and use philosophical questions to expose
   missing definitions or mathematical obligations.
4. Validate implementation changes locally against the pinned package and
   existing evidence before publishing the necessary commits and PRs.

The previous 49/57 checkpoint and its active-lane list are superseded. Current
work proceeds from the completed frozen coverage record rather than reopening
those items as pending.
