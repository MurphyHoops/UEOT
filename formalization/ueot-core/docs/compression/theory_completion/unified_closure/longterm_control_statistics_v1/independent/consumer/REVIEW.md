# Independent consumer integration review

**Verdict: CLEAR.** This review covers the ninth-overlay changes to
`fkrg_reuse.py` and `test_fkrg_reuse.py`, the unchanged scanner algorithm,
and their binding to the actual registered proof evidence. It does not
substitute for the separate Git-object, PR or resulting-main release gates.

The authorization baseline is
`ff71e63256c88ad2bb527fdd3004d55c77894ab7`. The reviewed Lean source fingerprint
is `60cd5f8ab161c5b51394463c466947a4c6a6c1742ecdcd9c2bbfc41c0c06bd31`.
The reproducible read-only review completed **264 checks**. Its complete
input manifest and results are in `CONSUMER_REVIEW.json`; reviewed consumer
source snapshots are retained in `source-snapshots/`.

## Changes and preservation

The consumer appends exactly one entry to each of the four overlay
registries and updates its source-of-truth description. Removing those
four appended entries and restoring that description produces an AST
identical to the baseline consumer. Source, hash, environment, ownership,
historical-repair and fail-closed validation logic is unchanged.

The tests grow from **31 + 14 = 45** to **33 + 14 = 47**. All 45 historical
tests remain. Only the explicitly expected current-census numeric literals
change in three existing methods; after those substitutions and removal of
the two new methods, the entire test module's AST equals the baseline.
No historical assertion, negative fixture, skip policy or exception check
is weakened.

The two additions test actual production evidence:

- The native owner/type/edge regression binds the new overlay to its
  predecessor, 12 physical modules, 90 public candidates, all 199 native
  theorem constants (including 30 private constants), standard axiom
  closures, exact registered edges and the independently pinned native
  artifact. It also rejects ninth-layer historical-repair keys.
- The proof-route regression checks the canonical time-zero reuse in the
  exit telescope, the safe-prefix dependency of the survival tail, the
  exact registered dependencies of the all-times policy theorem, the
  population-risk identity used by SISC calibration, the scalar calibration
  dependency used by identification, the actual product witness's generic
  identification dependency, and registration of the wrong-kernel boundary.
  It checks that the SISC theorem's physical owner is UnifiedClosure despite
  its ScientificClosure logical namespace.

The review independently recomputed these relationships from the full
native constant records and the loaded registered graph. It confirmed
149 new registered edges, 373,230 cross-layer type comparisons and 4,005
internal comparisons, with no recorded raw stored-type collisions. Those
comparisons retain their documented limits; they are not a test of general
logical independence.

All **33 historical artifacts** checked against the baseline have identical
bytes: the first eight overlays and certificates, their supporting native
exports, the immutable audit inputs, the clone table, the canonical
Compression ledger and the three pinned build-environment files. The clone
table remains **68 pairs / 12 spans of at least 15 lines / maximum 31
lines**. Every scanner byte after the module docstring is unchanged.
All 666 prior package source files retain their baseline bytes except the
authorized import aggregator. The ledger remains **106 P-IDs: 11 generated, 89 adapters and 6 boundaries**,
with four counted generators.

The read-only consumer load confirms **678 = 667 + 11 modules**, nine
overlays, **4,237 public graph nodes / 5,567 edges**, **444 overlay nodes /
680 outgoing edges**, the separately retained historical old-node repair,
and **102 cumulative lexical hint groups**. The historical 37 equal-type
groups, 77 names and 15 near-type pairs remain unchanged.

## Evidence bindings and execution boundary

| Input | SHA-256 |
| --- | --- |
| `fkrg_reuse.py` | `c598f8c5aad77afbac3082dee7ceebf79471408f6646fa1567ebf09027acfc74` |
| `test_fkrg_reuse.py` | `692b427234dffff6915ed1297c5e1fb0c256577369605691be38cb68ae2797e7` |
| `REBUILD_CLONE_CANDIDATES.py` | `75650dd952415292da28df5056be8504ae7b8468349cf0ea02fb42b85e4a4b2d` |
| Registered ninth overlay | `cb5792eff95b2a1386a7c0832eeeedc5a283f212b462f2c6c6d3342dd5e1bb06` |
| Native export | `0b6b77967ad43da71cec3a569b361501f591a7a8b384d072dda31af1b897d02c` |
| Fixed native certificate | `0643f8dfca2daec2ce6b4638f712f6abcacf8f91f31669a37120f397d6c27213` |

The separate source/raw-execution review is CLEAR on the same fingerprint.
The existing UMC full receipt and raw-log digest were read and checked:
79 research modules, 1,073 compiler-owned theorem constants with standard
axioms only, 106 located P-IDs, full Lean PASS and no frozen-source impact.
This consumer review did not rerun Lean, the Python gate suites or the full
clone scanner, and did not use Mac tools. Their actual execution receipts
remain separate evidence.

The initial local review harness counted only the first test class and
stopped at its count assertion. The corrected harness counts both test
classes and completed all 264 checks; no production consumer or test source
was changed to obtain that result.

The two knowledge READMEs now record the actual augmented overlay hash and
SOURCE / EXECUTION CLEAR. They identify exact Git-object preflight, PR and
resulting-main acceptance as separate release gates indexed by Issue #146
and the corresponding PR check runs. Historical raw `PENDING` receipts were
not rewritten, and no publication completion is inferred from this review.
