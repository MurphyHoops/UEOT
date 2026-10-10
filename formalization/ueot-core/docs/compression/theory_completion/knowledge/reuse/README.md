# FKRG proof-level reuse navigator — additive research v1

This is an ADDITIVE, read-only extension of FKRG's existing lexical source
search. It does NOT modify fkrg.py, the Core 106 Lean theorem files, the
Compression counted ledger, frozen proof semantics, or open scientific ports.

The existing FKRG cache remains useful for broad keyword/module search.
This supplement adds real proof-term direct dependencies, verified same-type
theorem peers, source copies, and a read-only scientific-role distinction.

## Run from repository root

    P=formalization/ueot-core/docs/compression/theory_completion/knowledge/reuse
    python3 "$P/fkrg_reuse.py" status
    python3 "$P/fkrg_reuse.py" search "tvDist_symm"
    python3 "$P/fkrg_reuse.py" show UEOT.V3.StatisticalDefect.tvDist_symm
    python3 "$P/fkrg_reuse.py" show UEOT.V3.Compression.TransportCertificate.processInterface_approx_via_twoStage
    python3 "$P/fkrg_reuse.py" clones --min-lines 20
    python3 "$P/fkrg_reuse.py" --json status
    python3 "$P/test_fkrg_reuse.py"
    python3 "$P/REBUILD_CLONE_CANDIDATES.py"
    python3 "$P/VERIFY_PMF_TV_BRIDGE.py"

## Strongly typed and provenance-limited evidence

- 633 source modules = 622 UEOT-maintained + 11 adapted upstream modules.
- 3,793 public source theorem proofs, with 4,886 direct registered-source
  theorem references extracted from the Lean proof term expressions.
- 37 equal-type groups / 77 names. The original audit checked 40/40
  representative-to-peer theorem type pairs via Lean Meta.isDefEq. Here
  the CLI identifies these as PINNED SNAPSHOT checks, not a fresh proof run.
- The canonical Compression ledger fixes the role of 14 independently
  reconstructed same-type cases: 8 counted M-TC/M-OI family results
  (including an intermediate support lemma), 4 uncounted retained
  P-ALI/P-CTL experimental adapters, 1 repeated TV symmetry helper,
  and 1 interface alias for an existing physical-seed no-go.
- The other 15 near-type candidate pairs were ALL rejected as closed
  definitional type equalities in the initial compilation, 0/15 PASS.
  Their inference direction or implicit assumptions may still relate.
- 68 cross-file source-code spans with at least 8 normalized nonblank
  lines (61 wholly nonvendored and 7 involving adapted upstream code);
  12 spans reach 15 lines. This is a text-copy candidate index, NOT
  a proof-equivalence decision procedure.

## New exact Lean bridge despite non-identical closed types

Two P-GOA-related files, FiniteRecurrentDecompositionStability and
SymmetricKilledSpectralStability, locally implement the same PMF
total-variation half-L1 calculation over 31 identical consecutive
nonblank proof lines. Comparing their raw closed elaborated theorem types
using Meta.isDefEq gives FALSE, reflecting the theorem contexts and
implicit type arguments.

Nevertheless, a temporary whole-module compilation of the latter after
importing the former and replacing the second PMF TV proof with a direct
exact invocation of the first PASSES with Lean. The script
VERIFY_PMF_TV_BRIDGE.py reproduces this while validating two hardcoded
historical source SHA-256 hashes BEFORE any compilation and never editing
real Core Lean files.

This is evidence of a technically viable future refactor, NOT authorization
to mutate the frozen source. Core's L3 governance and its semantic
review requirements must be satisfied separately.

## Fail-closed freshness and source authority

The navigator validates fixed, independent SHA-256 values for EVERY
source audit input file, its own 68-row clone snapshot, the immutable
canonical Compression ledger used for scientific-role classifications,
the exact set of live Lean source paths (including detecting ANY newly added
or deleted module), and all 633 source-file content hashes against the pinned
source census. It refuses to
answer if any source or metadata changed. A docs-only Git commit does
not spuriously make a valid source snapshot stale.

For a real subsequent Lean source change, regenerate source+elaboration
evidence and independently review new pinned digests. Do not silently
overwrite the old audit or treat the existing cached evidence as current.

The direct proof graph only includes registered PUBLIC source theorem
targets; a declaration with zero registered outgoing dependencies may
still reuse Mathlib, source definitions, private/local helpers or
compiler-generated theorem constants.

## Required future anti-repetition preflight

1. Search original FKRG lexical index (fkrg.py find/show).
2. Search this proof reuse navigator for prior theorem statements and
   inspect direct dependencies and same-type peers.
3. Open source and compare actual Lean hypotheses, including instances,
   universe types and domain mappings. Test exact/apply in temporary
   compilation before inventing a new proof or deleting an existing one.
4. If a repeated theorem is a counted family generator witness,
   preserve its actual abstract-to-Core derivation, rather than making
   the terminal statement an immediate alias and calling it compression.
5. Follow the canonical Compression ledger for uncounted adapters and
   counted mappings. Green type-checking never promotes scientific claims.

KNOWN LIMITATIONS: no general logical equivalence algorithm; no
identifier-renaming-invariant clone detection; some copy spans include
theorem statement headers; code matching can miss renamed or rewritten
proofs; pinned type results are not dynamically recomputed; no claim
that UEOT physical validity or generator minimality follows.
