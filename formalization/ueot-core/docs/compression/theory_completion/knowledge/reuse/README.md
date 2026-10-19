# FKRG proof-level reuse navigator — additive research v1

This is an ADDITIVE, read-only extension of FKRG's existing lexical source
search. It does NOT modify fkrg.py, the Core 106 Lean theorem files, the
Compression counted ledger, frozen proof semantics, or open scientific ports.

The existing FKRG cache remains useful for broad keyword/module search.
This supplement adds real proof-term direct dependencies, verified same-type
theorem peers, source copies, and a read-only scientific-role distinction.

## Governed overlay chain (2026-10-11 to 2026-10-19)

The 2026-10-10 633-module audit remains immutable history.

### Layer 1 — relation/defect MINCORE

`MINCORE_REUSE_OVERLAY_V1.json` is the first immutable additive layer, pinned
to source checkpoint `fb70de6fb5dd26918222bc7b0849fb38900f8604`.
It records the 634th Lean module, the then-current import-only
`TheoryCompletion.lean` source-hash update, and 10 public theorem nodes. Its
certificate `VERIFY_MINCORE_OVERLAY_TYPES.lean` performs 37,930
cross-snapshot `Meta.isDefEq` checks plus 45 internal pair checks and finds
0 definitionally-equal matches. Its compiled proof terms contain 0 registered
base/overlay theorem edges.

That historical result remains unchanged. In particular, source text for
`rescale_changes_nonzero_defect` mentions `rescale_defect` in a tactic, but
the theorem constant is absent from the elaborated proof term; FKRG records
kernel proof dependencies, not tactic-token references.

### Layer 2 — calibrated defect comparison

`CALIBRATED_DEFECT_REUSE_OVERLAY_V1.json` composes on top of the 634-module
state instead of rewriting Layer 1. It is pinned to source checkpoint
`fb16512a6b4e813ef94f2ba3db0e6f3a44500886` and adds the 635th module,
`CalibratedDefectComparison.lean`, plus 8 public theorem nodes.

`VERIFY_CALIBRATED_DEFECT_OVERLAY_TYPES.lean` kernel-checks those 8 theorem
types against all 3,803 previously registered theorem nodes:
30,424 cross-layer `Meta.isDefEq` comparisons plus 28 internal comparisons,
with 0 matches. The same verifier checks exact compiled proof dependencies and
certifies exactly 3 registered theorem edges:

- `DefectCalibration.rel_iff` → `DefectCalibration.zero_defect_iff`;
- `DefectCalibration.tendsto_zero_iff` → `DefectCalibration.reverse_budget`;
- `calibrated_weighted_chain_bound` →
  `TransportCertificate.weighted_chain_bound`.

The last edge is the intended theorem reuse: the calibrated bridge transports
an already-proved M-TC finite-horizon certificate rather than reproving the
weighted recurrence.

### Layer 3 — defect gauge covariance

`DEFECT_GAUGE_REUSE_OVERLAY_V1.json` composes on the intact 635-module state,
pinned to source checkpoint `3fb6c422638a6c8dbb2ea31cf9affd4e2f17b668`.
It adds `DefectGaugeCovariance.lean` and 6 public theorem nodes.

`VERIFY_DEFECT_GAUGE_OVERLAY_TYPES.lean` compares those 6 types with all
3,811 prior registered theorem nodes: 22,866 cross-layer `Meta.isDefEq`
comparisons plus 15 internal comparisons, with 0 matches. The same native
certificate checks exactly 6 registered direct proof edges:

- `DefectCalibration.triangle_quasi` and
  `calibrated_cross_stage_contraction` each use
  `DefectCalibration.reverse_budget`;
- `rescaled_weighted_chain_bound` uses
  `TransportCertificate.weighted_chain_bound` and the three new scalar-gauge
  helpers `rescale_triangle_preserved`, `rescale_contraction_transformed`, and
  `rescale_local_budget_transformed`;
- the three scalar-gauge helpers have no registered direct theorem edges.

The immutable-base PR preflight finds six new theorem names, with prior
lexical reuse candidates for one of them: `rescaled_weighted_chain_bound`.
Its three hints are the registered weighted-chain bound, the earlier calibrated
bound, and `TransportCertificate.chain_bound`. These remain name-similarity
hints; the compiled dependency certificate above establishes the actual reuse.
The PR parser's lexical corpus counts (3,812 to 3,818) and the registered
proof graph counts (3,811 to 3,817) are distinct scopes.

The resulting live census is **636 modules = 625 UEOT-maintained + 11 adapted
upstream**, with **3,817** public authored theorem proof nodes in the direct
proof graph. All three overlay JSON files and Lean certificates are pinned by
independent SHA-256 values. The exact live source path set and cumulative
source-hash overrides are checked fail-closed. Any further Lean source
addition/removal or source-byte drift requires another governed overlay or
snapshot and may not be silently absorbed.

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

Run the new native certificate from `formalization/ueot-core` after building
the public imports with the pinned toolchain:

    lake env lean docs/compression/theory_completion/knowledge/reuse/VERIFY_DEFECT_GAUGE_OVERLAY_TYPES.lean

## Strongly typed and provenance-limited evidence

- 633 immutable-base source modules = 622 UEOT-maintained + 11 adapted upstream modules;
  the three governed overlays extend the live census to 636 = 625 + 11.
- 3,793 immutable-base public source theorem proofs + 24 governed overlay theorem
  proofs = 3,817 live graph nodes, with 4,895 direct registered-source theorem
  references after the calibrated and gauge overlays add 3 and 6 certified edges.
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
  a proof-equivalence decision procedure. Recomputing over all 636 modules
  preserves all 68 historical rows exactly; no clone snapshot is overwritten.

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
the pinned Lean compiler/dependency environment (lean-toolchain,
lakefile.lean and lake-manifest.json including the pinned Mathlib revision),
the exact set of live Lean source paths (including detecting ANY newly added
or deleted module), and all immutable-base source hashes plus the governed
overlay-chain hashes against the exact 636-module live source census. It refuses to
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
