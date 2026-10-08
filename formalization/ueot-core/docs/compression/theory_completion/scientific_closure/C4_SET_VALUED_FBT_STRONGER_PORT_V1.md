# C4 stronger-port work — directed set-valued FBT (v1)

Status: **LOCAL LEAN-CHECKED CONDITIONAL EXTENSION**; full Core §31.2 C4 port remains **OPEN**.

## The precise advance

Previously `C4FBT.lean` quantified a pair of selected parent representatives
`f0 x, f1 (tx x)`.  This did not state that *every* admissible source
completion can continue when formation is nonunique. The additive
`C4SetValuedFBT.lean` instead defines:

`DirectedFormationCoverage F0 F1 tx tp epsF` iff for every `F0 x p0`
there exists `p1` with `F1 (tx x) p1` and
`dist (tp p0) p1 ≤ epsF`.

This is a **source-fibre-wide, directed existence premise**, not the construction
of a measurable selector, a stochastic coupling or an empirical certificate.
For each source completion the theorem derives the target realization bound

`dist (B1 p1) (td (B0 p0)) ≤ L * epsF + epsB`

under `0 ≤ L`, the declared binding Lipschitz bound, and the independent
binding-transport defect.  `directed_realized_fibre_coverage` states it as
point-to-set realised inclusion without compactness/closedness assumptions.
`exact_formation_implies_directed_coverage` reuses existing exact set-valued
naturality as the zero-defect case; no extra equivalence is asserted.

`directed_two_step_realized_continuation` composes two such directed relations:
if the second realised transport is `M`-Lipschitz (`0 ≤ M`), the two-step
realization defect is bounded by `delta12 + M * delta01`.
That transport regularity is **necessary as an explicit input** to this proof;
the theorem does not infer it from the original binding assumptions.

`forward_formation_does_not_imply_reverse` supplies a finite Bool witness:
all source completions can have a matching successor even though a target
completion is newly born and has no source predecessor.

## What is *not* established

- No symmetric Hausdorff distance bound, because reverse coverage is absent.
- No general set-valued path existence in arbitrary time, no path measurability,
  no global coherent matching across time and no composition independence.
- No unrestricted split/merge/death theorem. One-to-many targets and many-to-one
  successors are compatible with the relation; a source that actually disappears
  without any matched target violates `DirectedFormationCoverage`.
- No `SameObject` identity theorem, nor an object-level lineage theorem.
- No construction/calibration of `epsF`, `epsB`, `L`, `M` from physical data.
- No change to frozen Core 106/106, its four counted generators, P0–P12 status,
  or the prior C1–C7 local evidence interpretation.

## Stronger next gates

1. **Mechanistic coverage:** derive forward matching and epsF for a declared
   response-generated formation model, or exhibit a physical counterexample.
2. **Bidirectional/lineage:** add a separate reverse witness relation when the
   application requires symmetric matching; explicitly type births and deaths
   rather than silently treating them as matches.
3. **Path-level coherence:** prove selector-free compatible paths with time
   regularity or give a no-go/counterexample to naive pairwise composition.
4. **Empirical calibration:** estimate transport defects on preregistered
   discovery/calibration splits and test the resulting held-out prediction.

The v1 target is therefore **one mathematically meaningful C4 subport**, not a
claim that all C4/split/merge/birth/death structure has been solved.
