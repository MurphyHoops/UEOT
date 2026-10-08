# SISC N5-A — process-level lineage non-identifiability after whole-repository reuse audit

2026-10-09. Additive local UEOT research branch; not a new governed Core theorem.

## Actual repository modules inspected

- `Compression/TheoryCompletion/LineageEvolution.lean` (P8) already gives **two distinct typed relations**: `LineageSemantics.SameObject` from an identity map and `LineageSemantics.OffspringOf` from `parentOf` plus a *different* identity; `CompatibleTransmission` and `ReproductiveTransmission` connect positive population transition mass to **supplied genealogical evidence**. We **reuse** those exact definitions, do not redefine reproduction.
- `Compression/TheoryCompletion/AutopoiesisClosure.lean` (P12) already gives conditional lifecycle-formation/discovery/repair/lineage bridges, and its no-go for physical-only reconstruction of multiple repair program sources. The parent mapping and repair source remain explicit inputs.
- `Compression/CrossTrack/ParentSemanticNoGo.lean` (X1) proves a child projection can lose parent semantics despite unique isolated invariant laws for each completion.
- `Compression/CrossTrack/RobustParentSemanticCertificate.lean` (X5) gives conditional quantitative within-fibre stationary semantic diameter, not an inverse proof of unique parent identity.
- `Compression/CrossTrack/ParentBindingDiagnosticNoGo.lean` shows forward Lipschitz-stable composition diagnostic can still fail to identify a parent.
- `Compression/TheoryCompletion/InverseObjecthood/NonIdentifiabilityBoundaries.lean` already proves indistinguishable valid candidate evidence obstructs literal candidate recovery.
- `SISCIdentityNoGo.lean` already proves generic equality of responses does not imply object token identity and causal edges may split or merge.
- `Compression/Objecthood/StationaryCausalPathLawBridge.lean` proves path-law agreement for a registered stationary causal embedding; it does not invert passive path observations into genealogy.

The gap for N5 is therefore **not** a fresh philosophical non-identifiability claim, but an exact example **fixing the entire fully observed microprocess** while genealogical interpretation still varies.

## Formalized counterexample

`SISCCausalLineageNoGo.lean` reuses the previously proved normalized two-state deterministic flip kernel `flipObservationKernel`, chooses an **injective, full microstate readout**, and supplies two explicit P8 `LineageSemantics Bool Bool` interpretations that **share the exact same kernel and readout**:

- first `parentOf p c := p ≠ c` interprets false→true as a reproductive parent edge (their identity tags differ);
- second `parentOf _ _ := False` interprets the **same** positive-probability transition as non-reproductive process change.

Lean proves `K(false,(),true)=1`, injectivity of the full readout, positive genealogical edge in the first interpretation, absent edge in the second, and that no single recovered edge predicate can match both. This strengthens the earlier *collapsed-observation* no-go: **even perfect observability of the microstate process is not sufficient to derive a semantic ancestry predicate from K alone**.

The statement does **not** claim physical ancestry is arbitrary: the two interpretations differ in missing external reproduction/provenance mechanism evidence. The correct scientific conclusion is that a plain state transition is not automatically reproduction.

## Next typed positive bridge

Retain the actual kernel K and let the operational N3 resolver scan registered next-state candidates with `K(source,action,c)>0`, rather than a selected `tp` or an arbitrary candidate-specific causal oracle. This **proves process reachability**, not parentage. Only when the genuine P8 `CompatibleTransmission` or `ReproductiveTransmission` contract has been independently certified may a positive transition be lifted to P8's `parentOf` or `OffspringOf` predicate.

The stronger ontic P12 lifecycle would still need independent observed parent/repair/identity maps; a transition-support bridge cannot supply those by itself.

Governance: local-only, scientific-final HOLD, independent experiment not established, no cloud activity.
