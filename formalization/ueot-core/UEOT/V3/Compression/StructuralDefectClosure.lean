import UEOT.V3.Compression.QuotientDescent
import UEOT.V3.Compression.TransportCertificate
import UEOT.V3.Compression.OccupationLimitInvariance

/-!
# Second-order compression experiment — structural defect closure

This module does **not** change the counted four-generator Core compression
ledger.  It tests a stricter second-order hypothesis suggested only after the
106 frozen Core v3 P-IDs were formalized and the first compression mission
closed:

* exact zero structural defect should support quotient descent;
* finite nonzero defect should support transport bounds;
* asymptotically vanishing defect should close to an exact limiting relation.

The first out-of-sample target is intentionally not one of the frozen 106
source P-IDs: an approximate quotient whose fibre defect vanishes along a
convergent sequence of representations has an exact quotient in the limit.

Promotion requires more than this file compiling.  In particular, the
experiment must later show substantive wrapper reduction for the existing
M-QD/M-TC/M-OI surfaces and pass a deletion audit. -/

namespace UEOT.V3.Compression.StructuralDefectClosure

open Filter Function Topology

universe uX uY uZ

/-- Pointwise convergence plus vanishing metric defect on every representation
fibre forces the limiting quantity to be exactly fibre-compatible.

This is the basic "asymptotic defect -> exact structural relation" bridge.
Unlike M-OI, the structural relation here is quotient compatibility rather than
invariance under time evolution. -/
theorem fiberCompatible_of_asymptotic_fiber_dist
    {X : Type uX} {Y : Type uY} {Z : Type uZ} [MetricSpace Z]
    (q : X → Y)
    (gseq : ℕ → X → Z) (g : X → Z)
    (hconv : ∀ x, Tendsto (fun n => gseq n x) atTop (𝓝 (g x)))
    (hdefect :
      ∀ ⦃x x' : X⦄, q x = q x' →
        Tendsto (fun n => dist (gseq n x) (gseq n x')) atTop (𝓝 0)) :
    QuotientDescent.FiberCompatible q g := by
  intro x x' hxx'
  have hdist :
      Tendsto (fun n => dist (gseq n x) (gseq n x'))
        atTop (𝓝 (dist (g x) (g x'))) :=
    (hconv x).dist (hconv x')
  have hz : dist (g x) (g x') = 0 :=
    tendsto_nhds_unique hdist (hdefect hxx')
  exact dist_eq_zero.mp hz

/-- A uniform scalar upper envelope converging to zero is enough to discharge
the asymptotic fibre-defect premise.  This is the intended attachment point for
finite-horizon transport certificates such as M-TC weighted bounds. -/
theorem fiberCompatible_of_uniform_fiber_bound
    {X : Type uX} {Y : Type uY} {Z : Type uZ} [MetricSpace Z]
    (q : X → Y)
    (gseq : ℕ → X → Z) (g : X → Z)
    (bound : ℕ → ℝ)
    (hconv : ∀ x, Tendsto (fun n => gseq n x) atTop (𝓝 (g x)))
    (hbound0 : Tendsto bound atTop (𝓝 0))
    (hbound :
      ∀ ⦃x x' : X⦄, q x = q x' →
        ∀ n, dist (gseq n x) (gseq n x') ≤ bound n) :
    QuotientDescent.FiberCompatible q g := by
  apply fiberCompatible_of_asymptotic_fiber_dist q gseq g hconv
  intro x x' hxx'
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hbound0
    (Eventually.of_forall fun n => dist_nonneg)
    (Eventually.of_forall fun n => hbound hxx' n)

/-- **Out-of-sample second-order theorem.**

A sequence of only approximately quotient-compatible representations becomes
an exact quotient representation in the limit when:

1. every pointwise representation converges;
2. all within-fibre defects are bounded by one common envelope;
3. that envelope vanishes;
4. the representation map is surjective.

The conclusion is exact existence and uniqueness of the descended limiting
quantity.  This theorem is not one of the frozen 106 source P-IDs; it is a new
cross-layer consequence of the quotient-descent and asymptotic-defect ideas. -/
theorem existsUnique_descend_of_vanishing_fiber_bound
    {X : Type uX} {Y : Type uY} {Z : Type uZ} [MetricSpace Z]
    (q : X → Y) (hq : Surjective q)
    (gseq : ℕ → X → Z) (g : X → Z)
    (bound : ℕ → ℝ)
    (hconv : ∀ x, Tendsto (fun n => gseq n x) atTop (𝓝 (g x)))
    (hbound0 : Tendsto bound atTop (𝓝 0))
    (hbound :
      ∀ ⦃x x' : X⦄, q x = q x' →
        ∀ n, dist (gseq n x) (gseq n x') ≤ bound n) :
    ∃! gbar : Y → Z, gbar ∘ q = g := by
  exact QuotientDescent.existsUnique_descend q g hq
    (fiberCompatible_of_uniform_fiber_bound
      q gseq g bound hconv hbound0 hbound)

/-- Exact zero defect is the degenerate endpoint of the same closure logic.

This theorem is deliberately tiny: it records the exact corner that a later
second-order interface must recover without pretending that metric structure
is required by the original set-level M-QD theorem. -/
theorem fiberCompatible_of_zero_fiber_dist
    {X : Type uX} {Y : Type uY} {Z : Type uZ} [MetricSpace Z]
    (q : X → Y) (g : X → Z)
    (hzero :
      ∀ ⦃x x' : X⦄, q x = q x' → dist (g x) (g x') = 0) :
    QuotientDescent.FiberCompatible q g := by
  intro x x' hxx'
  exact dist_eq_zero.mp (hzero hxx')

end UEOT.V3.Compression.StructuralDefectClosure
