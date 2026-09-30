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
open scoped BigOperators

universe uX uY uZ

/-- A nonnegative scalar defect that is uniformly bounded by an envelope
converging to zero is itself exactly zero.

This is the smallest reusable asymptotic-closure primitive in the
second-order structural-defect layer.  Domain adapters are expected to supply
their own nonnegativity theorem and the certified envelope; the closure step is
owned here rather than reimplemented downstream. -/
theorem nonnegative_defect_eq_zero_of_uniform_bound
    (defect : ℝ) (bound : ℕ → ℝ)
    (hdefect : 0 ≤ defect)
    (hbound0 : Tendsto bound atTop (𝓝 0))
    (hbound : ∀ n, defect ≤ bound n) :
    defect = 0 := by
  have hzero : Tendsto (fun _ : ℕ => defect) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hbound0
      (Eventually.of_forall fun _ => hdefect)
      (Eventually.of_forall hbound)
  exact tendsto_nhds_unique tendsto_const_nhds hzero

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
quantity.  This theorem is not one of the frozen 106 source P-IDs, but by
itself it is only an out-of-sample **metric corollary of M-QD** plus elementary
limit closure.  Essential cross-generator evidence begins only in the weighted
transport theorems below. -/
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

/-- M-TC attachment: a weighted finite-stage transport certificate whose exact
derived envelope tends to zero forces the within-fibre defect itself to vanish.

The theorem intentionally keeps the asymptotic envelope hypothesis explicit.
M-TC controls finite propagation; it does not by itself imply asymptotic
decay. -/
theorem fiber_dist_tendsto_zero_of_weighted_transport
    {X : Type uX} {Y : Type uY} {Z : Type uZ} [MetricSpace Z]
    (q : X → Y)
    (gseq : ℕ → X → Z)
    (step : ℕ → Z → Z)
    (L ε : ℕ → ℝ)
    (hcontract :
      ∀ ⦃x x' : X⦄, q x = q x' →
        ∀ n,
          dist (gseq (n + 1) x) (step n (gseq n x')) ≤
            L n * dist (gseq n x) (gseq n x'))
    (hlocal :
      ∀ x n,
        dist (step n (gseq n x)) (gseq (n + 1) x) ≤ ε n)
    (hL0 : ∀ n, 0 ≤ L n)
    (hvanish :
      ∀ ⦃x x' : X⦄, q x = q x' →
        Tendsto
          (fun n =>
            (∏ j ∈ Finset.range n, L j) *
                dist (gseq 0 x) (gseq 0 x') +
              ∑ k ∈ Finset.range n,
                ε k * ∏ j ∈ Finset.Ico (k + 1) n, L j)
          atTop (𝓝 0)) :
    ∀ ⦃x x' : X⦄, q x = q x' →
      Tendsto (fun n => dist (gseq n x) (gseq n x')) atTop (𝓝 0) := by
  intro x x' hxx'
  have hupper :
      ∀ n,
        dist (gseq n x) (gseq n x') ≤
          (∏ j ∈ Finset.range n, L j) *
              dist (gseq 0 x) (gseq 0 x') +
            ∑ k ∈ Finset.range n,
              ε k * ∏ j ∈ Finset.Ico (k + 1) n, L j := by
    intro n
    exact TransportCertificate.weighted_chain_bound
      (A := fun _ => Z)
      (defect := fun _ => dist)
      (ideal := fun t => gseq t x)
      (actual := fun t => gseq t x')
      (step := step)
      (L := L)
      (ε := ε)
      (fun t => hcontract hxx' t)
      (fun t => dist_triangle _ _ _)
      (fun t => hlocal x' t)
      hL0
      n
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds
    (hvanish hxx')
    (Eventually.of_forall fun n => dist_nonneg)
    (Eventually.of_forall fun n => hupper n)

/-- First three-layer composition theorem.

A genuine M-TC weighted transport certificate controls every fibre pair; if
the derived certificate envelope vanishes and the represented quantities
converge pointwise, the limit satisfies exact M-QD quotient descent.

This is stronger evidence of cross-generator composition than the bare uniform
bound theorem above, but it is still a bridge theorem: it does not show that
M-QD, M-TC, or M-OI is redundant. -/
theorem existsUnique_descend_of_weighted_transport_limit
    {X : Type uX} {Y : Type uY} {Z : Type uZ} [MetricSpace Z]
    (q : X → Y) (hq : Surjective q)
    (gseq : ℕ → X → Z) (g : X → Z)
    (step : ℕ → Z → Z)
    (L ε : ℕ → ℝ)
    (hconv : ∀ x, Tendsto (fun n => gseq n x) atTop (𝓝 (g x)))
    (hcontract :
      ∀ ⦃x x' : X⦄, q x = q x' →
        ∀ n,
          dist (gseq (n + 1) x) (step n (gseq n x')) ≤
            L n * dist (gseq n x) (gseq n x'))
    (hlocal :
      ∀ x n,
        dist (step n (gseq n x)) (gseq (n + 1) x) ≤ ε n)
    (hL0 : ∀ n, 0 ≤ L n)
    (hvanish :
      ∀ ⦃x x' : X⦄, q x = q x' →
        Tendsto
          (fun n =>
            (∏ j ∈ Finset.range n, L j) *
                dist (gseq 0 x) (gseq 0 x') +
              ∑ k ∈ Finset.range n,
                ε k * ∏ j ∈ Finset.Ico (k + 1) n, L j)
          atTop (𝓝 0)) :
    ∃! gbar : Y → Z, gbar ∘ q = g := by
  exact QuotientDescent.existsUnique_descend q g hq
    (fiberCompatible_of_asymptotic_fiber_dist q gseq g hconv
      (fiber_dist_tendsto_zero_of_weighted_transport
        q gseq step L ε hcontract hlocal hL0 hvanish))

/-- Essential M-TC -> M-OI composition.

For each time label and observable, a weighted M-TC certificate controls the
defect between the evolved observable and the base observable.  If the exact
derived certificate envelope vanishes, M-OI's continuous-observable theorem
turns that asymptotic defect into invariance of the limiting state.

This theorem is deliberately real-valued at the observable layer because both
counted M-OI source families use real separating observables.  It does not claim
that M-TC alone implies decay: the asymptotic envelope hypothesis remains
explicit. -/
theorem invariant_of_weighted_observable_transport
    {State : Type*} [TopologicalSpace State]
    {Time : Type*} {Obs : Type*}
    (observe : Obs → State → ℝ)
    (advance : Time → State → State)
    (seq : ℕ → State) (limit : State)
    (hseq : Tendsto seq atTop (𝓝 limit))
    (hObserve : ∀ o, Continuous (observe o))
    (hAdvanceObserve : ∀ t o, Continuous (fun x => observe o (advance t x)))
    (hseparates :
      ∀ x y : State, (∀ o, observe o x = observe o y) → x = y)
    (step : Time → Obs → ℕ → ℝ → ℝ)
    (L ε : Time → Obs → ℕ → ℝ)
    (hcontract :
      ∀ t o n,
        dist
            (observe o (advance t (seq (n + 1))))
            (step t o n (observe o (seq n))) ≤
          L t o n *
            dist
              (observe o (advance t (seq n)))
              (observe o (seq n)))
    (hlocal :
      ∀ t o n,
        dist
            (step t o n (observe o (seq n)))
            (observe o (seq (n + 1))) ≤
          ε t o n)
    (hL0 : ∀ t o n, 0 ≤ L t o n)
    (hvanish :
      ∀ t o,
        Tendsto
          (fun n =>
            (∏ j ∈ Finset.range n, L t o j) *
                dist
                  (observe o (advance t (seq 0)))
                  (observe o (seq 0)) +
              ∑ k ∈ Finset.range n,
                ε t o k *
                  ∏ j ∈ Finset.Ico (k + 1) n, L t o j)
          atTop (𝓝 0)) :
    ∀ t, advance t limit = limit := by
  apply OccupationLimitInvariance.invariant_of_continuous_observable_residual
    observe advance seq limit hseq hObserve hAdvanceObserve hseparates
  intro t o
  have hupper :
      ∀ n,
        dist
            (observe o (advance t (seq n)))
            (observe o (seq n)) ≤
          (∏ j ∈ Finset.range n, L t o j) *
              dist
                (observe o (advance t (seq 0)))
                (observe o (seq 0)) +
            ∑ k ∈ Finset.range n,
              ε t o k *
                ∏ j ∈ Finset.Ico (k + 1) n, L t o j := by
    intro n
    exact TransportCertificate.weighted_chain_bound
      (A := fun _ => ℝ)
      (defect := fun _ => dist)
      (ideal := fun m => observe o (advance t (seq m)))
      (actual := fun m => observe o (seq m))
      (step := step t o)
      (L := L t o)
      (ε := ε t o)
      (fun m => hcontract t o m)
      (fun m => dist_triangle _ _ _)
      (fun m => hlocal t o m)
      (fun m => hL0 t o m)
      n
  have hdist :
      Tendsto
        (fun n =>
          dist
            (observe o (advance t (seq n)))
            (observe o (seq n)))
        atTop (𝓝 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds
      (hvanish t o)
      (Eventually.of_forall fun n => dist_nonneg)
      (Eventually.of_forall fun n => hupper n)
  rw [tendsto_zero_iff_abs_tendsto_zero]
  change
    Tendsto
      (fun n =>
        |observe o (advance t (seq n)) - observe o (seq n)|)
      atTop (𝓝 0)
  simpa [Real.dist_eq] using hdist

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
