import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# P-PER-04 — tangency necessity

Frozen UEOT Core 3 §8.6 uses the Bouligand contingent cone defined by
positive-time increments `h ↓ 0`.  Mathlib's matching object is
`posTangentConeAt`, i.e. `tangentConeAt NNReal`, rather than the two-sided
real-scalar tangent cone.

The proof is the source proof in filter form.  A differentiable viable curve
has positive-time difference quotients converging to its initial velocity.
Those same increments are points of the viability domain, so they provide the
witness required by `mem_tangentConeAt_of_seq`.
-/

namespace UEOT.V3.ViabilityTangency

open Filter Set
open scoped Topology NNReal

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **P-PER-04 (tangency necessity).**

Let `V` be the closed identity/viability domain from the frozen source.  If a
curve is differentiable at zero and remains in `V` for nonnegative time, its
initial velocity belongs to the positive Bouligand contingent cone of `V` at
its initial point.

Closedness is part of the frozen §8.6 domain contract; the necessity argument
itself is local and in fact does not need to use it. -/
theorem p_per_04
    (V : Set E) (_hV : IsClosed V)
    (x : ℝ → E) (v : E)
    (hdiff : HasDerivAt x v 0)
    (hstay : ∀ t : ℝ, 0 ≤ t → x t ∈ V) :
    v ∈ posTangentConeAt V (x 0) := by
  let d : ℝ≥0 → E := fun t => x (t : ℝ) - x 0

  have hcoe :
      Tendsto ((↑) : ℝ≥0 → ℝ) (𝓝[>] (0 : ℝ≥0)) (𝓝[>] (0 : ℝ)) := by
    change Filter.map ((↑) : ℝ≥0 → ℝ) (𝓝[>] (0 : ℝ≥0)) ≤ 𝓝[>] (0 : ℝ)
    simpa using (le_refl (𝓝[>] (0 : ℝ)))

  have hcontRight : Tendsto x (𝓝[>] (0 : ℝ)) (𝓝 (x 0)) := by
    exact hdiff.continuousAt.mono_left inf_le_left

  have hd0 : Tendsto d (𝓝[>] (0 : ℝ≥0)) (𝓝 0) := by
    have hpath : Tendsto (fun t : ℝ≥0 => x (t : ℝ))
        (𝓝[>] (0 : ℝ≥0)) (𝓝 (x 0)) := hcontRight.comp hcoe
    have hconst : Tendsto (fun _ : ℝ≥0 => x 0)
        (𝓝[>] (0 : ℝ≥0)) (𝓝 (x 0)) := tendsto_const_nhds
    have hsub : Tendsto (fun t : ℝ≥0 => x (t : ℝ) - x 0)
        (𝓝[>] (0 : ℝ≥0)) (𝓝 (x 0 - x 0)) := hpath.sub hconst
    simpa [d] using hsub

  have hmem : ∀ᶠ t in 𝓝[>] (0 : ℝ≥0), x 0 + d t ∈ V := by
    refine Filter.Eventually.of_forall ?_
    intro t
    have ht : x (t : ℝ) ∈ V := hstay (t : ℝ) t.2
    simpa [d, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using ht

  have hslopeReal :
      Tendsto (fun t : ℝ≥0 => ((t : ℝ))⁻¹ • (x (t : ℝ) - x 0))
        (𝓝[>] (0 : ℝ≥0)) (𝓝 v) := by
    have h := hdiff.tendsto_slope_zero_right.comp hcoe
    simpa [Function.comp_def] using h

  have hscaled :
      Tendsto (fun t : ℝ≥0 => t⁻¹ • d t)
        (𝓝[>] (0 : ℝ≥0)) (𝓝 v) := by
    simpa [d, NNReal.smul_def] using hslopeReal

  exact mem_tangentConeAt_of_seq
    (x := x 0) (y := v) (s := V)
    (𝓝[>] (0 : ℝ≥0)) (fun t : ℝ≥0 => t⁻¹) d hd0 hmem hscaled

end UEOT.V3.ViabilityTangency
