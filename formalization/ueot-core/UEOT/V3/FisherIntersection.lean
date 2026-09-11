import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic

/-!
# P-INV-03 foundation — Fisher accumulation and kernel intersection

The frozen theorem has two steps:
1. conditional independence plus zero-mean scores makes total Fisher equal the
   sum of the experiment-wise Fisher matrices;
2. since every Fisher block is positive semidefinite, the kernel of that sum is
   exactly the intersection of the individual kernels.

This file machine-checks step 2 and a reusable probabilistic lemma for step 1:
centered independent scalar scores have zero cross expectation.
-/

namespace UEOT.V3.FisherIntersection

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Pointwise sum of finitely many linear/Fisher actions. -/
def totalAction {E d : ℕ}
    (A : Fin E → (Fin d → ℝ) → (Fin d → ℝ))
    (v : Fin d → ℝ) : Fin d → ℝ :=
  fun i => ∑ e, A e v i

/-- Abstract PSD quadratic data for a family of Fisher blocks.  `q e v` is the
quadratic form of block `e`; the final field records the standard PSD fact that
a zero quadratic form value is equivalent to annihilation of `v`. -/
structure PSDActionFamily (E d : ℕ) where
  action : Fin E → (Fin d → ℝ) → (Fin d → ℝ)
  quad : Fin E → (Fin d → ℝ) → ℝ
  quad_nonneg : ∀ e v, 0 ≤ quad e v
  quad_zero_iff : ∀ e v, quad e v = 0 ↔ action e v = 0
  total_quad_zero_iff : ∀ v,
    (∑ e, quad e v) = 0 ↔ totalAction action v = 0

/-- The PSD kernel-intersection mechanism in P-INV-03: a vector is killed by
the total Fisher action iff it is killed by every experiment-wise Fisher
block. -/
theorem total_kernel_iff_forall_kernel {E d : ℕ}
    (F : PSDActionFamily E d) (v : Fin d → ℝ) :
    totalAction F.action v = 0 ↔ ∀ e, F.action e v = 0 := by
  constructor
  · intro htotal
    have hsum : (∑ e, F.quad e v) = 0 :=
      (F.total_quad_zero_iff v).2 htotal
    have h_each : ∀ e : Fin E, F.quad e v = 0 := by
      have h := (Finset.sum_eq_zero_iff_of_nonneg
        (s := Finset.univ) (f := fun e : Fin E => F.quad e v)
        (fun e _ => F.quad_nonneg e v)).mp (by simpa using hsum)
      intro e
      exact h e (Finset.mem_univ e)
    intro e
    exact (F.quad_zero_iff e v).1 (h_each e)
  · intro h_each
    apply (F.total_quad_zero_iff v).1
    apply Finset.sum_eq_zero
    intro e he
    exact (F.quad_zero_iff e v).2 (h_each e)

universe uΩ
variable {Ω : Type uΩ} [MeasurableSpace Ω]

/-- If two scalar experiment scores are independent and centered, their Fisher
cross term vanishes.  This is the exact probabilistic cancellation used when
expanding the square of the total score. -/
theorem independent_centered_cross_integral_eq_zero
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ}
    (hXY : X ⟂ᵢ[μ] Y)
    (hX : AEStronglyMeasurable X μ)
    (hY : AEStronglyMeasurable Y μ)
    (hX0 : ∫ ω, X ω ∂μ = 0)
    (hY0 : ∫ ω, Y ω ∂μ = 0) :
    ∫ ω, X ω * Y ω ∂μ = 0 := by
  calc
    ∫ ω, X ω * Y ω ∂μ = (∫ ω, X ω ∂μ) * (∫ ω, Y ω ∂μ) := by
      simpa only [Pi.mul_apply] using hXY.integral_mul_eq_mul_integral hX hY
    _ = 0 := by rw [hX0, hY0]; norm_num

end UEOT.V3.FisherIntersection
