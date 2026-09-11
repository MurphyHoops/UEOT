import UEOT.V3.FisherGauge
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

This file machine-checks the PSD kernel mechanism, centered independent cross
term cancellation, finite-dimensional Fisher-entry accumulation, and the
corresponding Fisher-operator additivity.
-/

namespace UEOT.V3.FisherIntersection

open MeasureTheory ProbabilityTheory
open UEOT.V3.FisherGauge
open scoped BigOperators

/-- Pointwise sum of finitely many linear/Fisher actions. -/
def totalAction {E d : ℕ}
    (A : Fin E → (Fin d → ℝ) → (Fin d → ℝ))
    (v : Fin d → ℝ) : Fin d → ℝ :=
  fun i => ∑ e, A e v i

/-- Abstract PSD quadratic data for a family of Fisher blocks. `quad e v` is the
quadratic form of block `e`. -/
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
cross term vanishes. This is the exact probabilistic cancellation used when
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

/-- Coordinatewise sum of finitely many experiment scores. -/
def scoreSum {E d : ℕ} (s : Fin E → Ω → Fin d → ℝ) : Ω → Fin d → ℝ :=
  fun ω i => ∑ e, s e ω i

/-- A finite-dimensional Fisher matrix entry written directly as a score
second moment. -/
noncomputable def fisherEntry {d : ℕ} (μ : Measure Ω) (s : Ω → Fin d → ℝ)
    (i j : Fin d) : ℝ :=
  ∫ ω, s ω i * s ω j ∂μ

/-- Under coordinatewise independence across distinct experiments and centered
scores, the Fisher matrix of the summed score is the sum of experiment Fisher
matrices. Pairwise integrability is stated explicitly so the Bochner integral
linearity step is fully justified. -/
theorem fisherEntry_scoreSum_eq_sum
    {E d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Fin E → Ω → Fin d → ℝ)
    (h_int : ∀ e f i j,
      Integrable (fun ω => s e ω i * s f ω j) μ)
    (h_indep : ∀ e f, e ≠ f → ∀ i j,
      (fun ω => s e ω i) ⟂ᵢ[μ] (fun ω => s f ω j))
    (h_meas : ∀ e i, AEStronglyMeasurable (fun ω => s e ω i) μ)
    (h_centered : ∀ e i, ∫ ω, s e ω i ∂μ = 0)
    (i j : Fin d) :
    fisherEntry μ (scoreSum s) i j = ∑ e, fisherEntry μ (s e) i j := by
  unfold fisherEntry scoreSum
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro e he
    rw [integral_finsetSum]
    · rw [Finset.sum_eq_single e]
      · intro f hf hfe
        exact independent_centered_cross_integral_eq_zero μ
          (h_indep e f (Ne.symm hfe) i j) (h_meas e i) (h_meas f j)
          (h_centered e i) (h_centered f j)
      · simp
    · intro f hf
      exact h_int e f i j
  · intro e he
    exact integrable_finsetSum _ (fun f hf => h_int e f i j)

/-- Pairwise score-product integrability implies integrability of every product
of two coordinates of the summed score. -/
theorem integrable_scoreSum_mul_scoreSum
    {E d : ℕ}
    (μ : Measure Ω)
    (s : Fin E → Ω → Fin d → ℝ)
    (h_int : ∀ e f i j,
      Integrable (fun ω => s e ω i * s f ω j) μ)
    (i j : Fin d) :
    Integrable (fun ω => scoreSum s ω i * scoreSum s ω j) μ := by
  simp only [scoreSum]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  exact integrable_finsetSum _ (fun e _ =>
    integrable_finsetSum _ (fun f _ => h_int e f i j))

/-- Coordinate form of Fisher action: `I v` is matrix-vector multiplication by
the Fisher entries. -/
theorem fisherAction_apply_eq_sum_fisherEntry_mul
    {d : ℕ}
    (μ : Measure Ω)
    (s : Ω → Fin d → ℝ)
    (h_int : ∀ i j, Integrable (fun ω => s ω i * s ω j) μ)
    (v : Fin d → ℝ) (i : Fin d) :
    fisherAction μ s v i = ∑ j, fisherEntry μ s i j * v j := by
  unfold fisherAction directionalScore fisherEntry
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    simpa [mul_assoc] using
      (integral_mul_const (v j) (fun ω => s ω i * s ω j) :
        (∫ ω, (s ω i * s ω j) * v j ∂μ) =
          (∫ ω, s ω i * s ω j ∂μ) * v j)
  · intro j hj
    simpa only [mul_assoc] using (h_int i j).mul_const (v j)

/-- Fisher information is additive as an operator under the same centered
cross-experiment independence hypotheses used for entry-wise additivity. -/
theorem fisherAction_scoreSum_eq_totalAction
    {E d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Fin E → Ω → Fin d → ℝ)
    (h_int : ∀ e f i j,
      Integrable (fun ω => s e ω i * s f ω j) μ)
    (h_indep : ∀ e f, e ≠ f → ∀ i j,
      (fun ω => s e ω i) ⟂ᵢ[μ] (fun ω => s f ω j))
    (h_meas : ∀ e i, AEStronglyMeasurable (fun ω => s e ω i) μ)
    (h_centered : ∀ e i, ∫ ω, s e ω i ∂μ = 0)
    (v : Fin d → ℝ) :
    fisherAction μ (scoreSum s) v =
      totalAction (fun e => fisherAction μ (s e)) v := by
  funext i
  calc
    fisherAction μ (scoreSum s) v i
        = ∑ j, fisherEntry μ (scoreSum s) i j * v j :=
      fisherAction_apply_eq_sum_fisherEntry_mul μ (scoreSum s)
        (fun a b => integrable_scoreSum_mul_scoreSum μ s h_int a b) v i
    _ = ∑ j, (∑ e, fisherEntry μ (s e) i j) * v j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [fisherEntry_scoreSum_eq_sum μ s h_int h_indep h_meas h_centered]
    _ = ∑ j, ∑ e, fisherEntry μ (s e) i j * v j := by
      simp_rw [Finset.sum_mul]
    _ = ∑ e, ∑ j, fisherEntry μ (s e) i j * v j := by
      rw [Finset.sum_comm]
    _ = ∑ e, fisherAction μ (s e) v i := by
      apply Finset.sum_congr rfl
      intro e he
      symm
      exact fisherAction_apply_eq_sum_fisherEntry_mul μ (s e)
        (fun a b => h_int e e a b) v i
    _ = totalAction (fun e => fisherAction μ (s e)) v i := by rfl

end UEOT.V3.FisherIntersection
