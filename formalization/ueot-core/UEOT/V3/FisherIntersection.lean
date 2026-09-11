import UEOT.V3.FisherGauge
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic

/-!
# P-INV-03 — Fisher accumulation and kernel intersection

The frozen theorem has two steps:
1. conditional independence plus zero-mean scores makes total Fisher equal the
   sum of the experiment-wise Fisher matrices;
2. since every Fisher block is positive semidefinite, the kernel of that sum is
   exactly the intersection of the individual kernels.

This file machine-checks the PSD kernel mechanism, centered independent cross
term cancellation, finite-dimensional Fisher-entry accumulation, Fisher
operator additivity, positivity of the actual Fisher quadratic form, and the
source-facing kernel-intersection theorem.
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

/-- The abstract PSD kernel-intersection mechanism used by P-INV-03. -/
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

/-- The actual Fisher quadratic form `vᵀIv = E[(vᵀs)^2]`. -/
noncomputable def fisherQuadratic {d : ℕ}
    (μ : Measure Ω) (s : Ω → Fin d → ℝ) (v : Fin d → ℝ) : ℝ :=
  ∫ ω, (directionalScore s v ω) ^ 2 ∂μ

/-- Fisher quadratic forms are nonnegative. -/
theorem fisherQuadratic_nonneg {d : ℕ}
    (μ : Measure Ω) (s : Ω → Fin d → ℝ) (v : Fin d → ℝ) :
    0 ≤ fisherQuadratic μ s v := by
  unfold fisherQuadratic
  exact integral_nonneg_of_ae
    (Filter.Eventually.of_forall fun ω => sq_nonneg (directionalScore s v ω))

/-- Pairwise score-product integrability implies integrability of `s_i (vᵀs)`. -/
theorem integrable_score_mul_directionalScore {d : ℕ}
    (μ : Measure Ω) (s : Ω → Fin d → ℝ)
    (h_int : ∀ i j, Integrable (fun ω => s ω i * s ω j) μ)
    (v : Fin d → ℝ) (i : Fin d) :
    Integrable (fun ω => s ω i * directionalScore s v ω) μ := by
  unfold directionalScore
  simp_rw [Finset.mul_sum]
  exact integrable_finsetSum _ (fun j _ => by
    simpa [mul_assoc] using (h_int i j).mul_const (v j))

/-- Pairwise score-product integrability implies integrability of `(vᵀs)^2`. -/
theorem integrable_directionalScore_sq {d : ℕ}
    (μ : Measure Ω) (s : Ω → Fin d → ℝ)
    (h_int : ∀ i j, Integrable (fun ω => s ω i * s ω j) μ)
    (v : Fin d → ℝ) :
    Integrable (fun ω => (directionalScore s v ω) ^ 2) μ := by
  unfold directionalScore
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
  exact integrable_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (h_int i j).mul_const (v i * v j)))

/-- The Fisher quadratic form is the Euclidean pairing of `Iv` with `v`. -/
theorem fisherQuadratic_eq_sum_action_mul {d : ℕ}
    (μ : Measure Ω) (s : Ω → Fin d → ℝ)
    (h_int : ∀ i j, Integrable (fun ω => s ω i * s ω j) μ)
    (v : Fin d → ℝ) :
    fisherQuadratic μ s v = ∑ i, fisherAction μ s v i * v i := by
  have hpoint : ∀ ω,
      (directionalScore s v ω) ^ 2 =
        ∑ i, (s ω i * directionalScore s v ω) * v i := by
    intro ω
    calc
      (directionalScore s v ω) ^ 2
          = directionalScore s v ω * directionalScore s v ω := by rw [pow_two]
      _ = (∑ i, s ω i * v i) * directionalScore s v ω := by rfl
      _ = ∑ i, (s ω i * v i) * directionalScore s v ω := by
        rw [Finset.sum_mul]
      _ = ∑ i, (s ω i * directionalScore s v ω) * v i := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
  unfold fisherQuadratic
  calc
    (∫ ω, (directionalScore s v ω) ^ 2 ∂μ)
        = ∫ ω, ∑ i, (s ω i * directionalScore s v ω) * v i ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = ∑ i, ∫ ω, (s ω i * directionalScore s v ω) * v i ∂μ := by
      rw [integral_finsetSum]
      intro i hi
      exact (integrable_score_mul_directionalScore μ s h_int v i).mul_const (v i)
    _ = ∑ i, fisherAction μ s v i * v i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_mul_const]
      rfl

/-- For an actual Fisher block, quadratic zero is equivalent to being in the
Fisher kernel. This discharges the PSD zero-direction step used in the source
proof, rather than assuming it abstractly. -/
theorem fisherQuadratic_eq_zero_iff_fisherAction_eq_zero {d : ℕ}
    (μ : Measure Ω) (s : Ω → Fin d → ℝ)
    (h_int : ∀ i j, Integrable (fun ω => s ω i * s ω j) μ)
    (v : Fin d → ℝ) :
    fisherQuadratic μ s v = 0 ↔ fisherAction μ s v = 0 := by
  constructor
  · intro hq
    have haeSq :
        (fun ω => (directionalScore s v ω) ^ 2) =ᵐ[μ] (fun _ => (0 : ℝ)) :=
      (integral_eq_zero_iff_of_nonneg_ae
        (Filter.Eventually.of_forall fun ω => sq_nonneg (directionalScore s v ω))
        (integrable_directionalScore_sq μ s h_int v)).1 hq
    have hzero : OrbitTangentScoreZero μ s v := by
      filter_upwards [haeSq] with ω hω
      exact sq_eq_zero_iff.mp (by simpa using hω)
    exact fisherAction_eq_zero_of_orbitTangentScoreZero μ s v hzero
  · intro ha
    rw [fisherQuadratic_eq_sum_action_mul μ s h_int v]
    simp [ha]

/-- Independence and centering make the total Fisher quadratic form equal the
sum of the experiment-wise Fisher quadratic forms. -/
theorem fisherQuadratic_scoreSum_eq_sum
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
    fisherQuadratic μ (scoreSum s) v = ∑ e, fisherQuadratic μ (s e) v := by
  rw [fisherQuadratic_eq_sum_action_mul μ (scoreSum s)
    (fun i j => integrable_scoreSum_mul_scoreSum μ s h_int i j) v]
  rw [fisherAction_scoreSum_eq_totalAction μ s h_int h_indep h_meas h_centered v]
  unfold totalAction
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  symm
  exact fisherQuadratic_eq_sum_action_mul μ (s e) (fun i j => h_int e e i j) v

/-- **P-INV-03. Multi-Intervention Fisher Kernel Intersection Theorem.**
For conditionally independent/independent centered experiment scores, the
joint Fisher operator is the sum of the experiment Fisher operators and its
kernel is exactly their kernel intersection. -/
theorem p_inv_03
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
    fisherAction μ (scoreSum s) v = 0 ↔
      ∀ e, fisherAction μ (s e) v = 0 := by
  constructor
  · intro htotal
    have hqTotal : fisherQuadratic μ (scoreSum s) v = 0 :=
      (fisherQuadratic_eq_zero_iff_fisherAction_eq_zero μ (scoreSum s)
        (fun i j => integrable_scoreSum_mul_scoreSum μ s h_int i j) v).2 htotal
    have hsum : (∑ e, fisherQuadratic μ (s e) v) = 0 := by
      rw [← fisherQuadratic_scoreSum_eq_sum μ s h_int h_indep h_meas h_centered v]
      exact hqTotal
    have hEach := (Finset.sum_eq_zero_iff_of_nonneg
      (s := Finset.univ) (f := fun e : Fin E => fisherQuadratic μ (s e) v)
      (fun e _ => fisherQuadratic_nonneg μ (s e) v)).mp hsum
    intro e
    apply (fisherQuadratic_eq_zero_iff_fisherAction_eq_zero μ (s e)
      (fun i j => h_int e e i j) v).1
    exact hEach e (Finset.mem_univ e)
  · intro hEach
    rw [fisherAction_scoreSum_eq_totalAction μ s h_int h_indep h_meas h_centered v]
    funext i
    unfold totalAction
    apply Finset.sum_eq_zero
    intro e he
    exact congrFun (hEach e) i

end UEOT.V3.FisherIntersection
