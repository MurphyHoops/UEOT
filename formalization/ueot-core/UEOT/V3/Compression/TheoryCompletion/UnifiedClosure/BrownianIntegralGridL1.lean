import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralCompensator
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralSquareL1
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
Original commitment: general-input partition quadratic variation needs a grid-UNIFORM natural-L1 approximation bound.
Existing result: SAME actual integral localized second energy/time-energy identities and native square L1 estimate.
Premise reduced: derive each grid's total increment energy and uniform L1 stability from original source isometry.
Model/witness: SAME fullPredictableL2 T/sourceLaw/naturalFiltration; arbitrary original finite monotone 0/T clock.
Consumer: uniform-family full-input QV extension without L4; no partition-QV convergence or Ito is assumed here.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralGridL1
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianTimeIntegrand BrownianPredictableInputs BrownianPredictableDensity
open BrownianIntegralTimeTruncation BrownianIntegralMartingale BrownianIntegralContinuousVersion
open BrownianIntegralTimeEnergy BrownianIntegralPastLocalization BrownianIntegralCompensator BrownianIntegralSquareL1
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Original actual native integral increment map. -/
def incrementAt (T s t : ℝ≥0) : fullPredictableL2 T →L[ℝ] Lp ℝ 2 sourceLaw := integralAt T t-integralAt T s

theorem incrementAt_coe (T s t : ℝ≥0) (f : fullPredictableL2 T) :
    (incrementAt T s t f : (ℝ≥0 → ℝ) → ℝ) =ᵐ[sourceLaw]
      fun ω => continuousIntegralProcess T f t ω-continuousIntegralProcess T f s ω := by
  filter_upwards [Lp.coeFn_sub (integralClassProcess T f t) (integralClassProcess T f s),
    (continuousIntegralProcess_eq_actual T t f).trans (integralProcess_eq_truncated T t f),
    (continuousIntegralProcess_eq_actual T s f).trans (integralProcess_eq_truncated T s f)] with ω hd ht hs
  simp only [Pi.sub_apply] at hd
  exact hd.trans (congrArg₂ (fun x y : ℝ => x-y) ht.symm hs.symm)

private theorem lp_norm_sq {α : Type*} [MeasurableSpace α] (μ : Measure α) (g : Lp ℝ 2 μ) :
    ‖g‖^2 = ∫ a, g a^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]

private theorem integralClass_norm_moment (T s : ℝ≥0) (f : fullPredictableL2 T) :
    ‖integralClassProcess T f s‖^2 = ∫ ω, continuousIntegralProcess T f s ω^2 ∂sourceLaw := by
  rw [lp_norm_sq]
  apply integral_congr_ae
  exact ((continuousIntegralProcess_eq_actual T s f).trans (integralProcess_eq_truncated T s f)).symm.mono
    (fun _ h => congrArg (fun x : ℝ => x^2) h)

/-- Actual increment energy is its actual endpoint-energy difference. This
comes from PROVED localized source energy/Fubini, not a QV certificate. -/
theorem incrementAt_norm_sq (T s t : ℝ≥0) (hst : s ≤ t) (f : fullPredictableL2 T) :
    ‖incrementAt T s t f‖^2 = ‖integralClassProcess T f t‖^2-‖integralClassProcess T f s‖^2 := by
  have hM := localized_second_energy T s t hst univ MeasurableSet.univ f
  have hA := timeEnergy_increment_setIntegral T s t hst univ MeasurableSet.univ f
  simp only [Measure.restrict_univ] at hM hA
  calc
    _ = ∫ ω, (continuousIntegralProcess T f t ω-continuousIntegralProcess T f s ω)^2 ∂sourceLaw := by
      rw [lp_norm_sq]
      exact integral_congr_ae ((incrementAt_coe T s t f).mono (fun _ h => congrArg (fun x : ℝ => x^2) h))
    _ = ∫ ω, (timeEnergy T f t ω-timeEnergy T f s ω) ∂sourceLaw := hM.trans hA.symm
    _ = (∫ ω, timeEnergy T f t ω ∂sourceLaw)-(∫ ω, timeEnergy T f s ω ∂sourceLaw) :=
      integral_sub (timeEnergy_integrable T t f) (timeEnergy_integrable T s f)
    _ = _ := by
      rw [← continuousIntegralProcess_secondMoment_eq_timeEnergy T t f,
        ← continuousIntegralProcess_secondMoment_eq_timeEnergy T s f,
        integralClass_norm_moment,integralClass_norm_moment]

/-- Exact total energy for EVERY original finite monotone 0/T clock. -/
theorem grid_total_energy {n : ℕ} (T : ℝ≥0) (τ : Fin (n+1) → ℝ≥0)
    (hτ : Monotone τ) (h0 : τ 0 = 0) (hT : τ (Fin.last n) = T) (f : fullPredictableL2 T) :
    (∑ i : Fin n, ‖incrementAt T (τ i.castSucc) (τ i.succ) f‖^2) = ‖f‖^2 := by
  have hinc (i : Fin n) : ‖incrementAt T (τ i.castSucc) (τ i.succ) f‖^2 =
      ‖integralClassProcess T f (τ i.succ)‖^2-‖integralClassProcess T f (τ i.castSucc)‖^2 :=
    incrementAt_norm_sq T _ _ (hτ (show i.castSucc ≤ i.succ by exact_mod_cast Nat.le_succ (i : ℕ))) f
  simp_rw [hinc]
  rw [Finset.sum_sub_distrib]
  have hz := Fin.sum_univ_succ (fun j => ‖integralClassProcess T f (τ j)‖^2)
  have hN := Fin.sum_univ_castSucc (fun j => ‖integralClassProcess T f (τ j)‖^2)
  have he : (∑ i : Fin n, ‖integralClassProcess T f (τ i.succ)‖^2)-
      (∑ i : Fin n, ‖integralClassProcess T f (τ i.castSucc)‖^2) =
      ‖integralClassProcess T f (τ (Fin.last n))‖^2-‖integralClassProcess T f (τ 0)‖^2 := by linarith
  rw [he,h0,hT,integralClassProcess_zero,integralClassProcess_horizon,predictableIntegral_norm]
  simp

/-- Native source L1 class of the ACTUAL original integral-grid square sum. -/
def gridSquares {n : ℕ} (T : ℝ≥0) (τ : Fin (n+1) → ℝ≥0) (f : fullPredictableL2 T) : Lp ℝ 1 sourceLaw :=
  ∑ i : Fin n, squareClass sourceLaw (incrementAt T (τ i.castSucc) (τ i.succ) f)

private theorem grid_cauchy {n : ℕ} (T : ℝ≥0) (τ : Fin (n+1) → ℝ≥0)
    (hτ : Monotone τ) (h0 : τ 0 = 0) (hT : τ (Fin.last n) = T) (f g : fullPredictableL2 T) :
    (∑ i : Fin n, ‖incrementAt T (τ i.castSucc) (τ i.succ) f‖*‖incrementAt T (τ i.castSucc) (τ i.succ) g‖) ≤
      ‖f‖*‖g‖ := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : Fin n => ‖incrementAt T (τ i.castSucc) (τ i.succ) f‖)
    (fun i : Fin n => ‖incrementAt T (τ i.castSucc) (τ i.succ) g‖)
  rw [grid_total_energy T τ hτ h0 hT f,grid_total_energy T τ hτ h0 hT g] at hc
  apply (sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  simpa only [mul_pow] using hc

/-- Grid-UNIFORM actual L1 stability at the ORIGINAL full input L2 scale.
No fourth moment or externally supplied quadratic variation is required. -/
theorem gridSquares_sub_norm_le {n : ℕ} (T : ℝ≥0) (τ : Fin (n+1) → ℝ≥0)
    (hτ : Monotone τ) (h0 : τ 0 = 0) (hT : τ (Fin.last n) = T) (f g : fullPredictableL2 T) :
    ‖gridSquares T τ f-gridSquares T τ g‖ ≤ ‖f-g‖*(‖f‖+‖g‖) := by
  classical
  calc
    _ = ‖∑ i : Fin n, (squareClass sourceLaw (incrementAt T (τ i.castSucc) (τ i.succ) f)-
        squareClass sourceLaw (incrementAt T (τ i.castSucc) (τ i.succ) g))‖ := by rw [Finset.sum_sub_distrib]; rfl
    _ ≤ ∑ i : Fin n, ‖squareClass sourceLaw (incrementAt T (τ i.castSucc) (τ i.succ) f)-
        squareClass sourceLaw (incrementAt T (τ i.castSucc) (τ i.succ) g)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin n, ‖incrementAt T (τ i.castSucc) (τ i.succ) (f-g)‖*
        (‖incrementAt T (τ i.castSucc) (τ i.succ) f‖+‖incrementAt T (τ i.castSucc) (τ i.succ) g‖) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [map_sub] using squareClass_sub_norm_le sourceLaw
        (incrementAt T (τ i.castSucc) (τ i.succ) f) (incrementAt T (τ i.castSucc) (τ i.succ) g)
    _ = (∑ i : Fin n, ‖incrementAt T (τ i.castSucc) (τ i.succ) (f-g)‖*‖incrementAt T (τ i.castSucc) (τ i.succ) f‖)+
        (∑ i : Fin n, ‖incrementAt T (τ i.castSucc) (τ i.succ) (f-g)‖*‖incrementAt T (τ i.castSucc) (τ i.succ) g‖) := by
      simp only [mul_add,Finset.sum_add_distrib]
    _ ≤ ‖f-g‖*‖f‖+‖f-g‖*‖g‖ := add_le_add (grid_cauchy T τ hτ h0 hT (f-g) f) (grid_cauchy T τ hτ h0 hT (f-g) g)
    _ = _ := by ring

private theorem lp1_sum_coe (S : Finset ι) (F : ι → Lp ℝ 1 sourceLaw) :
    (∑ i ∈ S, F i : Lp ℝ 1 sourceLaw) =ᵐ[sourceLaw] fun ω => ∑ i ∈ S, F i ω := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℝ 1 sourceLaw] with ω hω
    simp only [Finset.sum_empty]
    exact hω
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (F i) (∑ j ∈ S, F j),ih] with ω ha hs
    simp only [Pi.add_apply] at ha
    rw [ha,hs]

/-- The native L1 class in the stability bound is the caller's ACTUAL path
square-increment sum. Only finitely many fixedtime AE identities are used. -/
theorem gridSquares_coe {n : ℕ} (T : ℝ≥0) (τ : Fin (n+1) → ℝ≥0) (f : fullPredictableL2 T) :
    (gridSquares T τ f : (ℝ≥0 → ℝ) → ℝ) =ᵐ[sourceLaw]
      fun ω => ∑ i : Fin n, (continuousIntegralProcess T f (τ i.succ) ω-
        continuousIntegralProcess T f (τ i.castSucc) ω)^2 := by
  have hi : ∀ᵐ ω ∂sourceLaw, ∀ i : Fin n,
      squareClass sourceLaw (incrementAt T (τ i.castSucc) (τ i.succ) f) ω =
        (continuousIntegralProcess T f (τ i.succ) ω-continuousIntegralProcess T f (τ i.castSucc) ω)^2 :=
    ae_all_iff.mpr (fun i => (squareClass_coe sourceLaw (incrementAt T (τ i.castSucc) (τ i.succ) f)).trans
      ((incrementAt_coe T (τ i.castSucc) (τ i.succ) f).mono (fun _ h => congrArg (fun x : ℝ => x^2) h)))
  filter_upwards [lp1_sum_coe Finset.univ (fun i : Fin n => squareClass sourceLaw
    (incrementAt T (τ i.castSucc) (τ i.succ) f)),hi] with ω hs hi
  rw [show gridSquares T τ f = ∑ i : Fin n, squareClass sourceLaw
    (incrementAt T (τ i.castSucc) (τ i.succ) f) from rfl,hs]
  exact Finset.sum_congr rfl (fun i _ => hi i)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralGridL1
