import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorIntegralContinuousVersion
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralSquareL1
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
Original commitment: P11 finite-vector actual-path calculus needs SAME-input partition energy, not a supplied quadratic-variation law.
Existing result: original full joint-predictable Euclidean input, cutoff isometry/conditional projection and actual continuous integral version.
Premise reduced: derive EVERY finite monotone 0/T grid's total increment energy and grid-uniform L1 stability without L4.
Model: original productLaw d/inputLaw d T/jointNaturalFiltration, finite d including0, T0/repeated deterministic times, no new coefficient permissions.
Consumer: actual full-input vector-noise partition QV and state-Ito dependencies; this module proves stability/binding, not QV convergence or general SDE.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorIntegralGridL1
open MeasureTheory ProbabilityTheory Set Filter
open BrownianFiniteProductSource BrownianVectorTimeInput BrownianVectorIntegralClosure
open BrownianVectorPredictableInputs BrownianVectorPredictableDensity BrownianVectorIntegralTimeSource
open BrownianVectorIntegralConditionalSource BrownianVectorIntegralContinuousVersion
open BrownianIntegralSquareL1
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
variable (d : ℕ)

/-- Nesting uses the SAME actual cutoff, not a conditional-law assumption. -/
theorem truncate_nested (T s t : ℝ≥0) (hst : s≤t) (f : fullPredictableL2 d T) :
    truncate d T s (truncate d T t f)=truncate d T s f := by
  have hsub : timeSet d T s ⊆ timeSet d T t := by
    intro p hp
    exact ⟨⟨hp.1.1,hp.1.2.trans (by exact_mod_cast min_le_min_right T hst)⟩,hp.2⟩
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [truncate_coe d T s (truncate d T t f),truncate_coe d T t f,
    truncate_coe d T s f] with p ho ht hs
  rw [ho,hs]
  by_cases hp : p∈timeSet d T s
  · rw [Set.indicator_of_mem hp,ht,Set.indicator_of_mem (hsub hp),Set.indicator_of_mem hp]
  · rw [Set.indicator_of_notMem hp,Set.indicator_of_notMem hp]

/-- The actual later integral's ORIGINAL joint-past projection is its actual
prefix, derived from the old source identity and nested cutoff. -/
theorem integral_projection_prefix (T s t : ℝ≥0) (hst : s≤t) (f : fullPredictableL2 d T) :
    naturalProjection d s (integralClassProcess d T f t)=integralClassProcess d T f s := by
  have h := integral_projection_identity d T s (truncate d T t f)
  change naturalProjection d s (integralClassProcess d T f t)=
    predictableIntegral d T (truncate d T s (truncate d T t f)) at h
  rwa [truncate_nested d T s t hst] at h

/-- Actual native SAME-source increment map. -/
def incrementAt (T s t : ℝ≥0) : fullPredictableL2 d T →L[ℝ] Lp ℝ 2 (productLaw d) :=
  integralAt d T t-integralAt d T s

theorem incrementAt_coe (T s t : ℝ≥0) (f : fullPredictableL2 d T) :
    (incrementAt d T s t f : Sample d → ℝ) =ᵐ[productLaw d]
      fun ω => continuousIntegralProcess d T f t ω-continuousIntegralProcess d T f s ω := by
  filter_upwards [Lp.coeFn_sub (integralClassProcess d T f t) (integralClassProcess d T f s),
    (continuousIntegralProcess_eq_actual d T t f).trans (integralProcess_eq_truncated d T t f),
    (continuousIntegralProcess_eq_actual d T s f).trans (integralProcess_eq_truncated d T s f)] with ω hd ht hs
  simp only [Pi.sub_apply] at hd
  exact hd.trans (congrArg₂ (fun x y : ℝ => x-y) ht.symm hs.symm)

/-- Genuine joint-natural conditional projection gives the actual Hilbert
increment energy. No desired compensator/QV field enters the proof. -/
theorem incrementAt_norm_sq (T s t : ℝ≥0) (hst : s≤t) (f : fullPredictableL2 d T) :
    ‖incrementAt d T s t f‖^2 =
      ‖integralClassProcess d T f t‖^2-‖integralClassProcess d T f s‖^2 := by
  have hg := mem_lpMeas_iff_aestronglyMeasurable.mp (integralClassProcess_adapted d T s f)
  have hi := inner_condExpL2_eq_inner_fun (𝕜 := ℝ) ((jointNaturalFiltration d).le s)
    (integralClassProcess d T f t) (integralClassProcess d T f s) hg
  change inner ℝ (naturalProjection d s (integralClassProcess d T f t))
    (integralClassProcess d T f s)=_ at hi
  rw [integral_projection_prefix d T s t hst,real_inner_self_eq_norm_sq] at hi
  change ‖integralClassProcess d T f t-integralClassProcess d T f s‖^2=_
  rw [norm_sub_sq_real,← hi]
  ring

/-- Exact total energy for EVERY original finite monotone 0/T clock. -/
theorem grid_total_energy {n : ℕ} (T : ℝ≥0) (τ : Fin (n+1) → ℝ≥0)
    (hτ : Monotone τ) (h0 : τ 0 = 0) (hT : τ (Fin.last n) = T) (f : fullPredictableL2 d T) :
    (∑ i : Fin n, ‖incrementAt d T (τ i.castSucc) (τ i.succ) f‖^2) = ‖f‖^2 := by
  have hinc (i : Fin n) : ‖incrementAt d T (τ i.castSucc) (τ i.succ) f‖^2 =
      ‖integralClassProcess d T f (τ i.succ)‖^2-‖integralClassProcess d T f (τ i.castSucc)‖^2 :=
    incrementAt_norm_sq d T _ _ (hτ (show i.castSucc ≤ i.succ by exact_mod_cast Nat.le_succ (i : ℕ))) f
  simp_rw [hinc]
  rw [Finset.sum_sub_distrib]
  have hz := Fin.sum_univ_succ (fun j => ‖integralClassProcess d T f (τ j)‖^2)
  have hN := Fin.sum_univ_castSucc (fun j => ‖integralClassProcess d T f (τ j)‖^2)
  have he : (∑ i : Fin n, ‖integralClassProcess d T f (τ i.succ)‖^2)-
      (∑ i : Fin n, ‖integralClassProcess d T f (τ i.castSucc)‖^2) =
      ‖integralClassProcess d T f (τ (Fin.last n))‖^2-‖integralClassProcess d T f (τ 0)‖^2 := by linarith
  rw [he,h0,hT,integralClassProcess_zero d,integralClassProcess_horizon d,predictableIntegral_norm d]
  simp

/-- Native source L1 class of the ACTUAL original integral-grid square sum. -/
def gridSquares {n : ℕ} (T : ℝ≥0) (τ : Fin (n+1) → ℝ≥0) (f : fullPredictableL2 d T) : Lp ℝ 1 (productLaw d) :=
  ∑ i : Fin n, squareClass (productLaw d) (incrementAt d T (τ i.castSucc) (τ i.succ) f)

private theorem grid_cauchy {n : ℕ} (T : ℝ≥0) (τ : Fin (n+1) → ℝ≥0)
    (hτ : Monotone τ) (h0 : τ 0 = 0) (hT : τ (Fin.last n) = T) (f g : fullPredictableL2 d T) :
    (∑ i : Fin n, ‖incrementAt d T (τ i.castSucc) (τ i.succ) f‖*‖incrementAt d T (τ i.castSucc) (τ i.succ) g‖) ≤
      ‖f‖*‖g‖ := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : Fin n => ‖incrementAt d T (τ i.castSucc) (τ i.succ) f‖)
    (fun i : Fin n => ‖incrementAt d T (τ i.castSucc) (τ i.succ) g‖)
  rw [grid_total_energy d T τ hτ h0 hT f,grid_total_energy d T τ hτ h0 hT g] at hc
  apply (sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  simpa only [mul_pow] using hc

/-- Grid-UNIFORM actual L1 stability at the ORIGINAL full input L2 scale.
No fourth moment or externally supplied quadratic variation is required. -/
theorem gridSquares_sub_norm_le {n : ℕ} (T : ℝ≥0) (τ : Fin (n+1) → ℝ≥0)
    (hτ : Monotone τ) (h0 : τ 0 = 0) (hT : τ (Fin.last n) = T) (f g : fullPredictableL2 d T) :
    ‖gridSquares d T τ f-gridSquares d T τ g‖ ≤ ‖f-g‖*(‖f‖+‖g‖) := by
  classical
  calc
    _ = ‖∑ i : Fin n, (squareClass (productLaw d) (incrementAt d T (τ i.castSucc) (τ i.succ) f)-
        squareClass (productLaw d) (incrementAt d T (τ i.castSucc) (τ i.succ) g))‖ := by rw [Finset.sum_sub_distrib]; rfl
    _ ≤ ∑ i : Fin n, ‖squareClass (productLaw d) (incrementAt d T (τ i.castSucc) (τ i.succ) f)-
        squareClass (productLaw d) (incrementAt d T (τ i.castSucc) (τ i.succ) g)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin n, ‖incrementAt d T (τ i.castSucc) (τ i.succ) (f-g)‖*
        (‖incrementAt d T (τ i.castSucc) (τ i.succ) f‖+‖incrementAt d T (τ i.castSucc) (τ i.succ) g‖) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [map_sub] using squareClass_sub_norm_le (productLaw d)
        (incrementAt d T (τ i.castSucc) (τ i.succ) f) (incrementAt d T (τ i.castSucc) (τ i.succ) g)
    _ = (∑ i : Fin n, ‖incrementAt d T (τ i.castSucc) (τ i.succ) (f-g)‖*‖incrementAt d T (τ i.castSucc) (τ i.succ) f‖)+
        (∑ i : Fin n, ‖incrementAt d T (τ i.castSucc) (τ i.succ) (f-g)‖*‖incrementAt d T (τ i.castSucc) (τ i.succ) g‖) := by
      simp only [mul_add,Finset.sum_add_distrib]
    _ ≤ ‖f-g‖*‖f‖+‖f-g‖*‖g‖ := add_le_add (grid_cauchy d T τ hτ h0 hT (f-g) f) (grid_cauchy d T τ hτ h0 hT (f-g) g)
    _ = _ := by ring

/-- Actual caller's path-square sum is the SAME native L1 class; only finitely
many source fixedtime identities are intersected for each caller clock. -/
theorem gridSquares_coe {n : ℕ} (T : ℝ≥0) (τ : Fin (n+1) → ℝ≥0) (f : fullPredictableL2 d T) :
    (gridSquares d T τ f : Sample d → ℝ) =ᵐ[productLaw d]
      fun ω => ∑ i : Fin n, (continuousIntegralProcess d T f (τ i.succ) ω-
        continuousIntegralProcess d T f (τ i.castSucc) ω)^2 := by
  have hi : ∀ᵐ ω ∂productLaw d, ∀ i : Fin n,
      squareClass (productLaw d) (incrementAt d T (τ i.castSucc) (τ i.succ) f) ω =
        (continuousIntegralProcess d T f (τ i.succ) ω-
          continuousIntegralProcess d T f (τ i.castSucc) ω)^2 :=
    ae_all_iff.mpr (fun i => (squareClass_coe (productLaw d) (incrementAt d T (τ i.castSucc) (τ i.succ) f)).trans
      ((incrementAt_coe d T (τ i.castSucc) (τ i.succ) f).mono (fun _ h => congrArg (fun x : ℝ => x^2) h)))
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin n => squareClass (productLaw d)
    (incrementAt d T (τ i.castSucc) (τ i.succ) f)),hi] with ω hs hi
  rw [gridSquares,hs]
  simp only [Finset.sum_apply] at *
  exact Finset.sum_congr rfl (fun i _ => hi i)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorIntegralGridL1
