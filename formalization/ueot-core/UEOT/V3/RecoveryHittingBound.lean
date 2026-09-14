import UEOT.V3.RecoveryHittingDrift

/-!
# P-REC-04 — drift implies a finite recovery-time bound

This file closes the discrete recovery-time argument from the Core 3 source.
The proof uses the nonnegative tail-sum representation of the hitting time:

`E τ_A = sup_N sum_{n < N} P(τ_A > n)`.

The one-step survival-potential drift proved in `RecoveryHittingDrift` telescopes
at every finite horizon.  Monotone convergence then gives the full hitting-time
bound without adding an optional-stopping or integrability hypothesis beyond
the source kernel drift.
-/

namespace UEOT.V3.RecoveryHittingBound

open Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder ProbabilityTheory
open UEOT.V3.DynamicsKernel
open UEOT.V3.RecoveryHittingNonnegative
open UEOT.V3.RecoveryHittingDrift
open scoped ENNReal ProbabilityTheory

universe uX

variable {X : Type uX} [MeasurableSpace X]

/-- The pathwise truncations of the hitting time increase with the horizon. -/
theorem monotone_truncatedHittingValue
    (A : Set X) (ω : ℕ → X) :
    Monotone fun N => truncatedHittingValue A N ω := by
  apply monotone_nat_of_le_succ
  intro N
  unfold truncatedHittingValue
  rw [Finset.sum_range_succ]
  exact self_le_add_right _ _

/-- Integrating the pathwise truncated hitting time is exactly the finite
survival-probability tail sum. -/
theorem lintegral_truncatedHittingValue_eq_truncatedExpectedHittingTime
    (P : Kernel X X) [IsMarkovKernel P]
    (x : X) (A : Set X) (hA : MeasurableSet A) (N : ℕ) :
    (∫⁻ ω,
      truncatedHittingValue A N ω
      ∂homTrajMeasure (Measure.dirac x) P) =
      truncatedExpectedHittingTime P x A N := by
  unfold truncatedHittingValue truncatedExpectedHittingTime
  rw [lintegral_finsetSum (range N)]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [lintegral_indicator_const (measurableSet_survivalSet hA n) 1]
    simp only [one_mul]
    unfold survivalProb prefixLaw survivalSet
    rw [Measure.map_apply (measurable_frestrictLe n)
      (measurableSet_historySurvivalSet hA n)]
  · intro n hn
    exact measurable_const.indicator (measurableSet_survivalSet hA n)

/-- The extended hitting-time expectation is the monotone supremum of its
finite tail-sum truncations. -/
theorem expectedHittingTime_eq_iSup_truncatedExpectedHittingTime
    (P : Kernel X X) [IsMarkovKernel P]
    (x : X) (A : Set X) (hA : MeasurableSet A) :
    expectedHittingTime P x A =
      ⨆ N : ℕ, truncatedExpectedHittingTime P x A N := by
  unfold expectedHittingTime hittingValue
  rw [lintegral_iSup]
  · congr with N
    exact lintegral_truncatedHittingValue_eq_truncatedExpectedHittingTime
      P x A hA N
  · intro N
    exact measurable_truncatedHittingValue hA N
  · intro N M hNM ω
    exact monotone_truncatedHittingValue A ω hNM

/-- At horizon zero the surviving potential is bounded by the deterministic
initial potential.  This also covers the trivial case `x ∈ A`, where the
survival indicator vanishes. -/
theorem survivalPotentialMean_zero_le_initial
    (P : Kernel X X) [IsMarkovKernel P]
    (x : X) (A : Set X) (V : X → ℝ≥0∞)
    (hA : MeasurableSet A) (hV : Measurable V) :
    survivalPotentialMean P x A V 0 ≤ V x := by
  let e : ((i : Iic 0) → X) ≃ᵐ X :=
    MeasurableEquiv.piUnique (fun _ : Iic 0 => X)
  have hprefix :
      prefixLaw P x 0 = (Measure.dirac x).map e.symm := by
    unfold prefixLaw
    simpa [e] using homTrajMeasure_prefix_zero (Measure.dirac x) P
  unfold survivalPotentialMean
  rw [hprefix]
  rw [lintegral_map
    (measurable_historySurvivalPotential hA hV 0)
    e.symm.measurable]
  rw [lintegral_dirac' x
    ((measurable_historySurvivalPotential hA hV 0).comp e.symm.measurable)]
  have hcoord : (e.symm x) (lastHistoryIndex 0) = x := by
    have he := e.apply_symm_apply x
    change (e.symm x) default = x at he
    have hi : lastHistoryIndex 0 = default := Subsingleton.elim _ _
    simpa [hi] using he
  unfold historySurvivalPotential
  calc
    (historySurvivalSet A 0).indicator
        (fun h => V (h (lastHistoryIndex 0))) (e.symm x)
        ≤ V ((e.symm x) (lastHistoryIndex 0)) :=
      Set.indicator_apply_le fun _ => le_rfl
    _ = V x := by rw [hcoord]

/-- The integrated one-step drift telescopes over every finite horizon. -/
theorem survivalPotentialMean_add_truncatedExpectedHittingTime_le_initial
    (P : Kernel X X) [IsMarkovKernel P]
    (x : X) (A : Set X) (V : X → ℝ≥0∞) (c : ℝ≥0∞)
    (hA : MeasurableSet A) (hV : Measurable V)
    (hdrift : ∀ z, z ∉ A → (∫⁻ y, V y ∂P z) + c ≤ V z)
    (N : ℕ) :
    survivalPotentialMean P x A V N +
        c * truncatedExpectedHittingTime P x A N ≤
      survivalPotentialMean P x A V 0 := by
  induction N with
  | zero =>
      simp [truncatedExpectedHittingTime]
  | succ N ih =>
      have hstep :=
        survivalPotentialMean_succ_add_survival_le
          P x A V c hA hV hdrift N
      calc
        survivalPotentialMean P x A V (N + 1) +
            c * truncatedExpectedHittingTime P x A (N + 1) =
          (survivalPotentialMean P x A V (N + 1) +
              c * survivalProb P x A N) +
            c * truncatedExpectedHittingTime P x A N := by
              simp only [truncatedExpectedHittingTime,
                Finset.sum_range_succ, mul_add]
              ac_rfl
        _ ≤ survivalPotentialMean P x A V N +
              c * truncatedExpectedHittingTime P x A N :=
          add_le_add hstep (le_refl _)
        _ ≤ survivalPotentialMean P x A V 0 := ih

/-- Every finite truncation of the recovery time satisfies the source
Lyapunov bound. -/
theorem c_mul_truncatedExpectedHittingTime_le_initial
    (P : Kernel X X) [IsMarkovKernel P]
    (x : X) (A : Set X) (V : X → ℝ≥0∞) (c : ℝ≥0∞)
    (hA : MeasurableSet A) (hV : Measurable V)
    (hdrift : ∀ z, z ∉ A → (∫⁻ y, V y ∂P z) + c ≤ V z)
    (N : ℕ) :
    c * truncatedExpectedHittingTime P x A N ≤ V x := by
  have htel :=
    survivalPotentialMean_add_truncatedExpectedHittingTime_le_initial
      P x A V c hA hV hdrift N
  have hdrop :
      c * truncatedExpectedHittingTime P x A N ≤
        survivalPotentialMean P x A V N +
          c * truncatedExpectedHittingTime P x A N :=
    self_le_add_left _ _
  exact (hdrop.trans htel).trans
    (survivalPotentialMean_zero_le_initial P x A V hA hV)

/-- Nonnegative source form of P-REC-04 before dividing by the positive drift
constant. -/
theorem c_mul_expectedHittingTime_le_initial
    (P : Kernel X X) [IsMarkovKernel P]
    (x : X) (A : Set X) (V : X → ℝ≥0∞) (c : ℝ≥0∞)
    (hA : MeasurableSet A) (hV : Measurable V)
    (hdrift : ∀ z, z ∉ A → (∫⁻ y, V y ∂P z) + c ≤ V z) :
    c * expectedHittingTime P x A ≤ V x := by
  rw [expectedHittingTime_eq_iSup_truncatedExpectedHittingTime P x A hA]
  rw [ENNReal.mul_iSup]
  exact iSup_le fun N =>
    c_mul_truncatedExpectedHittingTime_le_initial
      P x A V c hA hV hdrift N

/-- **P-REC-04 (drift implies recovery time).**  For the canonical homogeneous
Markov chain, a measurable nonnegative potential with uniform drift at least
`c > 0` outside the target set satisfies

`E_x τ_A ≤ V(x) / c`.

The two explicit side conditions on `c` are precisely positivity and finiteness
in `ℝ≥0∞`.  The Core 3 finite-valued formulation is therefore an immediate
special case. -/
theorem p_rec_04_hitting_time_bound
    (P : Kernel X X) [IsMarkovKernel P]
    (x : X) (A : Set X) (V : X → ℝ≥0∞) (c : ℝ≥0∞)
    (hA : MeasurableSet A) (hV : Measurable V)
    (hc0 : c ≠ 0) (hctop : c ≠ ∞)
    (hdrift : ∀ z, z ∉ A → (∫⁻ y, V y ∂P z) + c ≤ V z) :
    expectedHittingTime P x A ≤ V x / c := by
  apply (ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hctop)).2
  simpa [mul_comm] using
    c_mul_expectedHittingTime_le_initial P x A V c hA hV hdrift

end UEOT.V3.RecoveryHittingBound
