import UEOT.V3.RecoveryHittingNonnegative

/-!
# P-REC-04 — survival-potential drift

This layer converts the source state-kernel Lyapunov drift into a pathwise
one-step inequality for histories that have not yet reached the target.  It
then integrates that inequality against the homogeneous Markov prefix law.

The resulting recurrence is the nonnegative analogue of the stopped
supermartingale step used in the Core 3 manuscript:

`Q (n+1) + c * P(τ_A > n) ≤ Q n`,

where `Q n = E[1_{τ_A > n} V(X_n)]`.
-/

namespace UEOT.V3.RecoveryHittingDrift

open Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder ProbabilityTheory
open UEOT.V3.DynamicsKernel
open UEOT.V3.RecoveryHittingNonnegative
open scoped ENNReal ProbabilityTheory

universe uX

variable {X : Type uX} [MeasurableSpace X]

/-- Appending one state preserves survival exactly when the old prefix survived
and the newly sampled state is still outside the target. -/
theorem appendHistory_mem_historySurvivalSet_iff
    (A : Set X) (n : ℕ)
    (h : (i : Iic n) → X) (y : X) :
    appendHistory n (h, y) ∈ historySurvivalSet A (n + 1) ↔
      h ∈ historySurvivalSet A n ∧ y ∉ A := by
  rw [mem_historySurvivalSet_iff, mem_historySurvivalSet_iff]
  constructor
  · intro hs
    constructor
    · intro i
      have hi : (i : ℕ) ≤ n := mem_Iic.mp i.2
      have hval := hs
        (⟨i.1, mem_Iic.mpr (hi.trans (Nat.le_succ n))⟩ : Iic (n + 1))
      simpa [appendHistory, IicProdIoc_def, hi] using hval
    · have hlast := hs (lastHistoryIndex (n + 1))
      simpa [appendHistory, lastHistoryIndex, IicProdIoc_def,
        MeasurableEquiv.piSingleton] using hlast
  · rintro ⟨hh, hy⟩ i
    by_cases hi : (i : ℕ) ≤ n
    · have hval := hh (⟨i.1, mem_Iic.mpr hi⟩ : Iic n)
      simpa [appendHistory, IicProdIoc_def, hi] using hval
    · have hin : (i : ℕ) = n + 1 := by
        have hle : (i : ℕ) ≤ n + 1 := mem_Iic.mp i.2
        omega
      have hieq : i = lastHistoryIndex (n + 1) := Subtype.ext hin
      rw [hieq]
      simpa [appendHistory, lastHistoryIndex, IicProdIoc_def,
        MeasurableEquiv.piSingleton] using hy

/-- On a surviving appended prefix, the survival potential is the potential of
the newly appended state. -/
theorem historySurvivalPotential_append_eq_of_survive
    (A : Set X) (V : X → ℝ≥0∞) (n : ℕ)
    (h : (i : Iic n) → X) (y : X)
    (hh : h ∈ historySurvivalSet A n) (hy : y ∉ A) :
    historySurvivalPotential A V (n + 1) (appendHistory n (h, y)) = V y := by
  have hs : appendHistory n (h, y) ∈ historySurvivalSet A (n + 1) :=
    (appendHistory_mem_historySurvivalSet_iff A n h y).2 ⟨hh, hy⟩
  rw [historySurvivalPotential, Set.indicator_of_mem hs]
  simp [appendHistory, lastHistoryIndex, IicProdIoc_def,
    MeasurableEquiv.piSingleton]

/-- Once a prefix has already hit the target, every one-step extension has zero
survival potential. -/
theorem historySurvivalPotential_append_eq_zero_of_not_survive
    (A : Set X) (V : X → ℝ≥0∞) (n : ℕ)
    (h : (i : Iic n) → X) (y : X)
    (hh : h ∉ historySurvivalSet A n) :
    historySurvivalPotential A V (n + 1) (appendHistory n (h, y)) = 0 := by
  have hs : appendHistory n (h, y) ∉ historySurvivalSet A (n + 1) := by
    intro hs
    exact hh ((appendHistory_mem_historySurvivalSet_iff A n h y).1 hs).1
  simp [historySurvivalPotential, hs]

/-- The survival potential of an appended history never exceeds the raw
potential of the appended state. -/
theorem historySurvivalPotential_append_le
    (A : Set X) (V : X → ℝ≥0∞) (n : ℕ)
    (h : (i : Iic n) → X) (y : X) :
    historySurvivalPotential A V (n + 1) (appendHistory n (h, y)) ≤ V y := by
  by_cases hs : appendHistory n (h, y) ∈ historySurvivalSet A (n + 1)
  · have hpair := (appendHistory_mem_historySurvivalSet_iff A n h y).1 hs
    rw [historySurvivalPotential_append_eq_of_survive A V n h y hpair.1 hpair.2]
  · simp [historySurvivalPotential, hs]

/-- Expected surviving Lyapunov potential at time `n`. -/
noncomputable def survivalPotentialMean
    (P : Kernel X X) [IsMarkovKernel P]
    (x : X) (A : Set X) (V : X → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ h, historySurvivalPotential A V n h ∂prefixLaw P x n

/-- Pointwise stopped-drift inequality on a finite history.  If the history has
already hit `A`, all three terms vanish.  Otherwise the source kernel drift at
the last state controls the next surviving potential plus the recovery charge
`c`. -/
theorem oneStep_survival_drift
    (P : Kernel X X) [IsMarkovKernel P]
    (A : Set X) (V : X → ℝ≥0∞) (c : ℝ≥0∞)
    (hdrift : ∀ z, z ∉ A → (∫⁻ y, V y ∂P z) + c ≤ V z)
    (n : ℕ) (h : (i : Iic n) → X) :
    (∫⁻ y,
        historySurvivalPotential A V (n + 1) (appendHistory n (h, y))
        ∂homHistoryKernel P n h) +
      (historySurvivalSet A n).indicator (fun _ => c) h ≤
        historySurvivalPotential A V n h := by
  change
    (∫⁻ y,
        historySurvivalPotential A V (n + 1) (appendHistory n (h, y))
        ∂P (h (lastHistoryIndex n))) +
      (historySurvivalSet A n).indicator (fun _ => c) h ≤
        historySurvivalPotential A V n h
  by_cases hh : h ∈ historySurvivalSet A n
  · have hlast : h (lastHistoryIndex n) ∉ A :=
      (mem_historySurvivalSet_iff A n h).1 hh (lastHistoryIndex n)
    have hinner :
        (∫⁻ y,
          historySurvivalPotential A V (n + 1) (appendHistory n (h, y))
          ∂P (h (lastHistoryIndex n))) ≤
        ∫⁻ y, V y ∂P (h (lastHistoryIndex n)) :=
      lintegral_mono fun y => historySurvivalPotential_append_le A V n h y
    have hsum :
        (∫⁻ y,
          historySurvivalPotential A V (n + 1) (appendHistory n (h, y))
          ∂P (h (lastHistoryIndex n))) + c ≤
        (∫⁻ y, V y ∂P (h (lastHistoryIndex n))) + c :=
      add_le_add hinner (le_refl c)
    have hsource := hdrift (h (lastHistoryIndex n)) hlast
    simpa [historySurvivalPotential, hh] using hsum.trans hsource
  · have hzero : ∀ y,
        historySurvivalPotential A V (n + 1) (appendHistory n (h, y)) = 0 :=
      fun y => historySurvivalPotential_append_eq_zero_of_not_survive A V n h y hh
    simp_rw [hzero]
    simp [historySurvivalPotential, hh]

/-- The prefix law at `n+1` can be integrated by first integrating the newly
sampled state against the homogeneous history kernel and then the old prefix. -/
theorem survivalPotentialMean_succ_fubini
    (P : Kernel X X) [IsMarkovKernel P]
    (x : X) (A : Set X) (V : X → ℝ≥0∞)
    (hA : MeasurableSet A) (hV : Measurable V) (n : ℕ) :
    survivalPotentialMean P x A V (n + 1) =
      ∫⁻ h,
        (∫⁻ y,
          historySurvivalPotential A V (n + 1) (appendHistory n (h, y))
          ∂homHistoryKernel P n h)
        ∂prefixLaw P x n := by
  letI : IsProbabilityMeasure (Measure.dirac x) := by infer_instance
  letI : IsMarkovKernel (homHistoryKernel P n) :=
    isMarkovKernel_homHistoryKernel P n
  have hstep :
      (((prefixLaw P x n) ⊗ₘ homHistoryKernel P n).map (appendHistory n)) =
        prefixLaw P x (n + 1) := by
    simpa [prefixLaw] using
      (homTrajMeasure_prefix_succ (Measure.dirac x) P n)
  have hpot :
      Measurable (historySurvivalPotential A V (n + 1)) :=
    measurable_historySurvivalPotential hA hV (n + 1)
  have happ : Measurable (appendHistory (X := X) n) :=
    measurable_appendHistory n
  calc
    survivalPotentialMean P x A V (n + 1) =
        ∫⁻ z, historySurvivalPotential A V (n + 1) z
          ∂prefixLaw P x (n + 1) := rfl
    _ = ∫⁻ z, historySurvivalPotential A V (n + 1) z
          ∂(((prefixLaw P x n) ⊗ₘ homHistoryKernel P n).map (appendHistory n)) := by
      rw [hstep]
    _ = ∫⁻ p,
          historySurvivalPotential A V (n + 1) (appendHistory n p)
          ∂((prefixLaw P x n) ⊗ₘ homHistoryKernel P n) := by
      rw [lintegral_map hpot happ]
    _ = ∫⁻ h,
          (∫⁻ y,
            historySurvivalPotential A V (n + 1) (appendHistory n (h, y))
            ∂homHistoryKernel P n h)
          ∂prefixLaw P x n := by
      rw [Measure.lintegral_compProd]
      exact hpot.comp happ

/-- Integrated source drift.  This is the exact finite-time recurrence that
will telescope to the truncated hitting-time bound. -/
theorem survivalPotentialMean_succ_add_survival_le
    (P : Kernel X X) [IsMarkovKernel P]
    (x : X) (A : Set X) (V : X → ℝ≥0∞) (c : ℝ≥0∞)
    (hA : MeasurableSet A) (hV : Measurable V)
    (hdrift : ∀ z, z ∉ A → (∫⁻ y, V y ∂P z) + c ≤ V z)
    (n : ℕ) :
    survivalPotentialMean P x A V (n + 1) +
        c * survivalProb P x A n ≤
      survivalPotentialMean P x A V n := by
  letI : IsMarkovKernel (homHistoryKernel P n) :=
    isMarkovKernel_homHistoryKernel P n
  have hfub := survivalPotentialMean_succ_fubini P x A V hA hV n
  rw [hfub]
  have hpair : Measurable
      (fun p : ((i : Iic n) → X) × X =>
        historySurvivalPotential A V (n + 1) (appendHistory n p)) :=
    (measurable_historySurvivalPotential hA hV (n + 1)).comp
      (measurable_appendHistory n)
  have hinner : Measurable
      (fun h : (i : Iic n) → X =>
        ∫⁻ y,
          historySurvivalPotential A V (n + 1) (appendHistory n (h, y))
          ∂homHistoryKernel P n h) :=
    hpair.lintegral_kernel_prod_right'
  have hcharge :
      (∫⁻ h,
        (historySurvivalSet A n).indicator (fun _ => c) h
        ∂prefixLaw P x n) = c * survivalProb P x A n := by
    rw [lintegral_indicator_const (measurableSet_historySurvivalSet hA n) c]
    rfl
  rw [← hcharge]
  rw [← lintegral_add_left hinner]
  exact lintegral_mono fun h => oneStep_survival_drift P A V c hdrift n h

end UEOT.V3.RecoveryHittingDrift
