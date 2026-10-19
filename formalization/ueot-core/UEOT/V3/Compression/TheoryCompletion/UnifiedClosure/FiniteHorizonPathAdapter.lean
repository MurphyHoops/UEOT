import UEOT.V3.PathError

/-!
# Finite-horizon completion of the source path-error theorem

The frozen P-DYN-03 endpoint asks for one-step hypotheses at every natural
time. This adapter uses hypotheses only before the declared horizon. After
that horizon it completes the actual rows by the reference rows, with zero
error, and proves that this completion leaves the required path law intact.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open MeasureTheory UEOT.V3.PathError UEOT.V3.TotalVariation
open scoped BigOperators

universe u

/-- A finite causal law depends only on rows strictly before its horizon. -/
theorem causalLaw_congr_before
    {H₀ Z : Type u}
    (p₀ : PMF H₀)
    (K L : ∀ n, CausalHistory H₀ Z n → PMF Z)
    (T : ℕ)
    (hKL : ∀ n, n < T → ∀ h, K n h = L n h) :
    causalLaw p₀ K T = causalLaw p₀ L T := by
  have h : ∀ n, n ≤ T → causalLaw p₀ K n = causalLaw p₀ L n := by
    intro n
    induction n with
    | zero =>
        intro _
        rfl
    | succ n ih =>
        intro hn
        have hnT : n < T := Nat.lt_of_succ_le hn
        have hrows : K n = L n := funext (hKL n hnT)
        change pmfExtend (causalLaw p₀ K n) (K n) =
          pmfExtend (causalLaw p₀ L n) (L n)
        rw [ih (Nat.le_of_lt hnT), hrows]
  exact h T le_rfl

/-- The sharp source product bound under genuinely finite row hypotheses.
No tail control, independence of steps, or asymptotic safety is assumed. -/
theorem finite_horizon_path_error
    {H₀ Z : Type u}
    [Fintype H₀] [Fintype Z]
    [MeasurableSpace H₀] [MeasurableSingletonClass H₀]
    [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (p₀ : PMF H₀)
    (K L : ∀ n, CausalHistory H₀ Z n → PMF Z)
    (ε : ℕ → ℝ) (T : ℕ)
    (hε0 : ∀ n, n < T → 0 ≤ ε n)
    (hε1 : ∀ n, n < T → ε n ≤ 1)
    (hTV : ∀ n, n < T → ∀ h,
      tvDist (K n h).toMeasure (L n h).toMeasure ≤ ε n) :
    tvDist (causalLaw p₀ K T).toMeasure (causalLaw p₀ L T).toMeasure
        ≤ 1 - (∏ i ∈ Finset.range T, (1 - ε i)) ∧
      1 - (∏ i ∈ Finset.range T, (1 - ε i))
        ≤ ∑ i ∈ Finset.range T, ε i := by
  let completed : ∀ n, CausalHistory H₀ Z n → PMF Z :=
    fun n h => if n < T then K n h else L n h
  let budget : ℕ → ℝ := fun n => if n < T then ε n else 0
  have h0 : ∀ n, 0 ≤ budget n := by
    intro n
    dsimp [budget]
    split_ifs with hn
    · exact hε0 n hn
    · exact le_rfl
  have h1 : ∀ n, budget n ≤ 1 := by
    intro n
    dsimp [budget]
    split_ifs with hn
    · exact hε1 n hn
    · exact zero_le_one
  have hrows : ∀ n h,
      tvDist (completed n h).toMeasure (L n h).toMeasure ≤ budget n := by
    intro n h
    by_cases hn : n < T
    · simpa [completed, budget, hn] using hTV n hn h
    · simp [completed, budget, hn, tvDist_self_eq_zero]
  have hlaw : causalLaw p₀ completed T = causalLaw p₀ K T := by
    apply causalLaw_congr_before
    intro n hn h
    simp [completed, hn]
  have hprod : (∏ i ∈ Finset.range T, (1 - budget i)) =
      ∏ i ∈ Finset.range T, (1 - ε i) := by
    apply Finset.prod_congr rfl
    intro i hi
    simp [budget, Finset.mem_range.mp hi]
  have hsum : (∑ i ∈ Finset.range T, budget i) =
      ∑ i ∈ Finset.range T, ε i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [budget, Finset.mem_range.mp hi]
  have source := p_dyn_03_finite_path_error p₀ completed L budget h0 h1 hrows T
  rw [hlaw, hprod, hsum] at source
  exact source

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
