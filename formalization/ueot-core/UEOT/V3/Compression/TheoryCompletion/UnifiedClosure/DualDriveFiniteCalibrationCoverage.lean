import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DualDriveFiniteNoisyCalibration

/-!
Original commitment: finite measured calibration should support a useful actual decision, not only rare-error control with arbitrary rejection.
Existing result: same data-only selector and complete fixed-row source give Good=>selected-correct and joint error<=8 exp(-N/8).
Premise reduced: derive actual acceptance on original Good under explicit source gain/gap separation, with NO new selector inputs.
Model/witness: SAME unknown positive rational diagonal gains >=1, action latent gap >=1/2, SAME four iid rows/noise/threshold/budget; either action may be best.
Consumer: SAME returned action has correct-acceptance probability >=1-8 exp(-N/8); original registered two worlds consume the same theorem.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DualDriveFiniteCalibrationCoverage
open MeasureTheory ProbabilityTheory
open DualDriveFiniteNoisyCalibration
noncomputable section

private theorem selector_accepts_gap {N : ℕ} (data : Data N) (hN : 0 < N)
    (h0 : mean data 0 ≠ 0) (h1 : mean data 1 ≠ 0) (best : Bool)
    (hg : (3/10 : ℚ)*conditioning data < estimate data best-estimate data (!best)) :
    select data=some best := by
  have hn : N ≠ 0 := Nat.ne_of_gt hN
  cases best
  · have ht : ¬ (3/10 : ℚ)*conditioning data < estimate data true-estimate data false := by
      have hk := conditioning_nonneg data
      simp only [Bool.not_false] at hg
      linarith
    simp only [Bool.not_false] at hg
    simp [select,hn,h0,h1,ht,hg]
  · simp only [Bool.not_true] at hg
    simp [select,hn,h0,h1,hg]

/-- SAME source Good forces acceptance, without teaching its unknown gains
or true best action to the executable selector. -/
theorem good_selects_separated {N : ℕ} (p : Parameters) (omega : Raw N)
    (hN : 0 < N) (hg : omega ∈ Good N) (hgain : ∀ i, 1 ≤ p.gain i)
    (best : Bool) (hgap : (1/2 : ℚ) ≤ p.latent best-p.latent (!best)) :
    select (sourceData p omega)=some best := by
  let data := sourceData p omega
  have he (j : Row) : |mean data j-trueMean p j| ≤ (1/20 : ℚ) := by
    change |mean (sourceData p omega) j-trueMean p j| ≤ (1/20 : ℚ)
    apply (Rat.cast_le (K := ℝ)).mp
    push_cast
    exact good_mean_errors p omega hN hg j
  have he0 : |mean data 0-p.gain 0| ≤ (1/20 : ℚ) := by simpa [trueMean] using he 0
  have he1 : |mean data 1-p.gain 1| ≤ (1/20 : ℚ) := by simpa [trueMean] using he 1
  have hm0 : (19/20 : ℚ) ≤ mean data 0 := by
    have := (abs_le.mp he0).1
    linarith [hgain 0]
  have hm1 : (19/20 : ℚ) ≤ mean data 1 := by
    have := (abs_le.mp he1).1
    linarith [hgain 1]
  have hp0 : 0 < mean data 0 := by linarith
  have hp1 : 0 < mean data 1 := by linarith
  have hi0 : |(mean data 0)⁻¹| ≤ (20/19 : ℚ) := by
    rw [abs_of_pos (inv_pos.mpr hp0)]
    have hh := one_div_le_one_div_of_le (show (0 : ℚ) < 19/20 by norm_num) hm0
    norm_num [one_div] at hh
    exact hh
  have hi1 : |(mean data 1)⁻¹| ≤ (20/19 : ℚ) := by
    rw [abs_of_pos (inv_pos.mpr hp1)]
    have hh := one_div_le_one_div_of_le (show (0 : ℚ) < 19/20 by norm_num) hm1
    norm_num [one_div] at hh
    exact hh
  have hk : conditioning data ≤ (20/19 : ℚ) := max_le hi0 hi1
  have hbu : mean data (if best then 3 else 2)-p.gain 1*p.latent best ≤ (1/20 : ℚ) ∧
      -(1/20 : ℚ) ≤ mean data (if best then 3 else 2)-p.gain 1*p.latent best := by
    have hx : |mean data (if best then 3 else 2)-p.gain 1*p.latent best| ≤ (1/20 : ℚ) := by
      cases best
      · simpa [trueMean] using he 2
      · simpa [trueMean] using he 3
    exact ⟨(abs_le.mp hx).2,(abs_le.mp hx).1⟩
  have hlu : mean data (if !best then 3 else 2)-p.gain 1*p.latent (!best) ≤ (1/20 : ℚ) ∧
      -(1/20 : ℚ) ≤ mean data (if !best then 3 else 2)-p.gain 1*p.latent (!best) := by
    have hx : |mean data (if !best then 3 else 2)-p.gain 1*p.latent (!best)| ≤ (1/20 : ℚ) := by
      cases best
      · simpa [trueMean] using he 3
      · simpa [trueMean] using he 2
    exact ⟨(abs_le.mp hx).2,(abs_le.mp hx).1⟩
  have hsourcegap : (p.gain 1)/2 ≤ p.gain 1*p.latent best-p.gain 1*p.latent (!best) := by
    have := mul_le_mul_of_nonneg_left hgap (show 0 ≤ p.gain 1 by linarith [hgain 1])
    nlinarith
  have hden : mean data 1 ≤ p.gain 1+1/20 := by
    have := (abs_le.mp he1).2
    linarith
  have hmul := mul_le_mul_of_nonneg_right hk hp1.le
  have hobs : (3/10 : ℚ)*conditioning data*mean data 1 <
      mean data (if best then 3 else 2)-mean data (if !best then 3 else 2) := by
    nlinarith [hgain 1]
  apply selector_accepts_gap data hN (ne_of_gt hp0) (ne_of_gt hp1) best
  rw [estimate,estimate,← sub_div]
  exact (lt_div_iff₀ hp1).mpr hobs

/-- SAME actual accepted artifact enters the EXISTING source-calibrated
original action-gap consumer, not a new truth-reading decision rule. -/
theorem good_correct_accepts {N : ℕ} (p : Parameters) (hp : Valid p) (omega : Raw N)
    (hN : 0 < N) (hg : omega ∈ Good N) (hgain : ∀ i, 1 ≤ p.gain i)
    (best : Bool) (hgap : (1/2 : ℚ) ≤ p.latent best-p.latent (!best)) :
    select (sourceData p omega)=some best ∧
      ∀ a : Bool, a ≠ best → p.latent a < p.latent best := by
  have hs := good_selects_separated p omega hN hg hgain best hgap
  exact ⟨hs,good_selected_action_correct p hp omega hN hg best hs⟩

/-- Rejections and wrong outputs are ALL retained in the original complete
source. Under explicit separation they are confined to the original bad set. -/
theorem not_best_probability_le (p : Parameters) (N : ℕ) (hN : 0 < N)
    (hgain : ∀ i, 1 ≤ p.gain i) (best : Bool)
    (hgap : (1/2 : ℚ) ≤ p.latent best-p.latent (!best)) :
    (rawLaw N).real {omega | select (sourceData p omega) ≠ some best} ≤
      8*Real.exp (-(N : ℝ)/8) := by
  apply (measureReal_mono ?_).trans (bad_good_probability_le N hN)
  intro omega hfail hg
  exact hfail (good_selects_separated p omega hN hg hgain best hgap)

/-- Useful correct acceptance on the SAME source, not merely joint safety
with possibly universal rejection. No conditional-on-acceptance bound. -/
theorem best_accept_probability_ge (p : Parameters) (N : ℕ) (hN : 0 < N)
    (hgain : ∀ i, 1 ≤ p.gain i) (best : Bool)
    (hgap : (1/2 : ℚ) ≤ p.latent best-p.latent (!best)) :
    1-8*Real.exp (-(N : ℝ)/8) ≤
      (rawLaw N).real {omega | select (sourceData p omega)=some best} := by
  have hb := not_best_probability_le p N hN hgain best hgap
  have hm : MeasurableSet {omega : Raw N | select (sourceData p omega)=some best} :=
    (Set.toFinite _).measurableSet
  have hc := measureReal_compl (μ := rawLaw N) hm
  simp only [probReal_univ] at hc
  change (rawLaw N).real ({omega | select (sourceData p omega)=some best}ᶜ) ≤ _ at hb
  rw [hc] at hb
  linarith

/-- BOTH original registered worlds have strictly positive correct
acceptance mass. No new word, batch, threshold or budget. -/
theorem registered_both_worlds_useful :
    0 < (rawLaw registeredBudget).real {omega | select (sourceData regularParameters omega)=some true} ∧
    0 < (rawLaw registeredBudget).real {omega | select (sourceData reverseParameters omega)=some false} := by
  have hp : (0 : ℝ) < 1-8*Real.exp (-4) := by linarith [registered_bound_nonvacuous]
  constructor
  · have h := best_accept_probability_ge regularParameters registeredBudget (by decide)
      (by intro i; norm_num [regularParameters]) true (by norm_num [regularParameters])
    norm_num [registeredBudget] at h
    linarith
  · have h := best_accept_probability_ge reverseParameters registeredBudget (by decide)
      (by intro i; norm_num [reverseParameters]) false (by norm_num [reverseParameters])
    norm_num [registeredBudget] at h
    linarith

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DualDriveFiniteCalibrationCoverage
