import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DualDrivePersistentReadCounterexample

/-!
Original commitment: actual accepted allowed actions need source-bound true rankings, including correlated-read boundaries.
Existing result: original select has iid/Good guarantees and an actual persistent-shock error; those old facts remain unchanged.
Premise reduced: NEW data-only orientation wrapper derives acceptance soundness pathwise, without IID/Good/law assumptions.
Model: SAME four rows, unknown positive gains, Bool actions, exact sensor ±1/10 and original3/10*kappa threshold; rejection/coverage separate.
Consumer: actual returned action, arbitrary actual adaptive decoder/router and persistent fragile source; no inverse accuracy/generalGL claim.

Preregistered BEFORE new-wrapper evaluation in
/tmp/ueot-positive-orientation-registration-20261030.json.
The original selector, data, thresholds and registered words are unchanged.
Only the accepted action is flipped when the observed row1 mean is negative.
No true parameter/order/Good/raw sign/law is a selector or router input.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DualDrivePositiveOrientationCalibration
open MeasureTheory ProbabilityTheory
open DualDriveFiniteNoisyCalibration DualDriveFiniteCalibrationCoverage
open DualDriveAdaptiveReadCalibration DualDrivePersistentReadCounterexample
open scoped BigOperators ENNReal

/-- Exact executable wrapper over the SAME old selector and observed data. -/
def orient {N : ℕ} (data : Data N) : Option Bool :=
  (select data).map (fun a => if mean data 1<0 then !a else a)

def returned (m K : ℕ) (route : Router) (data : Data (m+K)) : Option Bool :=
  orient (decoded (run m K route data))

def queryRow (a : Bool) : Row := if a then 3 else 2

noncomputable section

/-- An average of bounded actual sensor errors remains bounded for EVERY
raw word. There is no independence or unbiased-empirical-mean premise. -/
private theorem mean_error_of_bounded {N : ℕ} (data : Data N) (j : Row) (M δ : ℚ) (hN : 0<N)
    (hb : ∀ k : Fin N, |data ⟨j,k⟩-M|≤δ) : |mean data j-M|≤δ := by
  have hq : (0 : ℚ)<N := by exact_mod_cast hN
  have he : mean data j-M=(∑ k : Fin N, (data ⟨j,k⟩-M))/(N : ℚ) := by
    simp only [mean,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  have hs : |∑ k : Fin N, (data ⟨j,k⟩-M)|≤(N : ℚ)*δ := by
    calc
      _ ≤ ∑ k : Fin N, |data ⟨j,k⟩-M| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin N, δ := Finset.sum_le_sum (fun k _ => hb k)
      _ = _ := by simp
  rw [he,abs_div,abs_of_pos hq]
  exact (div_le_iff₀ hq).mpr (by simpa only [mul_comm] using hs)

theorem any_raw_mean_error {N : ℕ} (p : Parameters) (omega : Raw N) (hN : 0<N) (j : Row) :
    |(mean (sourceData p omega) j : ℝ)-(trueMean p j : ℝ)|≤(1/10 : ℝ) := by
  have h : |mean (sourceData p omega) j-trueMean p j|≤(1/10 : ℚ) :=
    mean_error_of_bounded _ j _ _ hN (fun k => (sensor_noise_size p j (omega ⟨j,k⟩)).le)
  have hh := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at hh
  exact hh

private theorem conditioning_anchor {N : ℕ} (data : Data N) (h1 : mean data 1≠0) :
    (1 : ℚ)≤conditioning data*|mean data 1| := by
  have h := mul_le_mul_of_nonneg_right (le_max_right |(mean data 0)⁻¹| |(mean data 1)⁻¹|) (abs_nonneg (mean data 1))
  change |(mean data 1)⁻¹| * |mean data 1|≤conditioning data*|mean data 1| at h
  simpa only [← abs_mul,inv_mul_cancel₀ h1,abs_one] using h

/-- The NEW accepted artifact has a literal PHYSICAL query gap>3/10.
The sign correction is computed solely from the same observed anchor. -/
theorem orient_spec {N : ℕ} (data : Data N) (chosen : Bool) (hs : orient data=some chosen) :
    N≠0 ∧ (3/10 : ℚ)< mean data (queryRow chosen)-mean data (queryRow (!chosen)) := by
  obtain ⟨a,ha,hout⟩ := Option.map_eq_some_iff.mp hs
  have h := select_spec data a ha
  have hk := conditioning_anchor data h.2.2.1
  have hg := h.2.2.2
  rw [estimate,estimate,← sub_div] at hg
  by_cases hn : mean data 1<0
  · simp only [if_pos hn] at hout
    subst chosen
    have hh := (lt_div_iff_of_neg hn).mp hg
    have hb : (1 : ℚ)≤conditioning data*(-mean data 1) := by simpa only [abs_of_neg hn] using hk
    refine ⟨h.1,?_⟩
    simp only [Bool.not_not,queryRow]
    nlinarith
  · simp only [if_neg hn] at hout
    subst chosen
    have hp : 0< mean data 1 := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm h.2.2.1)
    have hh := (lt_div_iff₀ hp).mp hg
    have hb : (1 : ℚ)≤conditioning data*mean data 1 := by simpa only [abs_of_pos hp] using hk
    refine ⟨h.1,?_⟩
    change (3/10 : ℚ)< mean data (if a then 3 else 2)-mean data (if !a then 3 else 2)
    nlinarith

private theorem query_truth (p : Parameters) (a : Bool) : trueMean p (queryRow a)=p.gain 1*p.latent a := by
  cases a <;> norm_num [trueMean,queryRow,Fin.ext_iff]

/-- Original Decision.action_gap consumes SAME raw physical query means and
actual returned action. Deterministic error1/10, not an IID Good event. -/
theorem accepted_oriented_correct {N : ℕ} (p : Parameters) (hp : Valid p) (omega : Raw N)
    (chosen : Bool) (hs : orient (sourceData p omega)=some chosen) :
    ∀ a : Bool, a≠chosen → p.latent a<p.latent chosen := by
  have hspec := orient_spec (sourceData p omega) chosen hs
  have hN : 0<N := Nat.pos_of_ne_zero hspec.1
  have herr (a : Bool) : |((p.gain 1*p.latent a : ℚ) : ℝ)-(mean (sourceData p omega) (queryRow a) : ℝ)|≤(1/10 : ℝ) := by
    have h := any_raw_mean_error p omega hN (queryRow a)
    rw [query_truth] at h
    rwa [abs_sub_comm] at h
  have hgap (a : Bool) (ha : a≠chosen) :
      2*(1/10 : ℝ)<(mean (sourceData p omega) (queryRow chosen) : ℝ)-(mean (sourceData p omega) (queryRow a) : ℝ) := by
    have he : a= !chosen := by cases a <;> cases chosen <;> simp_all
    subst a
    have hr : (3/10 : ℝ)<(mean (sourceData p omega) (queryRow chosen) : ℝ)-(mean (sourceData p omega) (queryRow (!chosen)) : ℝ) := by
      have hc := (Rat.cast_lt (K := ℝ)).mpr hspec.2
      push_cast at hc
      exact hc
    linarith
  have h := UEOT.V3.Decision.action_gap (fun a => ((p.gain 1*p.latent a : ℚ) : ℝ))
    (fun a => (mean (sourceData p omega) (queryRow a) : ℝ)) (1/10) chosen herr hgap
  intro a ha
  have hh := h a ha
  push_cast at hh
  have hpos : (0 : ℝ)<p.gain 1 := by exact_mod_cast hp.1 1
  have hd : (p.latent a : ℝ)<p.latent chosen := by
    by_contra hn
    have hm := mul_le_mul_of_nonneg_left (le_of_not_gt hn) hpos.le
    exact (not_lt_of_ge hm) hh
  exact_mod_cast hd

/-- NEW-policy joint error; original AcceptWrong/ActualWrong remain unchanged. -/
def Wrong {N : ℕ} (p : Parameters) (data : Data N) : Prop :=
  ∃ chosen, orient data=some chosen ∧ ¬ ∀ a : Bool, a≠chosen → p.latent a<p.latent chosen

/-- Arbitrary time/row-correlated raw laws are permitted: the NEW joint error
set is actually empty, including rejected outcomes in the complete source. -/
theorem any_law_joint_error_zero {N : ℕ} (p : Parameters) (hp : Valid p) (mu : Measure (Raw N)) :
    mu {omega | Wrong p (sourceData p omega)}=0 := by
  have he : {omega : Raw N | Wrong p (sourceData p omega)}=∅ := by
    ext omega
    simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false,Wrong]
    rintro ⟨a,ha,hbad⟩
    exact hbad (accepted_oriented_correct p hp omega a ha)
  rw [he,measure_empty]

/-- ACTUAL data-selected decoder length and cache are reused, not an assumed
unbiased/fixed-count decoder field. This holds for EVERY actual Router. -/
theorem accepted_returned_correct (m K : ℕ) (route : Router) (p : Parameters) (hp : Valid p)
    (omega : Raw (m+K)) (chosen : Bool) (hs : returned m K route (sourceData p omega)=some chosen) :
    ∀ a : Bool, a≠chosen → p.latent a<p.latent chosen := by
  have hb := run_minCount_bounds m K route (sourceData p omega)
  have hsel : orient (sourceData p (prefixRaw hb.2 omega))=some chosen := by
    rw [← decoded_source_prefix m K route p omega]
    exact hs
  exact accepted_oriented_correct p hp _ chosen hsel

def ReturnedWrong (m K : ℕ) (route : Router) (p : Parameters) (omega : Raw (m+K)) : Prop :=
  ∃ chosen, returned m K route (sourceData p omega)=some chosen ∧
    ¬ ∀ a : Bool, a≠chosen → p.latent a<p.latent chosen

theorem any_route_law_joint_error_zero (m K : ℕ) (route : Router) (p : Parameters) (hp : Valid p)
    (mu : Measure (Raw (m+K))) : mu {omega | ReturnedWrong m K route p omega}=0 := by
  have he : {omega : Raw (m+K) | ReturnedWrong m K route p omega}=∅ := by
    ext omega
    simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false,ReturnedWrong]
    rintro ⟨a,ha,hbad⟩
    exact hbad (accepted_returned_correct m K route p hp omega a ha)
  rw [he,measure_empty]

/-- Coverage keeps its OWN explicit source assumptions. Positive observed
anchor means NEW wrapper equals old select, with the old threshold untouched. -/
theorem orient_of_anchor_nonneg {N : ℕ} (data : Data N) (h : 0≤ mean data 1) : orient data=select data := by
  simp only [orient,if_neg (not_lt.mpr h)]
  cases select data <;> rfl

private theorem good_anchor_nonneg {N : ℕ} (p : Parameters) (omega : Raw N) (hN : 0<N)
    (hg : omega∈Good N) (hgain : (1 : ℚ)≤p.gain 1) : 0≤ mean (sourceData p omega) 1 := by
  have he := good_mean_errors p omega hN hg 1
  have ht : trueMean p 1=p.gain 1 := by norm_num [trueMean,Fin.ext_iff]
  rw [ht] at he
  have hr : (1 : ℝ)≤p.gain 1 := by
    have hc := (Rat.cast_le (K:=ℝ)).mpr hgain
    norm_num only [Rat.cast_one] at hc
    exact hc
  have hm : (0 : ℝ)≤ mean (sourceData p omega) 1 := by linarith [(abs_le.mp he).1]
  apply (Rat.cast_le (K:=ℝ)).mp
  simpa only [Rat.cast_zero] using hm

theorem good_oriented_acceptance {N : ℕ} (p : Parameters) (omega : Raw N) (hN : 0<N)
    (hg : omega∈Good N) (hgain : ∀ i, (1 : ℚ)≤p.gain i) (best : Bool)
    (hgap : (1/2 : ℚ)≤p.latent best-p.latent (!best)) : orient (sourceData p omega)=some best := by
  rw [orient_of_anchor_nonneg _ (good_anchor_nonneg p omega hN hg (hgain 1))]
  exact good_selects_separated p omega hN hg hgain best hgap

/-- IID enters ONLY this useful acceptance statement. Pathwise safety above
never uses it. No all-Valid acceptance or general correlated coverage claimed. -/
theorem iid_not_best_probability_le (p : Parameters) (N : ℕ) (hN : 0<N)
    (hgain : ∀ i, (1 : ℚ)≤p.gain i) (best : Bool) (hgap : (1/2 : ℚ)≤p.latent best-p.latent (!best)) :
    (rawLaw N).real {omega | orient (sourceData p omega)≠some best}≤8*Real.exp (-(N : ℝ)/8) := by
  apply (measureReal_mono ?_).trans (bad_good_probability_le N hN)
  intro omega hfail hg
  exact hfail (good_oriented_acceptance p omega hN hg hgain best hgap)

/-- Actual old fragile shock now returns TRUE, for every positive count;
repeat_selects_wrong remains the old-policy theorem with its original meaning. -/
theorem repeat_oriented_true (N : ℕ) (hN : 0<N) :
    orient (sourceData fragileParameters (repeatRaw (N:=N) shockWord))=some true := by
  have hn : mean (sourceData fragileParameters (repeatRaw (N:=N) shockWord)) 1<0 := by
    rw [mean_repeat N hN]
    norm_num [sensor,trueMean,fragileParameters,shockWord,bit,Fin.ext_iff]
  simp only [orient,repeat_selects_wrong N hN,Option.map_some,if_pos hn,Bool.not_false]

theorem adaptive_repeat_oriented_true (m K : ℕ) (hm : 0 < m) (route : Router) :
    returned m K route (sourceData fragileParameters (repeatRaw (N:=m+K) shockWord))=some true := by
  have hb := run_minCount_bounds m K route (sourceData fragileParameters (repeatRaw (N:=m+K) shockWord))
  unfold returned
  rw [decoded_source_prefix,repeat_prefix]
  exact repeat_oriented_true _ (hm.trans_le hb.1)

/-- THIS correlated source has a useful NEW actual correct output, while its
old wrong-output lower bound remains untouched. No all-correlated success. -/
theorem persistent_new_correct_acceptance_ge (m K : ℕ) (hm : 0 < m) (route : Router) :
    (1/16 : ℝ)≤(rawLaw 1).real {z | returned m K route (sourceData fragileParameters (repeatRaw (N:=m+K) z))=some true} := by
  rw [← shock_mass]
  apply measureReal_mono (h₂ := by finiteness)
  intro z hz
  have he : z=shockWord := Set.mem_singleton_iff.mp hz
  subst z
  exact adaptive_repeat_oriented_true m K hm route

/-- A separate explicit high-signal source consumer: in the ORIGINAL regular
world, EVERY raw word accepts true. This is not all-Valid coverage. -/
theorem regular_any_raw_output {N : ℕ} (omega : Raw N) (hN : 0<N) :
    orient (sourceData regularParameters omega)=some true := by
  let data := sourceData regularParameters omega
  have he (j : Row) : |mean data j-trueMean regularParameters j|≤(1/10 : ℚ) :=
    mean_error_of_bounded _ j _ _ hN (fun k => (sensor_noise_size regularParameters j (omega ⟨j,k⟩)).le)
  have h0 : |mean data 0-2|≤(1/10 : ℚ) := by simpa [trueMean,regularParameters,Fin.ext_iff] using he 0
  have h1 : |mean data 1-2|≤(1/10 : ℚ) := by simpa [trueMean,regularParameters,Fin.ext_iff] using he 1
  have h2 : |mean data 2|≤(1/10 : ℚ) := by simpa [trueMean,regularParameters,Fin.ext_iff] using he 2
  have h3 : |mean data 3-2|≤(1/10 : ℚ) := by simpa [trueMean,regularParameters,Fin.ext_iff] using he 3
  have hm0 : (1 : ℚ)≤ mean data 0 := by linarith [(abs_le.mp h0).1]
  have hm1 : (1 : ℚ)≤ mean data 1 := by linarith [(abs_le.mp h1).1]
  have hp0 : 0 < mean data 0 := by linarith
  have hp1 : 0 < mean data 1 := by linarith
  have hi (x : ℚ) (hx : 1≤x) : |x⁻¹|≤1 := by
    have hp : 0<x := by linarith
    rw [abs_of_pos (inv_pos.mpr hp)]
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℚ)<1) hx
    simpa only [one_div,inv_one] using hh
  have hk : conditioning data≤1 := max_le (hi _ hm0) (hi _ hm1)
  have hmul := mul_le_mul_of_nonneg_right hk hp1.le
  have hphysical : (3/10 : ℚ)*conditioning data*mean data 1< mean data 3-mean data 2 := by
    nlinarith [(abs_le.mp h1).2,(abs_le.mp h2).2,(abs_le.mp h3).1]
  have hgap : (3/10 : ℚ)*conditioning data<estimate data true-estimate data false := by
    rw [estimate,estimate,← sub_div]
    exact (lt_div_iff₀ hp1).mpr hphysical
  have hs : select data=some true := by
    simp [select,Nat.ne_of_gt hN,ne_of_gt hp0,ne_of_gt hp1,hgap]
  rw [orient_of_anchor_nonneg _ hp1.le]
  exact hs

/-- The actual cached min-prefix may depend on every prior read; in this
explicit regular world its NEW returned artifact accepts true for EVERY route
and raw word, without independence. Counts/read source remain the old ones. -/
theorem adaptive_regular_any_raw (m K : ℕ) (hm : 0 < m) (route : Router) (omega : Raw (m+K)) :
    returned m K route (sourceData regularParameters omega)=some true := by
  have hb := run_minCount_bounds m K route (sourceData regularParameters omega)
  unfold returned
  rw [decoded_source_prefix]
  exact regular_any_raw_output _ (hm.trans_le hb.1)

theorem actual_registered_cache_outputs :
    returned adaptiveWarmup adaptiveExtra (feedbackRouter adaptiveWarmup)
      (sourceData regularParameters adaptiveRegisteredRaw)=some true ∧
    returned adaptiveWarmup adaptiveExtra (feedbackRouter adaptiveWarmup)
      (sourceData regularParameters adaptiveCountRaw)=some true :=
  ⟨adaptive_regular_any_raw _ _ (by decide) _ _,adaptive_regular_any_raw _ _ (by decide) _ _⟩

/-- SAME immutable original32/128sign registration, both old parameter worlds.
No new word or source/data threshold is chosen for the new algorithm. -/
theorem original_registered_outputs :
    orient (sourceData regularParameters registeredRaw)=some true ∧
    orient (sourceData reverseParameters registeredRaw)=some false := by
  constructor
  · exact regular_any_raw_output _ (by decide)
  · have hp : 0≤ mean (sourceData reverseParameters registeredRaw) 1 := by
      rw [registered_means]
      norm_num [trueMean,reverseParameters,Fin.ext_iff]
    rw [orient_of_anchor_nonneg _ hp]
    exact registered_reverse_output

/-- Zero-count remains an actual rejection, not an inferred accepted ranking. -/
theorem zero_budget_reject (data : Data 0) : orient data=none := by
  rw [orient,DualDriveFiniteNoisyCalibration.zero_budget_reject data]
  rfl

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DualDrivePositiveOrientationCalibration
