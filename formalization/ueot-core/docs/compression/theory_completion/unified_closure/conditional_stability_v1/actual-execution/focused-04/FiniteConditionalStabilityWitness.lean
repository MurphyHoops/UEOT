import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteConditionalStability

/-!
# Three-state sharpness and rare-event witnesses

The two safe outcomes are `some false` and `some true`; `none` is outside the
conditioning event.  For any 0 < r <= 1 the two source PMFs put mass r on
opposite safe outcomes and share mass 1-r outside.  Their unconditional TV is
r, but their actual filtered laws have TV one.  Thus the factor 1/eventMass
is attained and a survival lower bound cannot be omitted.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteConditionalStabilityWitness

open MeasureTheory
open UEOT.V3.PathError UEOT.V3.TotalVariation
open FiniteConditionalStability
open scoped BigOperators Classical

noncomputable section

abbrev State := Option Bool
local instance : MeasurableSpace State := ⊤

def safe : Set State := {x | x ≠ none}

private theorem none_ne_false : (none : State) ≠ some false := by decide
private theorem none_ne_true : (none : State) ≠ some true := by decide
private theorem false_ne_true : (some false : State) ≠ some true := by decide

private theorem safe_event_mass (p : PMF State) :
    p.toMeasure.real safe = (p (some false)).toReal + (p (some true)).toReal := by
  have hs : safe = (↑({some false, some true} : Finset State) : Set State) := by
    ext x
    fin_cases x <;> simp [safe, none_ne_false, none_ne_true,
      Ne.symm none_ne_false, Ne.symm none_ne_true, false_ne_true, Ne.symm false_ne_true]
  rw [hs, pmfMeasureReal_eq_sum_finset]
  simp [false_ne_true]

private def rareWeight (r : ℝ) (b : Bool) : State → ℝ
  | none => 1 - r
  | some c => if c = b then r else 0

private theorem rareWeight_nonneg
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (b : Bool) (x : State) :
    0 ≤ rareWeight r b x := by
  cases x with
  | none => exact sub_nonneg.mpr hr1
  | some c => exact ite_nonneg hr0 (le_refl 0)

/-- An actual normalized PMF on three states, with no supplied conditional law. -/
def rareSource (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (b : Bool) : PMF State :=
  PMF.ofFintype (fun x => ENNReal.ofReal (rareWeight r b x)) (by
    have hsum : (1 - r) + r = 1 := by ring
    cases b <;>
      simp only [Fintype.sum_option, Fintype.sum_bool, rareWeight,
        Bool.false_eq_true, Bool.true_eq_false, if_false, if_true,
        ENNReal.ofReal_zero, add_zero, zero_add] <;>
      rw [← ENNReal.ofReal_add (sub_nonneg.mpr hr1) hr0, hsum] <;> simp)

private theorem rareSource_mass
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (b : Bool) (x : State) :
    (rareSource r hr0 hr1 b x).toReal = rareWeight r b x := by
  simp only [rareSource, PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (rareWeight_nonneg r hr0 hr1 b x)]

private theorem rareSource_event_mass
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (b : Bool) :
    (rareSource r hr0 hr1 b).toMeasure.real safe = r := by
  change ((rareSource r hr0 hr1 b).toMeasure safe).toReal = r
  rw [PMF.toMeasure_apply_fintype]
  cases b <;>
    simp [safe, Set.indicator_apply, Fintype.sum_option, Fintype.sum_bool,
      rareSource, rareWeight, ENNReal.toReal_ofReal hr0]

private theorem rareSource_conditioned
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hr : 0 < r) (b : Bool)
    (hp : 0 < (rareSource r hr0 hr1 b).toMeasure.real safe) :
    conditionedPMF (rareSource r hr0 hr1 b) safe hp = PMF.pure (some b) := by
  have hne : ENNReal.ofReal r ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hr)
  apply PMF.ext
  intro x
  unfold conditionedPMF
  rw [PMF.filter_apply, tsum_fintype]
  cases b <;> fin_cases x <;>
    simp [safe, Set.indicator_apply, Fintype.sum_option, Fintype.sum_bool,
      rareSource, rareWeight, PMF.pure_apply,
      ENNReal.mul_inv_cancel hne ENNReal.ofReal_ne_top]

private theorem rareSource_tv
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    tvDist (rareSource r hr0 hr1 false).toMeasure
      (rareSource r hr0 hr1 true).toMeasure = r := by
  rw [tvDist_eq_one_sub_pmfCommonMass]
  simp only [pmfCommonMass, Fintype.sum_option, Fintype.sum_bool,
    rareSource_mass, rareWeight, Bool.false_eq_true, Bool.true_eq_false,
    if_false, if_true, min_self, min_eq_left hr0, min_eq_right hr0,
    add_zero, zero_add]
  ring

private theorem rareSource_conditioned_tv
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hr : 0 < r)
    (hp : 0 < (rareSource r hr0 hr1 false).toMeasure.real safe)
    (hq : 0 < (rareSource r hr0 hr1 true).toMeasure.real safe) :
    tvDist (conditionedPMF (rareSource r hr0 hr1 false) safe hp).toMeasure
      (conditionedPMF (rareSource r hr0 hr1 true) safe hq).toMeasure = 1 := by
  rw [rareSource_conditioned r hr0 hr1 hr false hp,
    rareSource_conditioned r hr0 hr1 hr true hq,
    tvDist_eq_one_sub_pmfCommonMass]
  norm_num [pmfCommonMass, Fintype.sum_option, Fintype.sum_bool, PMF.pure_apply,
    none_ne_false, none_ne_true, Ne.symm none_ne_false, Ne.symm none_ne_true]

/-- Every positive event mass in (0,1] attains the max-mass amplification
factor: original TV = r, both event masses = r, conditional TV = 1. -/
theorem rare_event_sharpness
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    let p := rareSource r (le_of_lt hr) hr1 false
    let q := rareSource r (le_of_lt hr) hr1 true
    p.toMeasure.real safe = r ∧ q.toMeasure.real safe = r ∧
      tvDist p.toMeasure q.toMeasure = r ∧
      ∃ (hp : 0 < p.toMeasure.real safe) (hq : 0 < q.toMeasure.real safe),
        tvDist (conditionedPMF p safe hp).toMeasure
          (conditionedPMF q safe hq).toMeasure = 1 := by
  dsimp only
  have hp : 0 < (rareSource r (le_of_lt hr) hr1 false).toMeasure.real safe := by
    rw [rareSource_event_mass]
    exact hr
  have hq : 0 < (rareSource r (le_of_lt hr) hr1 true).toMeasure.real safe := by
    rw [rareSource_event_mass]
    exact hr
  exact ⟨rareSource_event_mass r _ _ false, rareSource_event_mass r _ _ true,
    rareSource_tv r _ _, hp, hq, rareSource_conditioned_tv r _ _ hr hp hq⟩

/-- Arbitrarily small unconditional error can coexist with maximal conditional
error.  This rules out a uniform continuity claim without a positive survival
lower bound, even on this fixed three-state alphabet and the same event. -/
theorem arbitrarily_small_unconditional_error
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ (p q : PMF State)
      (hp : 0 < p.toMeasure.real safe) (hq : 0 < q.toMeasure.real safe),
      tvDist p.toMeasure q.toMeasure < delta ∧
        tvDist (conditionedPMF p safe hp).toMeasure
          (conditionedPMF q safe hq).toMeasure = 1 := by
  let r := min (delta / 2) (1 / 2 : ℝ)
  have hr : 0 < r := lt_min (by positivity) (by norm_num)
  have hr1 : r ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hrdelta : r < delta := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  obtain ⟨hpMass, hqMass, hTV, hp, hq, hcTV⟩ := rare_event_sharpness r hr hr1
  refine ⟨rareSource r (le_of_lt hr) hr1 false,
    rareSource r (le_of_lt hr) hr1 true, hp, hq, ?_, hcTV⟩
  rw [hTV]
  exact hrdelta

private def threeSource (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : a + b + c = 1) : PMF State :=
  PMF.ofFintype (fun x => ENNReal.ofReal (match x with
    | none => c
    | some false => a
    | some true => b)) (by
      simp only [Fintype.sum_option, Fintype.sum_bool]
      rw [← ENNReal.ofReal_add hb ha,
        ← ENNReal.ofReal_add hc (add_nonneg hb ha)]
      have hsum' : c + (b + a) = 1 := by linarith
      rw [hsum', ENNReal.ofReal_one])

def positiveP : PMF State :=
  threeSource (1/4) (1/4) (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def positiveQ : PMF State :=
  threeSource (3/8) (1/8) (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem positiveP_mass : positiveP.toMeasure.real safe = 1 / 2 := by
  rw [safe_event_mass]
  norm_num [positiveP, threeSource]

private theorem positiveQ_mass : positiveQ.toMeasure.real safe = 1 / 2 := by
  rw [safe_event_mass]
  norm_num [positiveQ, threeSource]

private theorem positive_source_tv :
    tvDist positiveP.toMeasure positiveQ.toMeasure = 1 / 8 := by
  rw [tvDist_eq_one_sub_pmfCommonMass]
  norm_num [pmfCommonMass, positiveP, positiveQ, threeSource,
    Fintype.sum_option, Fintype.sum_bool]

/-- A nontrivial positive certificate with reference mass 1/2 > error 1/8.
The actually filtered TV equals the certified 1/4, so sharpness is not only
an example where the bound has already saturated at one. -/
theorem positive_reference_certificate_is_sharp :
    ∃ (hp : 0 < positiveP.toMeasure.real safe)
      (hq : 0 < positiveQ.toMeasure.real safe),
      tvDist positiveP.toMeasure positiveQ.toMeasure = 1 / 8 ∧
      positiveQ.toMeasure.real safe = 1 / 2 ∧
      tvDist (conditionedPMF positiveP safe hp).toMeasure
        (conditionedPMF positiveQ safe hq).toMeasure = 1 / 4 ∧
      tvDist (conditionedPMF positiveP safe hp).toMeasure
        (conditionedPMF positiveQ safe hq).toMeasure ≤
        min 1 ((1 / 8) / positiveQ.toMeasure.real safe) := by
  have hp : 0 < positiveP.toMeasure.real safe := by rw [positiveP_mass]; norm_num
  have hq : 0 < positiveQ.toMeasure.real safe := by rw [positiveQ_mass]; norm_num
  refine ⟨hp, hq, positive_source_tv, positiveQ_mass, ?_, ?_⟩
  · have hpAtom (x : State) := mass_mul_conditioned_atom positiveP safe hp x
    have hqAtom (x : State) := mass_mul_conditioned_atom positiveQ safe hq x
    have hp0 : (conditionedPMF positiveP safe hp none).toReal = 0 := by
      have h := hpAtom none
      norm_num [positiveP_mass, safe] at h
      linarith
    have hpf : (conditionedPMF positiveP safe hp (some false)).toReal = 1/2 := by
      have h := hpAtom (some false)
      norm_num [positiveP_mass, safe, positiveP, threeSource, Ne.symm none_ne_false] at h
      linarith
    have hpt : (conditionedPMF positiveP safe hp (some true)).toReal = 1/2 := by
      have h := hpAtom (some true)
      norm_num [positiveP_mass, safe, positiveP, threeSource, Ne.symm none_ne_true] at h
      linarith
    have hq0 : (conditionedPMF positiveQ safe hq none).toReal = 0 := by
      have h := hqAtom none
      norm_num [positiveQ_mass, safe] at h
      linarith
    have hqf : (conditionedPMF positiveQ safe hq (some false)).toReal = 3/4 := by
      have h := hqAtom (some false)
      norm_num [positiveQ_mass, safe, positiveQ, threeSource, Ne.symm none_ne_false] at h
      linarith
    have hqt : (conditionedPMF positiveQ safe hq (some true)).toReal = 1/4 := by
      have h := hqAtom (some true)
      norm_num [positiveQ_mass, safe, positiveQ, threeSource, Ne.symm none_ne_true] at h
      linarith
    rw [tvDist_eq_one_sub_pmfCommonMass]
    norm_num [pmfCommonMass, Fintype.sum_option, Fintype.sum_bool,
      hp0, hpf, hpt, hq0, hqf, hqt]
  · exact conditional_tv_le_reference_mass positiveP positiveQ safe hp hq
      (1 / 8) (le_of_eq positive_source_tv)

end

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteConditionalStabilityWitness
