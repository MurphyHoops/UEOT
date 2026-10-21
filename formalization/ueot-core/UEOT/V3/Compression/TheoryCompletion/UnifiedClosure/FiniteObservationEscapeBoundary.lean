import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscape

/-!
A concrete infinite-ambient boundary: source-relative TV retains escape and live mass mismatch, while the finite encoding is not a global isometry between arbitrary references.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundaryCheck

open MeasureTheory UEOT.V3.TotalVariation UEOT.V3.PathError
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck
open scoped BigOperators Classical ENNReal

noncomputable section

local instance : MeasurableSpace Bool := ⊤
local instance : MeasurableSpace ℕ := ⊤
local instance : MeasurableSpace (Option Bool) := ⊤
local instance : MeasurableSpace (Option (Option Bool)) := ⊤

def live (b : Bool) : ℕ := if b then 2 else 0

theorem live_injective : Function.Injective live := by
  intro b c h
  cases b <;> cases c <;> simp_all [live]

private theorem none_ne_some_explicit {α : Type*} (x : α) :
    (none : Option α) ≠ some x := by
  intro h
  cases h

private theorem map_injective_atom {α β : Type*} (f : α → β)
    (hf : Function.Injective f) (p : PMF α) (a : α) :
    (p.map f) (f a) = p a := by
  rw [PMF.map_apply]
  refine (tsum_eq_single a ?_).trans ?_
  · intro b hb
    exact if_neg (fun h => hb (hf h).symm)
  · simp

private theorem map_some_none {α : Type*} (p : PMF α) :
    (p.map some) none = 0 := by
  simp [PMF.map_apply, none_ne_some_explicit]

private theorem map_some_some {α : Type*} (p : PMF α) (a : α) :
    (p.map some) (some a) = p a :=
  map_injective_atom some (fun _ _ h => Option.some.inj h) p a

def sourceWeight (b : Bool) : ℝ := if b then 2 / 3 else 1 / 3

def referenceWeight : Option Bool → ℝ
    | none => 1 / 4
    | some false => 1 / 2
    | some true => 1 / 4

def sourceOnLive : PMF Bool :=
  PMF.ofFintype (fun b => ENNReal.ofReal (sourceWeight b)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (by
      intro b _
      cases b <;> norm_num [sourceWeight])]
    norm_num [sourceWeight, Fintype.sum_bool])

def finiteReference : PMF (Option Bool) :=
  PMF.ofFintype (fun z => ENNReal.ofReal (referenceWeight z)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (by
      intro z _
      cases z with
      | none => norm_num [referenceWeight]
      | some b => cases b <;> norm_num [referenceWeight])]
    norm_num [Fintype.sum_option, referenceWeight,
      Finset.sum_insert, Finset.sum_singleton])

def place (escape : ℕ) : Option Bool → ℕ
  | none => escape
  | some b => live b

def source : PMF ℕ := sourceOnLive.map live
def reference (escape : ℕ) : PMF ℕ := finiteReference.map (place escape)

theorem place_five_injective : Function.Injective (place 5) := by
  intro b c h
  cases b with
  | none =>
      cases c with
      | none => rfl
      | some c => cases c <;> norm_num [place, live] at h
  | some b =>
      cases c with
      | none => cases b <;> norm_num [place, live] at h
      | some c => exact congrArg some (live_injective h)

theorem atomEncode_place (escape : ℕ) (h0 : escape ≠ 0) (h2 : escape ≠ 2)
    (z : Option Bool) : atomEncode live (place escape z) = z := by
  cases z with
  | none =>
      apply (atomEncode_eq_none_iff live escape).2
      rintro ⟨b, hb⟩
      cases b
      · exact h0 hb.symm
      · exact h2 hb.symm
  | some b => exact atomEncode_atom live live_injective b

theorem reference_encoded (escape : ℕ) (h0 : escape ≠ 0) (h2 : escape ≠ 2) :
    (reference escape).map (atomEncode live) = finiteReference := by
  unfold reference
  rw [PMF.map_comp]
  have h : atomEncode live ∘ place escape = id := by
    funext z
    exact atomEncode_place escape h0 h2 z
  rw [h, PMF.map_id]

/-- A 1/4 mass genuinely escapes to an ambient point outside the live image. -/
theorem reference_escape_probability (escape : ℕ) (h0 : escape ≠ 0)
    (h2 : escape ≠ 2) :
    (reference escape).toMeasure.real (Set.range live)ᶜ = 1 / 4 := by
  rw [← atomEncode_escape_probability live (reference escape).toMeasure,
    PMF.toMeasure_map (atomEncode live) (reference escape) (atomEncode_measurable live),
    reference_encoded escape h0 h2]
  rw [measureReal_def,
    PMF.toMeasure_apply_singleton _ none (measurableSet_singleton none)]
  norm_num [finiteReference, referenceWeight]

/-- This instantiates the exact TV theorem on the infinite alphabet ℕ;
live mass mismatch contributes in addition to escape. -/
theorem source_reference_tv (escape : ℕ) (h0 : escape ≠ 0) (h2 : escape ≠ 2) :
    tvDist source.toMeasure (reference escape).toMeasure = 5 / 12 := by
  unfold source
  rw [tvDist_embedded_eq_encoded live live_injective,
    reference_encoded escape h0 h2, tvDist_eq_one_sub_pmfCommonMass]
  simp only [pmfCommonMass, Fintype.sum_option, Fintype.sum_bool,
    map_some_none, map_some_some]
  norm_num [sourceOnLive, sourceWeight, finiteReference, referenceWeight]

def recodeSeven : Option Bool → Option (Option Bool)
  | none => none
  | some b => some (some b)

private theorem recode_injective : Function.Injective recodeSeven := by
  intro z w h
  cases z <;> cases w <;> simp_all [recodeSeven]

private theorem recode_mass (z : Option (Option Bool)) :
    (finiteReference.map recodeSeven) z =
      match z with
      | none => finiteReference none
      | some none => 0
      | some (some b) => finiteReference (some b) := by
  cases z with
  | none => exact map_injective_atom recodeSeven recode_injective finiteReference none
  | some z =>
      cases z with
      | none =>
          have hnone : ∀ z, (some none : Option (Option Bool)) ≠ recodeSeven z := by
            intro z
            cases z with
            | none => exact Option.some_ne_none _
            | some b =>
                intro h
                exact none_ne_some_explicit b (Option.some.inj h)
          simp [PMF.map_apply, hnone]
      | some b =>
          exact map_injective_atom recodeSeven recode_injective finiteReference (some b)

theorem recode_seven (z : Option Bool) :
    atomEncode (place 5) (place 7 z) = recodeSeven z := by
  cases z with
  | none =>
      apply (atomEncode_eq_none_iff (place 5) 7).2
      rintro ⟨b, hb⟩
      cases b with
      | none => norm_num [place] at hb
      | some b => cases b <;> norm_num [place, live] at hb
  | some b => exact atomEncode_atom (place 5) place_five_injective (some b)

/-- The original references differ by 1/4 although their escaped codes agree.
This prevents interpreting the source-specific equality as global isometry. -/
theorem references_original_tv :
    tvDist (reference 5).toMeasure (reference 7).toMeasure = 1 / 4 := by
  change tvDist (finiteReference.map (place 5)).toMeasure (reference 7).toMeasure = _
  rw [tvDist_embedded_eq_encoded (place 5) place_five_injective]
  have hmap : (reference 7).map (atomEncode (place 5)) =
      finiteReference.map recodeSeven := by
    unfold reference
    rw [PMF.map_comp]
    congr 1
    funext z
    exact recode_seven z
  rw [hmap, tvDist_eq_one_sub_pmfCommonMass]
  simp only [pmfCommonMass, Fintype.sum_option, Fintype.sum_bool,
    map_some_none, map_some_some, recode_mass]
  norm_num [finiteReference, referenceWeight]

theorem references_encoded_tv_zero :
    tvDist ((reference 5).map (atomEncode live)).toMeasure
      ((reference 7).map (atomEncode live)).toMeasure = 0 := by
  rw [reference_encoded 5 (by decide) (by decide),
    reference_encoded 7 (by decide) (by decide), tvDist_self_eq_zero]

/-- One joint boundary receipt distinguishes exact source TV, retained escape,
and the failure of a stronger reference-to-reference isometry claim. -/
theorem infinite_ambient_positive_escape_boundary :
    (reference 5).toMeasure.real (Set.range live)ᶜ = 1 / 4 ∧
    (reference 7).toMeasure.real (Set.range live)ᶜ = 1 / 4 ∧
    tvDist source.toMeasure (reference 5).toMeasure = 5 / 12 ∧
    tvDist source.toMeasure (reference 7).toMeasure = 5 / 12 ∧
    tvDist (reference 5).toMeasure (reference 7).toMeasure = 1 / 4 ∧
    tvDist ((reference 5).map (atomEncode live)).toMeasure
      ((reference 7).map (atomEncode live)).toMeasure = 0 := by
  exact ⟨reference_escape_probability 5 (by decide) (by decide),
    reference_escape_probability 7 (by decide) (by decide),
    source_reference_tv 5 (by decide) (by decide),
    source_reference_tv 7 (by decide) (by decide),
    references_original_tv, references_encoded_tv_zero⟩

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeBoundaryCheck
