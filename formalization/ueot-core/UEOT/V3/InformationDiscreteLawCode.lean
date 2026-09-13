import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Countable measure-valued law codes have measurable decoders

For P-INFO-03 the predictive core is a discrete random variable whose values
are probability laws for the future. The key recovery step therefore needs a
measurable inverse from the measure-valued representation back to the discrete
core label.

For a countable label type `C`, any injective code `law : C → Measure Y`
admits a measurable decoder from Giry's measurable space on `Measure Y` back
to `C`, with `decode code (law c) = c` for every label.

The construction does not assume that the whole measure space is standard
Borel. For each pair of distinct codewords it chooses one measurable event on
which the two measures differ. The countable family of those evaluations gives
measurable, pairwise-disjoint signature sets for the code image.
-/

namespace UEOT.V3.InformationDiscreteLawCode

noncomputable section

open MeasureTheory

universe uC uY

variable {C : Type uC} {Y : Type uY}
variable [MeasurableSpace C] [MeasurableSpace Y]
variable [Countable C] [MeasurableSingletonClass C] [Nonempty C]

/-- A countable predictive-core representation by distinct future laws. -/
structure DiscreteLawCode where
  law : C → Measure Y
  injective_law : Function.Injective law

namespace DiscreteLawCode

/-- Distinct measures differ on at least one measurable event. -/
lemma exists_measurableSet_measure_ne
    {μ ν : Measure Y} (hne : μ ≠ ν) :
    ∃ A : Set Y, MeasurableSet A ∧ μ A ≠ ν A := by
  by_contra h
  push Not at h
  apply hne
  ext A hA
  exact h A hA

/-- A measurable event chosen to distinguish two distinct codewords. For an
equal pair the event is `∅`; that coordinate carries no information. -/
def separatingEvent
    (code : DiscreteLawCode (C := C) (Y := Y)) (c d : C) : Set Y := by
  classical
  exact if hcd : c = d then ∅ else
    Classical.choose
      (exists_measurableSet_measure_ne (code.injective_law.ne hcd))

lemma measurableSet_separatingEvent
    (code : DiscreteLawCode (C := C) (Y := Y)) (c d : C) :
    MeasurableSet (separatingEvent code c d) := by
  classical
  unfold separatingEvent
  split_ifs with hcd
  · exact MeasurableSet.empty
  · exact (Classical.choose_spec
      (exists_measurableSet_measure_ne (code.injective_law.ne hcd))).1

lemma separatingEvent_distinguishes
    (code : DiscreteLawCode (C := C) (Y := Y))
    {c d : C} (hcd : c ≠ d) :
    code.law c (separatingEvent code c d) ≠
      code.law d (separatingEvent code c d) := by
  classical
  unfold separatingEvent
  rw [dif_neg hcd]
  exact (Classical.choose_spec
    (exists_measurableSet_measure_ne (code.injective_law.ne hcd))).2

/-- Measures with exactly the same countable distinguishing signature as one
codeword. The set may contain measures outside the code image; different
codeword signature sets are nevertheless disjoint. -/
def matchSet
    (code : DiscreteLawCode (C := C) (Y := Y)) (c : C) : Set (Measure Y) :=
  {ν | ∀ a b : C,
    ν (separatingEvent code a b) =
      code.law c (separatingEvent code a b)}

lemma measurableSet_matchSet
    (code : DiscreteLawCode (C := C) (Y := Y)) (c : C) :
    MeasurableSet (matchSet code c) := by
  rw [show matchSet code c =
      ⋂ a : C, ⋂ b : C,
        {ν : Measure Y |
          ν (separatingEvent code a b) =
            code.law c (separatingEvent code a b)} by
    ext ν
    simp [matchSet]]
  apply MeasurableSet.iInter
  intro a
  apply MeasurableSet.iInter
  intro b
  exact measurableSet_eq_fun
    (Measure.measurable_coe (measurableSet_separatingEvent code a b))
    measurable_const

lemma law_mem_matchSet
    (code : DiscreteLawCode (C := C) (Y := Y)) (c : C) :
    code.law c ∈ matchSet code c := by
  simp [matchSet]

lemma matchSet_unique
    (code : DiscreteLawCode (C := C) (Y := Y))
    {c d : C} {ν : Measure Y}
    (hc : ν ∈ matchSet code c)
    (hd : ν ∈ matchSet code d) :
    c = d := by
  by_contra hcd
  have hc' := hc c d
  have hd' := hd c d
  exact separatingEvent_distinguishes code hcd (hc'.symm.trans hd')

/-- The union of all valid code signatures. -/
def matched
    (code : DiscreteLawCode (C := C) (Y := Y)) : Set (Measure Y) :=
  ⋃ c : C, matchSet code c

lemma measurableSet_matched
    (code : DiscreteLawCode (C := C) (Y := Y)) :
    MeasurableSet (matched code) := by
  unfold matched
  exact MeasurableSet.iUnion fun c => measurableSet_matchSet code c

/-- Arbitrary default label used only for measures outside all code signatures. -/
def defaultLabel : C := Classical.choice inferInstance

/-- Measurable inverse on the countable code image. -/
def decode
    (code : DiscreteLawCode (C := C) (Y := Y)) (ν : Measure Y) : C := by
  classical
  exact if h : ∃ c : C, ν ∈ matchSet code c then Classical.choose h
  else defaultLabel (C := C)

lemma decode_eq_of_mem_matchSet
    (code : DiscreteLawCode (C := C) (Y := Y))
    {ν : Measure Y} {c : C}
    (hc : ν ∈ matchSet code c) :
    decode code ν = c := by
  classical
  unfold decode
  split
  · rename_i hmatch
    exact matchSet_unique code (Classical.choose_spec hmatch) hc
  · rename_i hnomatch
    exact False.elim (hnomatch ⟨c, hc⟩)

@[simp]
theorem decode_law
    (code : DiscreteLawCode (C := C) (Y := Y)) (c : C) :
    decode code (code.law c) = c :=
  decode_eq_of_mem_matchSet code (law_mem_matchSet code c)

lemma decode_preimage_singleton_of_ne_default
    (code : DiscreteLawCode (C := C) (Y := Y))
    {c : C} (hc0 : c ≠ defaultLabel (C := C)) :
    decode code ⁻¹' {c} = matchSet code c := by
  classical
  ext ν
  constructor
  · intro hν
    have hdec : decode code ν = c := by simpa using hν
    unfold decode at hdec
    split at hdec <;> rename_i hmatch
    · have hchosen : ν ∈ matchSet code (Classical.choose hmatch) :=
        Classical.choose_spec hmatch
      have heq : Classical.choose hmatch = c := hdec
      simpa [heq] using hchosen
    · exact False.elim (hc0 hdec.symm)
  · intro hν
    have hdec : decode code ν = c := decode_eq_of_mem_matchSet code hν
    simpa [hdec]

lemma decode_preimage_default
    (code : DiscreteLawCode (C := C) (Y := Y)) :
    decode code ⁻¹' {defaultLabel (C := C)} =
      matchSet code (defaultLabel (C := C)) ∪ (matched code)ᶜ := by
  classical
  ext ν
  constructor
  · intro hν
    have hdec : decode code ν = defaultLabel (C := C) := by simpa using hν
    by_cases hmatch : ∃ c : C, ν ∈ matchSet code c
    · left
      have hchosen : ν ∈ matchSet code (Classical.choose hmatch) :=
        Classical.choose_spec hmatch
      have heq : Classical.choose hmatch = defaultLabel (C := C) := by
        simpa [decode, hmatch] using hdec
      simpa [heq] using hchosen
    · right
      simp only [matched, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
      exact fun c hc => hmatch ⟨c, hc⟩
  · intro hν
    rcases hν with hν | hν
    · have hdec : decode code ν = defaultLabel (C := C) :=
        decode_eq_of_mem_matchSet code hν
      simpa [hdec]
    · have hnomatch : ¬ ∃ c : C, ν ∈ matchSet code c := by
        intro h
        rcases h with ⟨c, hc⟩
        exact hν (show ν ∈ matched code from Set.mem_iUnion.2 ⟨c, hc⟩)
      simp [decode, hnomatch]

/-- The law decoder is measurable for Giry's measurable structure on measures. -/
theorem measurable_decode
    (code : DiscreteLawCode (C := C) (Y := Y)) :
    Measurable (decode code) := by
  apply measurable_to_countable'
  intro c
  by_cases hc0 : c = defaultLabel (C := C)
  · subst c
    rw [decode_preimage_default code]
    exact (measurableSet_matchSet code (defaultLabel (C := C))).union
      (measurableSet_matched code).compl
  · rw [decode_preimage_singleton_of_ne_default code hc0]
    exact measurableSet_matchSet code c

/-- Composing any measurable measure-valued prediction with the decoder gives
a measurable discrete predictive-core label. -/
theorem measurable_decode_comp
    (code : DiscreteLawCode (C := C) (Y := Y))
    {Z : Type*} [MeasurableSpace Z]
    {q : Z → Measure Y} (hq : Measurable q) :
    Measurable (fun z => decode code (q z)) :=
  (measurable_decode code).comp hq

/-- Exact law equality recovers the corresponding discrete core label. -/
theorem decode_eq_of_law_eq
    (code : DiscreteLawCode (C := C) (Y := Y))
    {ν : Measure Y} {c : C} (h : ν = code.law c) :
    decode code ν = c := by
  rw [h]
  exact decode_law code c

end DiscreteLawCode

end

end UEOT.V3.InformationDiscreteLawCode
