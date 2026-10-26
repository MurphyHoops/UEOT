import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ObservableBeliefQuotient

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ObservableBeliefQuotientWitness

open MeasureTheory ProbabilityTheory
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure
open UEOT.V3.GeneralBayesPosterior
open ObservableBeliefQuotient
open scoped ENNReal

noncomputable section

abbrev State := Bool × Bool

def observe (x : State) : Bool := x.1

private theorem measurable_observe : Measurable observe := measurable_fst

def noise : Measure Bool := bernoulliMeasure true false ⟨1 / 4, by constructor <;> norm_num⟩

private instance noise_isProbability : IsProbabilityMeasure noise := by
  unfold noise
  infer_instance

def advance (x : State) (a n : Bool) : State :=
  (if a then Bool.xor x.1 n else x.1, Bool.xor x.2 n)

def source : Kernel (State × Bool) State where
  toFun xa := noise.map (advance xa.1 xa.2)
  measurable' := measurable_of_countable _

instance source_isMarkov : IsMarkovKernel source where
  isProbabilityMeasure xa := by
    change IsProbabilityMeasure (noise.map (advance xa.1 xa.2))
    exact noise.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

private theorem source_projection (x : State) (a : Bool) :
    (source (x, a)).map observe =
      noise.map (fun n => if a then Bool.xor x.1 n else x.1) := by
  change (noise.map (advance x a)).map observe = _
  rw [Measure.map_map measurable_observe (measurable_of_countable _)]
  rfl

theorem source_closed : ClosedTests source observe := by
  intro x x' hx a
  have hrow : (source (x, a)).map observe = (source (x', a)).map observe := by
    rw [source_projection, source_projection]
    change x.1 = x'.1 at hx
    rw [hx]
  simpa only [Measure.map_apply measurable_observe (measurableSet_singleton true)] using
    congrArg (fun μ : Measure Bool => μ {true}) hrow

private theorem probe_projection (x : State) :
    (source (x, false)).map observe = Measure.dirac (observe x) := by
  rw [source_projection]
  change noise.map (fun _ => observe x) = _
  simp only [Measure.map_const, measure_univ, one_smul]

theorem probe_observation_law (b : ProbabilityMeasure State) :
    observationLaw b.toMeasure source (observation observe measurable_observe) false =
      b.toMeasure.map observe := by
  have hO : fixedActionKernel (observation (A := Bool) observe measurable_observe) false =
      Kernel.deterministic observe measurable_observe := rfl
  have hP : (fixedActionKernel source false).map observe =
      Kernel.deterministic observe measurable_observe := by
    ext x s _hs
    rw [Kernel.map_apply _ measurable_observe]
    exact congrArg (fun μ : Measure Bool => μ s) (probe_projection x)
  rw [observationLaw, hO, Measure.deterministic_comp_eq_map measurable_observe,
    predictedLaw, Measure.map_comp b.toMeasure (fixedActionKernel source false)
      measurable_observe, hP, Measure.deterministic_comp_eq_map measurable_observe]

theorem probe_test_is_coordinate (b : ProbabilityMeasure State) :
    testExpectation source observe b [(false, true)] = (coordinate observe b : ℝ) := by
  rw [first_test_eq_observation observe measurable_observe source b false true,
    probe_observation_law]
  change ((b.toMeasure.map observe) {true}).toReal = _
  rw [Measure.map_apply measurable_observe (measurableSet_singleton true)]
  rfl

theorem predictive_equivalence_iff (b b' : ProbabilityMeasure State) :
    (∀ word : List (Bool × Bool),
      testExpectation source observe b word = testExpectation source observe b' word) ↔
      coordinate observe b = coordinate observe b' := by
  constructor
  · intro h
    apply Subtype.ext
    exact (probe_test_is_coordinate b).symm.trans
      ((h [(false, true)]).trans (probe_test_is_coordinate b'))
  · intro h word
    exact same_coordinate_same_tests observe measurable_observe source source_closed
      (false, false) (true, false) rfl rfl b b' h word

theorem actual_C1_descends (b : ProbabilityMeasure State) (a : Bool) :
    (c1BeliefTransitionKernel source (observation observe measurable_observe) (b, a)).map
        (coordinate observe) =
      quotientKernel observe measurable_observe source (false, false) (true, false)
        (coordinate observe b, a) := by
  exact quotientKernel_factor observe measurable_observe source source_closed
    (false, false) (true, false) rfl rfl b a

theorem source_hidden_flip_mass (x : State) (a : Bool) :
    source (x, a) {z | z.2 ≠ x.2} = (1 / 4 : ℝ≥0∞) := by
  change (noise.map (advance x a)) _ = _
  have hs : MeasurableSet {z : State | z.2 ≠ x.2} := (Set.to_countable _).measurableSet
  rw [Measure.map_apply (measurable_of_countable _) hs]
  have hpre : (advance x a) ⁻¹' {z : State | z.2 ≠ x.2} = {true} := by
    ext n
    cases hx : x.2 <;> cases n <;> simp [advance, hx]
  rw [hpre]
  change bernoulliMeasure true false _ {true} = _
  rw [bernoulliMeasure_apply_of_mem_of_notMem _ (measurableSet_singleton true)
    (by simp) (by simp)]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.coe_toReal]
  norm_num [unitInterval.toNNReal, NNReal.toReal]

def aliasZero : ProbabilityMeasure State := c1ProbDirac (false, false)
def aliasOne : ProbabilityMeasure State := c1ProbDirac (false, true)

private theorem alias_coordinates : coordinate observe aliasZero = coordinate observe aliasOne := by
  apply Subtype.ext
  change ((Measure.dirac (false, false)) (observe ⁻¹' {true})).toReal =
    ((Measure.dirac (false, true)) (observe ⁻¹' {true})).toReal
  simp [Measure.dirac_apply' _ ((measurableSet_singleton true).preimage measurable_observe),
    observe]

theorem aliases_have_all_same_future_tests :
    ∀ word : List (Bool × Bool),
      testExpectation source observe aliasZero word = testExpectation source observe aliasOne word :=
  (predictive_equivalence_iff aliasZero aliasOne).mpr alias_coordinates

def badSource : Kernel (State × Bool) State :=
  Kernel.deterministic
    (fun xa => (if xa.2 then xa.1.2 else xa.1.1, xa.1.2))
    (measurable_of_countable _)

instance badSource_isMarkov : IsMarkovKernel badSource := by
  unfold badSource
  infer_instance

theorem no_quotient_without_closed_tests :
    ¬ ∃ K : Kernel (unitInterval × Bool) unitInterval,
      ∀ (b : ProbabilityMeasure State) (a : Bool),
        (c1BeliefTransitionKernel badSource (observation observe measurable_observe) (b, a)).map
            (coordinate observe) = K (coordinate observe b, a) := by
  rintro ⟨K, hK⟩
  have hc := closed_tests_of_quotient observe measurable_observe badSource K hK
  have h := hc (false, false) (false, true) rfl true
  have hs := (measurableSet_singleton true).preimage measurable_observe
  change (Measure.dirac (false, false)) (observe ⁻¹' {true}) =
    (Measure.dirac (true, true)) (observe ⁻¹' {true}) at h
  norm_num [Measure.dirac_apply' _ hs, observe] at h

def reward (x : State) (a : Bool) : ℝ :=
  (if observe x then 1 else 0) - (if a then 1 / 8 else 0)

theorem reward_readout_factors (b : ProbabilityMeasure State) (a : Bool) :
    (∫ x, reward x a ∂b.toMeasure) =
      (coordinate observe b : ℝ) - (if a then 1 / 8 else 0) := by
  have h := observation_reward_factors observe measurable_observe b
    (fun y => (if y then 1 else 0) - (if a then 1 / 8 else 0))
  change (∫ x, ((if observe x then 1 else 0) - (if a then 1 / 8 else 0)) ∂b.toMeasure) = _
  rw [h]
  cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ring

theorem safe_readout_factors (b : ProbabilityMeasure State) :
    b.toMeasure.real {x | observe x = false} = 1 - (coordinate observe b : ℝ) := by
  exact safe_class_probability observe measurable_observe b

def hiddenReward (x : State) : ℝ := if x.2 then 1 else 0

def hiddenSafe : Set State := {x | x.2 = false}

theorem hidden_readouts_do_not_descend :
    (¬ ∃ rbar : unitInterval → ℝ, ∀ b : ProbabilityMeasure State,
      (∫ x, hiddenReward x ∂b.toMeasure) = rbar (coordinate observe b)) ∧
    (¬ ∃ sbar : unitInterval → ℝ, ∀ b : ProbabilityMeasure State,
      b.toMeasure.real hiddenSafe = sbar (coordinate observe b)) := by
  constructor
  · rintro ⟨rbar, hr⟩
    have h₀ := hr aliasZero
    have h₁ := hr aliasOne
    rw [alias_coordinates] at h₀
    have h := h₀.trans h₁.symm
    norm_num [aliasZero, aliasOne, c1ProbDirac, hiddenReward] at h
  · rintro ⟨sbar, hs⟩
    have h₀ := hs aliasZero
    have h₁ := hs aliasOne
    rw [alias_coordinates] at h₀
    have h := h₀.trans h₁.symm
    have hm : MeasurableSet hiddenSafe := (Set.to_countable _).measurableSet
    norm_num [aliasZero, aliasOne, c1ProbDirac, Measure.real,
      Measure.dirac_apply' _ hm, hiddenSafe] at h

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ObservableBeliefQuotientWitness
