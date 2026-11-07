import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeSource

/-! Exact finite output-count law of the actual regenerative source. -/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeSource

open scoped BigOperators

def eventTotal (a : Action) (z : Noise) : ℕ :=
  (if retains a z then 1 else 0) + (if births a z then 1 else 0)

theorem programStep_total (theta i tag : Bool) (z : Noise) :
    outputCapital (programStep (programBody theta i tag) z) =
      eventTotal (programAction theta i) z := by
  rw [program_step_executes]
  cases hr : retains (programAction theta i) z <;>
    cases hb : births (programAction theta i) z <;>
    simp [outputCapital, executedResult, optionCount, eventTotal, hr, hb]

def eventCountProbability (p : Parameters) (a : Action) (n : ℕ) : ℝ :=
  ∑ z : Noise, noiseWeight p z * (if eventTotal a z = n then 1 else 0)

def actualCountProbability (p : Parameters) (theta i tag : Bool) (n : ℕ) : ℝ :=
  ∑ z : Noise, noiseWeight p z *
    (if outputCapital (programStep (programBody theta i tag) z) = n then 1 else 0)

theorem actualCountProbability_eq (p : Parameters) (theta i tag : Bool) (n : ℕ) :
    actualCountProbability p theta i tag n =
      eventCountProbability p (programAction theta i) n := by
  simp [actualCountProbability, eventCountProbability, programStep_total]

theorem care_count_zero (p : Parameters) :
    eventCountProbability p .care 0 = (1-p.survival) * (1-p.commonBirth) := by
  simp [eventCountProbability, eventTotal, Noise, noiseWeight, survivalWeight,
    birthWeight, damageWeight, retains, births, Fintype.sum_prod_type, Fin.sum_univ_succ]
  ring

theorem care_count_one (p : Parameters) :
    eventCountProbability p .care 1 =
      p.survival * (1-p.commonBirth) + (1-p.survival) * p.commonBirth := by
  simp [eventCountProbability, eventTotal, Noise, noiseWeight, survivalWeight,
    birthWeight, damageWeight, retains, births, Fintype.sum_prod_type, Fin.sum_univ_succ]
  ring

theorem care_count_two (p : Parameters) :
    eventCountProbability p .care 2 = p.survival * p.commonBirth := by
  simp [eventCountProbability, eventTotal, Noise, noiseWeight, survivalWeight,
    birthWeight, damageWeight, retains, births, Fintype.sum_prod_type, Fin.sum_univ_succ]
  ring

theorem bloom_count_zero (p : Parameters) :
    eventCountProbability p .bloom 0 =
      (1-p.survival+p.careOnly) * (1-p.commonBirth-p.bloomOnly) := by
  simp [eventCountProbability, eventTotal, Noise, noiseWeight, survivalWeight,
    birthWeight, damageWeight, retains, births, Fintype.sum_prod_type, Fin.sum_univ_succ]
  ring

theorem bloom_count_one (p : Parameters) :
    eventCountProbability p .bloom 1 =
      (p.survival-p.careOnly) * (1-p.commonBirth-p.bloomOnly) +
        (1-p.survival+p.careOnly) * (p.commonBirth+p.bloomOnly) := by
  simp [eventCountProbability, eventTotal, Noise, noiseWeight, survivalWeight,
    birthWeight, damageWeight, retains, births, Fintype.sum_prod_type, Fin.sum_univ_succ]
  ring

theorem bloom_count_two (p : Parameters) :
    eventCountProbability p .bloom 2 =
      (p.survival-p.careOnly) * (p.commonBirth+p.bloomOnly) := by
  simp [eventCountProbability, eventTotal, Noise, noiseWeight, survivalWeight,
    birthWeight, damageWeight, retains, births, Fintype.sum_prod_type, Fin.sum_univ_succ]
  ring

/-- Even the common recovery/optimal program can lose its entire lineage immediately. -/
theorem actual_best_extinction_pos (p : Parameters) (hp : Valid p) (tag : Bool) :
    0 < actualCountProbability p true false tag 0 := by
  rw [actualCountProbability_eq]
  change 0 < eventCountProbability p .bloom 0
  rw [bloom_count_zero]
  apply mul_pos <;> linarith [hp.survival_lt_one, hp.careOnly_pos, hp.birth_sum_lt_one]

theorem concrete_care_count_law (tag : Bool) :
    actualCountProbability concreteParameters false false tag 0 = 5/32 ∧
    actualCountProbability concreteParameters false false tag 1 = 9/16 ∧
    actualCountProbability concreteParameters false false tag 2 = 9/32 := by
  simp only [actualCountProbability_eq, programAction, Bool.false_eq_true, ↓reduceIte]
  rw [care_count_zero, care_count_one, care_count_two]
  norm_num [concreteParameters]

theorem concrete_bloom_count_law (tag : Bool) :
    actualCountProbability concreteParameters true false tag 0 = 9/64 ∧
    actualCountProbability concreteParameters true false tag 1 = 15/32 ∧
    actualCountProbability concreteParameters true false tag 2 = 25/64 := by
  simp only [actualCountProbability_eq, programAction, Bool.false_eq_true, ↓reduceIte]
  rw [bloom_count_zero, bloom_count_one, bloom_count_two]
  norm_num [concreteParameters]

theorem concrete_best_extinct_inferior_nonzero_product (tag : Bool) :
    actualCountProbability concreteParameters true false tag 0 *
      (1 - actualCountProbability concreteParameters false false tag 0) = 243/2048 := by
  rw [(concrete_bloom_count_law tag).1, (concrete_care_count_law tag).1]
  norm_num

/-- Probability that the actual old identity is retained under a legal request. -/
def actualRetainedProbability (p : Parameters) (x : Body) (a : Action) : ℝ :=
  ∑ z : Noise, noiseWeight p z * (if (step x a z).retained.isSome then 1 else 0)

theorem healthy_retainedProbability (p : Parameters) (theta tag : Bool) (a : Action) :
    actualRetainedProbability p (programBody theta false tag) a = survivalRate p a := by
  have hr : ∀ z : Noise,
      (step (programBody theta false tag) a z).retained.isSome = retains a z := by
    intro z
    cases a with
    | care =>
        cases hh : retains .care z <;>
          simp [step, canExecute_program_care, executedResult, hh]
    | bloom =>
        cases hb : retains .bloom z <;>
          simp [step, canExecute_program_bloom, executedResult, hb]
    | stop => rfl
  simp only [actualRetainedProbability, hr]
  cases a <;>
    simp [Noise, noiseWeight, survivalWeight, birthWeight, damageWeight,
      survivalRate, retains, Fintype.sum_prod_type, Fin.sum_univ_succ] <;> ring

/-- Same physical program, same initial body, same wallet: expected-growth choice
strictly sacrifices the original identity's one-tick continuation probability. -/
theorem growth_choice_not_identity_survival_maximal (p : Parameters) (hp : Valid p) (tag : Bool) :
    actualRetainedProbability p (programBody true false tag) (programAction true false) <
      actualRetainedProbability p (programBody true false tag) .care := by
  rw [healthy_retainedProbability, healthy_retainedProbability]
  change p.survival - p.careOnly < p.survival
  linarith [hp.careOnly_pos]

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeSource
