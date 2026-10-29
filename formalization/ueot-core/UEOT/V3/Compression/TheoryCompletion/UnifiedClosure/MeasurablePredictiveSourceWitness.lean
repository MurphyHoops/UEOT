import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveSource

/-! An uncountable-state/action noisy consumer and a hidden-leak boundary.
The positive source has a genuinely non-atomic observation law, so its C1
identity is not a collection of positive-probability singleton Bayes formulas. -/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveSourceWitness
open MeasureTheory ProbabilityTheory
open UEOT.V3.GeneralBayesPosterior
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure
open MeasurablePredictiveSource
noncomputable section

def noise : Measure ℝ := gaussianReal 0 1
private instance noise_isProbability : IsProbabilityMeasure noise := by unfold noise; infer_instance

def visible (u : (ℝ × ℝ) × ℝ) : ℝ := u.1.1 + u.1.2 + u.2
def hidden (u : ((ℝ × ℝ) × ℝ) × ℝ) : ℝ := u.1.1.2 + u.2
private theorem measurable_visible : Measurable visible := by unfold visible; fun_prop
private theorem measurable_hidden : Measurable hidden := by unfold hidden; fun_prop

def actualSource : Kernel ((ℝ × ℝ) × ℝ) (ℝ × ℝ) :=
  source noise visible measurable_visible hidden measurable_hidden

private instance actualSource_isMarkov : IsMarkovKernel actualSource := by
  unfold actualSource
  infer_instance

/-- The general source theorem is actually consumed at uncountable visible,
hidden and action spaces with shared non-atomic noise. -/
theorem actual_C1_descends (b : ProbabilityMeasure (ℝ × ℝ)) (a : ℝ) :
    (c1BeliefTransitionKernel actualSource observation (b,a)).map coordinate =
      quotientKernel noise visible measurable_visible hidden measurable_hidden 0 (coordinate b,a) :=
  quotientKernel_factor noise visible measurable_visible hidden measurable_hidden 0 b a

private theorem coordinate_point (i : ℝ) :
    coordinate (c1ProbDirac (0,i)) = c1ProbDirac (0 : ℝ) := by
  apply Subtype.ext
  change (Measure.dirac (0,i)).map Prod.fst = Measure.dirac (0 : ℝ)
  simp

/-- The actual observation law at the origin is the original Gaussian noise. -/
theorem origin_observation_law :
    observationLaw (c1ProbDirac (0,0)).toMeasure actualSource observation 0 = noise := by
  unfold actualSource
  rw [observationLaw_factors noise visible measurable_visible hidden measurable_hidden,
    coordinate_point]
  unfold predictedLaw
  change fixedActionKernel (visibleKernel noise visible measurable_visible) 0 ∘ₘ Measure.dirac 0 = noise
  rw [Measure.dirac_bind (fixedActionKernel (visibleKernel noise visible measurable_visible) 0).measurable]
  change visibleKernel noise visible measurable_visible (0,0) = noise
  rw [visibleKernel, randomUpdate_apply]
  simp only [visible, zero_add]
  exact Measure.map_id

/-- Every individual observation here is null, despite a genuine probability
source and the actual measurable C1 recursion above. -/
theorem origin_singletons_are_null (y : ℝ) :
    observationLaw (c1ProbDirac (0,0)).toMeasure actualSource observation 0 {y} = 0 := by
  rw [origin_observation_law]
  have hn : NullSingletonClass noise := nullSingletonClass_gaussianReal (by norm_num)
  exact measure_singleton y

/-- Different hidden initial offsets have the same actual next observable
belief law. This is prediction transport, not hidden-state identification. -/
theorem hidden_aliases_same_actual_law :
    (c1BeliefTransitionKernel actualSource observation (c1ProbDirac (0,0),0)).map coordinate =
      (c1BeliefTransitionKernel actualSource observation (c1ProbDirac (0,1),0)).map coordinate := by
  rw [actual_C1_descends, actual_C1_descends, coordinate_point, coordinate_point]

/-- A genuinely different source: the hidden coordinate controls the next
visible value. It does not satisfy visible autonomy. -/
def leakingSource : Kernel ((ℝ × ℝ) × Unit) (ℝ × ℝ) :=
  Kernel.deterministic (fun u => (u.1.2,u.1.2)) (by fun_prop)
private instance leakingSource_isMarkov : IsMarkovKernel leakingSource := by
  unfold leakingSource
  infer_instance

private theorem leaking_observation (i : ℝ) :
    observationLaw (c1ProbDirac (0,i)).toMeasure leakingSource observation () = Measure.dirac i := by
  unfold observationLaw
  change Kernel.deterministic Prod.fst measurable_fst ∘ₘ _ = _
  rw [Measure.deterministic_comp_eq_map]
  unfold predictedLaw
  change (fixedActionKernel leakingSource () ∘ₘ Measure.dirac (0,i)).map Prod.fst = Measure.dirac i
  rw [Measure.dirac_bind (fixedActionKernel leakingSource ()).measurable]
  simp [fixedActionKernel, leakingSource, Kernel.comap_apply, Kernel.deterministic_apply]

/-- Observational-state equality alone cannot predict even the next observation
when the source leaks hidden information. This is a boundary to the positive
model class, not a claim that its autonomy condition is generally necessary. -/
theorem hidden_leak_has_no_observation_predictor :
    ¬ ∃ K : Kernel (ProbabilityMeasure ℝ × Unit) ℝ,
      ∀ (b : ProbabilityMeasure (ℝ × ℝ)) (a : Unit),
        observationLaw b.toMeasure leakingSource observation a = K (coordinate b,a) := by
  rintro ⟨K,hK⟩
  have h0 := hK (c1ProbDirac (0,0)) ()
  have h1 := hK (c1ProbDirac (0,1)) ()
  rw [leaking_observation, coordinate_point] at h0 h1
  have hd : Measure.dirac (0 : ℝ) = Measure.dirac 1 := h0.trans h1.symm
  have he := congrArg (fun μ : Measure ℝ => μ {0}) hd
  norm_num at he

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveSourceWitness
