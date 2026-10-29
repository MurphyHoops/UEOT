import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveSensor

/-!
# A genuinely uncertain, observation-dependent C1 posterior

A fresh fair Bool source is observed through a channel with correctness 3/4.
Both observations have positive mass. The ACTUAL common C1 posterior assigns
true probability 3/4 after true and 1/4 after false, so neither is Dirac and
the posterior is not a constant known state.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveSensorWitness
open MeasureTheory ProbabilityTheory
open UEOT.V3.GeneralBayesPosterior
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure
open MeasurablePredictiveSource MeasurablePredictiveSensor
open scoped ENNReal
noncomputable section

private def coin (p : ℝ≥0∞) (_hp : p ≤ 1) : Measure Bool :=
  p • Measure.dirac true + (1-p) • Measure.dirac false
private instance (p : ℝ≥0∞) (hp : p ≤ 1) : IsProbabilityMeasure (coin p hp) := by
  rw [isProbabilityMeasure_iff]
  simpa [coin] using add_tsub_cancel_of_le hp

private theorem coin_singleton (p : ℝ≥0∞) (hp : p ≤ 1) (b : Bool) :
    coin p hp {b} = if b then p else 1 - p := by
  cases b <;> simp [coin]

private def noise : Measure Bool := coin (1/2) (by norm_num)
private instance : IsProbabilityMeasure noise := by unfold noise; infer_instance
private def visible (u : (Bool × Unit) × Bool) : Bool := u.2
private theorem hv : Measurable visible := measurable_snd
private def hidden (_ : ((Bool × Unit) × Unit) × Bool) : Unit := ()
private theorem hh : Measurable hidden := measurable_const

/-- Actual hidden-blind noisy observation mechanism. -/
def sensor : Kernel (Bool × Unit) Bool where
  toFun ba := coin (if ba.1 then 3/4 else 1/4) (by
    split <;> norm_num [ENNReal.div_le_iff (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num : (4 : ℝ≥0∞) ≠ ∞)])
  measurable' := measurable_of_countable _
instance : IsMarkovKernel sensor where
  isProbabilityMeasure ba := by dsimp [sensor]; infer_instance

def prior : ProbabilityMeasure (Bool × Unit) := c1ProbDirac (false,())
def coarsePrior : ProbabilityMeasure Bool := coordinate prior
def visibleDynamics : Kernel (Bool × Unit) Bool := visibleKernel noise visible hv
private instance : IsMarkovKernel visibleDynamics := by unfold visibleDynamics; infer_instance

private theorem source_row (x : Bool) : fixedActionKernel visibleDynamics () x = noise := by
  change visibleKernel noise visible hv (x,()) = noise
  rw [visibleKernel, randomUpdate_apply]
  exact Measure.map_id

private theorem prediction : predictedLaw coarsePrior.toMeasure visibleDynamics () = noise := by
  have heq : fixedActionKernel visibleDynamics () = Kernel.const Bool noise := by ext1 x; exact source_row x
  rw [predictedLaw, heq, Measure.const_comp]
  rw [measure_univ, one_smul]

private theorem sensor_mass (x w : Bool) :
    fixedActionKernel sensor () x {w} =
      if x = w then (3/4 : ℝ≥0∞) else 1/4 := by
  change coin (if x then 3/4 else 1/4) (by
    split <;> norm_num [ENNReal.div_le_iff (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num : (4 : ℝ≥0∞) ≠ ∞)]) {w} = _
  rw [coin_singleton]
  cases x <;> cases w <;> simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
  all_goals apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  all_goals try rw [ENNReal.toReal_sub_of_le
    (by norm_num [ENNReal.div_le_iff (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num : (4 : ℝ≥0∞) ≠ ∞)]) (by norm_num)]
  all_goals norm_num [ENNReal.toReal_div]

private theorem noise_mass (x : Bool) : noise {x} = (1/2 : ℝ≥0∞) := by
  rw [noise, coin_singleton]
  cases x <;> norm_num

private theorem observation_mass (w : Bool) :
    observationLaw coarsePrior.toMeasure visibleDynamics sensor () {w} = (1/2 : ℝ≥0∞) := by
  rw [observationLaw, prediction, Measure.bind_apply (measurableSet_singleton _) (Kernel.aemeasurable _)]
  rw [lintegral_fintype]
  simp only [Fintype.sum_bool, noise_mass, sensor_mass]
  cases w <;> simp only [Bool.false_eq_true, ↓reduceIte]
  all_goals apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  all_goals rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  all_goals norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]

private theorem joint_mass (w : Bool) :
    jointLaw coarsePrior.toMeasure visibleDynamics sensor () ({true} ×ˢ {w}) =
      if w then (3/8 : ℝ≥0∞) else 1/8 := by
  rw [jointLaw, prediction, Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _)]
  rw [lintegral_singleton]
  rw [noise_mass, sensor_mass]
  cases w <;> simp only [Bool.false_eq_true, ↓reduceIte]
  all_goals apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  all_goals norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]

/-- Scalar Bayes identity derived from the actual common C1 factorization. -/
theorem actual_posterior_true_mass (w : Bool) :
    (c1ParametricPosteriorBelief visibleDynamics sensor ((coarsePrior,()),w)).toMeasure {true} =
      if w then (3/4 : ℝ≥0∞) else 1/4 := by
  have hfac := c1PosteriorSection_factorization visibleDynamics sensor coarsePrior ()
  have h := congrArg (fun μ : Measure (Bool × Bool) => μ ({w} ×ˢ {true})) hfac
  rw [Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _),
    lintegral_singleton, observation_mass,
    Measure.map_apply measurable_swap ((measurableSet_singleton _).prod (measurableSet_singleton _))] at h
  have hset : Prod.swap ⁻¹' ({w} ×ˢ {true}) = ({true} ×ˢ {w}) := by ext ⟨x,y⟩; simp [and_comm]
  rw [hset, joint_mass] at h
  change (c1ParametricPosteriorBelief visibleDynamics sensor ((coarsePrior,()),w)).toMeasure {true} * (1/2 : ℝ≥0∞) = _ at h
  cases w <;> simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  all_goals apply (ENNReal.mul_left_inj (c := (1/2 : ℝ≥0∞)) (by norm_num) (by norm_num)).mp
  all_goals refine h.trans ?_
  all_goals apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  all_goals norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]

/-- Every possible observation leaves genuine latent uncertainty. -/
theorem actual_posterior_not_dirac (w z : Bool) :
    c1ParametricPosteriorBelief visibleDynamics sensor ((coarsePrior,()),w) ≠ c1ProbDirac z := by
  intro heq
  have h := congrArg (fun b : ProbabilityMeasure Bool => (b.toMeasure {true}).toReal) heq
  rw [actual_posterior_true_mass] at h
  cases w <;> cases z <;> norm_num [c1ProbDirac, ENNReal.toReal_div] at h

/-- The actual posterior responds to the observation, rather than returning
a single fixed uncertain law for every observation. -/
theorem actual_posterior_changes :
    c1ParametricPosteriorBelief visibleDynamics sensor ((coarsePrior,()),true) ≠
      c1ParametricPosteriorBelief visibleDynamics sensor ((coarsePrior,()),false) := by
  intro heq
  have h := congrArg (fun b : ProbabilityMeasure Bool => (b.toMeasure {true}).toReal) heq
  rw [actual_posterior_true_mass, actual_posterior_true_mass] at h
  norm_num [ENNReal.toReal_div] at h

/-- Direct consumption by the actual microscopic C1 recursion. -/
theorem witness_actual_C1_recursion :
    (c1BeliefTransitionKernel (source noise visible hv hidden hh) (liftedSensor sensor) (prior,())).map
        coordinate = c1BeliefTransitionKernel visibleDynamics sensor (coarsePrior,()) :=
  actual_C1_recursion noise visible hv hidden hh sensor prior ()

/-- Actual microscopic posterior versions retain this uncertainty on the
legitimate observation-a.e. domain. -/
theorem microscopic_posterior_uncertain_ae :
    ∀ᵐ w ∂observationLaw prior.toMeasure (source noise visible hv hidden hh) (liftedSensor sensor) (),
      ∀ z : Bool, coordinate (c1ParametricPosteriorBelief (source noise visible hv hidden hh)
        (liftedSensor sensor) ((prior,()),w)) ≠ c1ProbDirac z := by
  filter_upwards [actual_posterior_coordinate_ae noise visible hv hidden hh sensor prior ()] with w hw
  intro z
  rw [hw]
  exact actual_posterior_not_dirac w z

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveSensorWitness
