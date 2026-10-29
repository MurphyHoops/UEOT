import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveSource

/-!
# Actual C1 recursion with a hidden-blind noisy or partial sensor

The source retains its explicit visible-autonomy restriction. The sensor is an
arbitrary Markov kernel on visible state/action; its microscopic lift is built
by projection. Neither posterior equivalence nor a desired quotient kernel is
an input. Their equality follows from the same joint law and uniqueness of
regular conditional probabilities, only observation-almost everywhere.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveSensor
open MeasureTheory ProbabilityTheory
open UEOT.V3.GeneralBayesPosterior
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure
open MeasurablePredictiveSource
open scoped ENNReal
noncomputable section

private theorem joint_projection {X Y W : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace W]
    (μ : Measure X) [SFinite μ] (q : X → Y) (hq : Measurable q)
    (O : Kernel Y W) [IsSFiniteKernel O] :
    (μ ⊗ₘ O.comap q hq).map (fun xw => (q xw.1,xw.2)) = μ.map q ⊗ₘ O := by
  have hm : Measurable (fun xw : X × W => (q xw.1,xw.2)) :=
    (hq.comp measurable_fst).prodMk measurable_snd
  ext s hs
  rw [Measure.map_apply hm hs, Measure.compProd_apply (hm hs), Measure.compProd_apply hs]
  simp only [Kernel.comap_apply]
  exact (lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hq).symm

variable {Y H A N W : Type*}
variable [MeasurableSpace Y] [MeasurableSpace H] [MeasurableSpace A]
variable [MeasurableSpace N] [MeasurableSpace W]

/-- The actual sensor sees the visible next state and the same action, and
cannot inspect the hidden next state. This is an explicit sufficient condition. -/
def liftedSensor (sensor : Kernel (Y × A) W) : Kernel ((Y × H) × A) W :=
  sensor.comap (fun xa => (xa.1.1,xa.2)) (measurable_fst.fst.prodMk measurable_snd)

instance liftedSensor_isMarkov (sensor : Kernel (Y × A) W) [IsMarkovKernel sensor] :
    IsMarkovKernel (liftedSensor (H := H) sensor) := by
  unfold liftedSensor
  infer_instance

private theorem fixed_liftedSensor (sensor : Kernel (Y × A) W) (a : A) :
    fixedActionKernel (liftedSensor (H := H) sensor) a =
      (fixedActionKernel sensor a).comap Prod.fst measurable_fst := rfl

variable [StandardBorelSpace Y] [StandardBorelSpace H] [MeasurableSpace.CountablyGenerated W]
variable [Nonempty Y] [Nonempty H]
variable (noise : Measure N) [IsProbabilityMeasure noise]
variable (visible : (Y × A) × N → Y) (hv : Measurable visible)
variable (hidden : ((Y × H) × A) × N → H) (hh : Measurable hidden)
variable (sensor : Kernel (Y × A) W) [IsMarkovKernel sensor]

omit [Nonempty Y] [Nonempty H] in
private theorem predicted_projection (b : ProbabilityMeasure (Y × H)) (a : A) :
    (predictedLaw b.toMeasure (source noise visible hv hidden hh) a).map Prod.fst =
      predictedLaw (coordinate b).toMeasure (visibleKernel noise visible hv) a := by
  have h := observationLaw_factors noise visible hv hidden hh b a
  change (Kernel.deterministic Prod.fst measurable_fst ∘ₘ
    predictedLaw b.toMeasure (source noise visible hv hidden hh) a) = _ at h
  rwa [Measure.deterministic_comp_eq_map measurable_fst] at h

omit [MeasurableSpace.CountablyGenerated W] [IsMarkovKernel sensor] [Nonempty Y] [Nonempty H] in
/-- The noisy observation law is computed from the same source marginal. -/
theorem sensor_observationLaw_factors (b : ProbabilityMeasure (Y × H)) (a : A) :
    observationLaw b.toMeasure (source noise visible hv hidden hh) (liftedSensor sensor) a =
      observationLaw (coordinate b).toMeasure (visibleKernel noise visible hv) sensor a := by
  rw [observationLaw, fixed_liftedSensor, observationLaw, ← predicted_projection noise visible hv hidden hh b a]
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp only [Kernel.comap_apply]
  exact (lintegral_map ((fixedActionKernel sensor a).measurable_coe hs) measurable_fst).symm

omit [MeasurableSpace.CountablyGenerated W] [Nonempty Y] [Nonempty H] in
private theorem sensor_joint_projection (b : ProbabilityMeasure (Y × H)) (a : A) :
    (jointLaw b.toMeasure (source noise visible hv hidden hh) (liftedSensor sensor) a).map
      (fun xw => (xw.1.1,xw.2)) =
        jointLaw (coordinate b).toMeasure (visibleKernel noise visible hv) sensor a := by
  rw [jointLaw, fixed_liftedSensor, joint_projection, predicted_projection, jointLaw]

/-- The ACTUAL common posterior versions commute with visible projection,
observation-a.e. This follows from their existing joint-law factorizations. -/
theorem actual_posterior_coordinate_ae (b : ProbabilityMeasure (Y × H)) (a : A) :
    ∀ᵐ w ∂observationLaw b.toMeasure (source noise visible hv hidden hh) (liftedSensor sensor) a,
      coordinate (c1ParametricPosteriorBelief (source noise visible hv hidden hh)
        (liftedSensor sensor) ((b,a),w)) =
      c1ParametricPosteriorBelief (visibleKernel noise visible hv) sensor ((coordinate b,a),w) := by
  have : IsProbabilityMeasure (observationLaw b.toMeasure (source noise visible hv hidden hh)
      (liftedSensor sensor) a) := by
    unfold observationLaw
    infer_instance
  let micro := c1PosteriorSection (source noise visible hv hidden hh) (liftedSensor sensor) b a
  let coarse := c1PosteriorSection (visibleKernel noise visible hv) sensor (coordinate b) a
  have hfac :
      observationLaw b.toMeasure (source noise visible hv hidden hh) (liftedSensor sensor) a ⊗ₘ
        micro.map Prod.fst =
      observationLaw b.toMeasure (source noise visible hv hidden hh) (liftedSensor sensor) a ⊗ₘ coarse := by
    rw [Measure.compProd_map measurable_fst]
    change (observationLaw b.toMeasure (source noise visible hv hidden hh) (liftedSensor sensor) a ⊗ₘ
      c1PosteriorSection (source noise visible hv hidden hh) (liftedSensor sensor) b a).map _ = _
    rw [c1PosteriorSection_factorization, sensor_observationLaw_factors,
      c1PosteriorSection_factorization]
    rw [Measure.map_map (measurable_id.prodMap measurable_fst) measurable_swap]
    have hm : Measurable (fun xw : (Y × H) × W => (xw.1.1,xw.2)) :=
      measurable_fst.fst.prodMk measurable_snd
    rw [← sensor_joint_projection noise visible hv hidden hh sensor b a,
      Measure.map_map measurable_swap hm]
    rfl
  have hae := Kernel.ae_eq_of_compProd_eq hfac
  filter_upwards [hae] with w hw
  apply Subtype.ext
  change (c1ParametricPosteriorKernel (source noise visible hv hidden hh)
    (liftedSensor sensor) ((b,a),w)).map Prod.fst =
      c1ParametricPosteriorKernel (visibleKernel noise visible hv) sensor ((coordinate b,a),w)
  simpa only [micro, coarse, c1PosteriorSection, Kernel.comap_apply, Function.comp_def,
    Kernel.map_apply _ measurable_fst] using hw

/-- A noisy or partial sensor retains the full coarse C1 recursion, including
non-Dirac updates;
no separately assumed posterior, belief kernel or image factor is required. -/
theorem actual_C1_recursion (b : ProbabilityMeasure (Y × H)) (a : A) :
    (c1BeliefTransitionKernel (source noise visible hv hidden hh) (liftedSensor sensor) (b,a)).map
      coordinate =
    c1BeliefTransitionKernel (visibleKernel noise visible hv) sensor (coordinate b,a) := by
  have hpost : Measurable (fun w => c1ParametricPosteriorBelief
      (source noise visible hv hidden hh) (liftedSensor sensor) ((b,a),w)) :=
    (measurable_c1ParametricPosteriorBelief _ _).comp (measurable_const.prodMk measurable_id)
  rw [c1BeliefTransitionKernel_apply_eq_map, Measure.map_map measurable_coordinate hpost,
    c1BeliefTransitionKernel_apply_eq_map]
  calc
    _ = (observationLaw b.toMeasure (source noise visible hv hidden hh) (liftedSensor sensor) a).map
      (fun w => c1ParametricPosteriorBelief (visibleKernel noise visible hv) sensor ((coordinate b,a),w)) :=
        Measure.map_congr (actual_posterior_coordinate_ae noise visible hv hidden hh sensor b a)
    _ = _ := by rw [sensor_observationLaw_factors]

/-- The same observable-belief policy remains compatible with the noisy
sensor recursion. This uses existing kernel composition directly. -/
theorem same_policy_controlled_recursion
    (policy : Kernel (ProbabilityMeasure Y) A) [IsMarkovKernel policy]
    (b : ProbabilityMeasure (Y × H)) :
    (Kernel.snd ((policy.comap coordinate measurable_coordinate) ⊗ₖ
      c1BeliefTransitionKernel (source noise visible hv hidden hh) (liftedSensor sensor)) b).map
        coordinate =
      Kernel.snd (policy ⊗ₖ c1BeliefTransitionKernel (visibleKernel noise visible hv) sensor)
        (coordinate b) := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply measurable_coordinate hs,
    Kernel.snd_apply' _ _ (measurable_coordinate hs),
    Kernel.compProd_apply (measurable_snd (measurable_coordinate hs)),
    Kernel.snd_apply' _ _ hs, Kernel.compProd_apply (measurable_snd hs)]
  simp only [Kernel.comap_apply]
  change (∫⁻ a, c1BeliefTransitionKernel (source noise visible hv hidden hh) (liftedSensor sensor)
    (b,a) (coordinate ⁻¹' s) ∂policy (coordinate b)) =
      ∫⁻ a, c1BeliefTransitionKernel (visibleKernel noise visible hv) sensor (coordinate b,a) s
        ∂policy (coordinate b)
  apply lintegral_congr
  intro a
  rw [← Measure.map_apply measurable_coordinate hs]
  exact congrArg (fun μ : Measure (ProbabilityMeasure Y) => μ s)
    (actual_C1_recursion noise visible hv hidden hh sensor b a)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveSensor
