import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.C1ParametricBelief
import Mathlib

/-!
# A general measurable predictive source from primitive shared-noise dynamics

Visible and hidden coordinates are Standard Borel. A visible update depends
on the visible state, action and fresh source noise; a hidden update may depend
on every microscopic coordinate and the SAME noise. The visible autonomy is
an explicit model restriction, not a universal necessity claim. The source
kernel, full probability-valued coordinate and its measurable section are
constructed. Actual C1 posterior versions are used only observation-a.e.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveSource
open MeasureTheory ProbabilityTheory
open UEOT.V3.GeneralBayesPosterior
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure
open scoped ENNReal
noncomputable section

section PrimitiveUpdate
variable {I N Z : Type*} [MeasurableSpace I] [MeasurableSpace N] [MeasurableSpace Z]

/-- A primitive source update driven by its declared probability noise law. -/
def randomUpdate (noise : Measure N) (update : I × N → Z) (hu : Measurable update) :
    Kernel I Z :=
  Kernel.snd ((Kernel.const I noise) ⊗ₖ Kernel.deterministic update hu)

instance randomUpdate_isMarkov (noise : Measure N) [IsProbabilityMeasure noise]
    (update : I × N → Z) (hu : Measurable update) :
    IsMarkovKernel (randomUpdate noise update hu) := by
  unfold randomUpdate
  infer_instance

/-- The sampled source really executes the given update function. -/
theorem randomUpdate_apply (noise : Measure N) [IsProbabilityMeasure noise]
    (update : I × N → Z) (hu : Measurable update) [MeasurableSingletonClass Z] (i : I) :
    randomUpdate noise update hu i = noise.map (fun n => update (i,n)) := by
  apply Measure.ext
  intro s hs
  have hm : Measurable (fun n => update (i,n)) := hu.comp measurable_prodMk_left
  rw [randomUpdate, Kernel.snd_apply' _ _ hs,
    Kernel.compProd_deterministic_apply hu (measurable_snd hs), Kernel.const_apply,
    Measure.map_apply hm hs]
  rfl
end PrimitiveUpdate

variable {Y H A N : Type*}
variable [MeasurableSpace Y] [MeasurableSpace H] [MeasurableSpace A] [MeasurableSpace N]

/-- The same noise drives both coordinates. Only the visible update is
restricted to the visible information; the hidden mechanism remains arbitrary. -/
def microscopicUpdate (visible : (Y × A) × N → Y)
    (hidden : ((Y × H) × A) × N → H) (u : ((Y × H) × A) × N) : Y × H :=
  (visible ((u.1.1.1,u.1.2),u.2), hidden u)

@[fun_prop] theorem measurable_microscopicUpdate
    (visible : (Y × A) × N → Y) (hv : Measurable visible)
    (hidden : ((Y × H) × A) × N → H) (hh : Measurable hidden) :
    Measurable (microscopicUpdate visible hidden) :=
  (hv.comp ((measurable_fst.fst.fst.prodMk measurable_fst.snd).prodMk measurable_snd)).prodMk hh

/-- Actual microscopic controlled dynamics, constructed before any quotient. -/
def source (noise : Measure N) (visible : (Y × A) × N → Y) (hv : Measurable visible)
    (hidden : ((Y × H) × A) × N → H) (hh : Measurable hidden) :
    Kernel ((Y × H) × A) (Y × H) :=
  randomUpdate noise (microscopicUpdate visible hidden) (measurable_microscopicUpdate visible hv hidden hh)

instance source_isMarkov (noise : Measure N) [IsProbabilityMeasure noise]
    (visible : (Y × A) × N → Y) (hv : Measurable visible)
    (hidden : ((Y × H) × A) × N → H) (hh : Measurable hidden) :
    IsMarkovKernel (source noise visible hv hidden hh) := by
  unfold source
  infer_instance

/-- Visible dynamics derived from the same primitive noise/update. This is not
an independently supplied desired quotient kernel. -/
def visibleKernel (noise : Measure N) (visible : (Y × A) × N → Y) (hv : Measurable visible) :
    Kernel (Y × A) Y := randomUpdate noise visible hv

instance visibleKernel_isMarkov (noise : Measure N) [IsProbabilityMeasure noise]
    (visible : (Y × A) × N → Y) (hv : Measurable visible) :
    IsMarkovKernel (visibleKernel noise visible hv) := by unfold visibleKernel; infer_instance

/-- Full observable probability state; no binary coordinate or guessed Borel
image is used. -/
def coordinate (b : ProbabilityMeasure (Y × H)) : ProbabilityMeasure Y :=
  b.map measurable_fst.aemeasurable

@[fun_prop] theorem measurable_coordinate :
    Measurable (coordinate : ProbabilityMeasure (Y × H) → ProbabilityMeasure Y) := by
  apply Measurable.subtype_mk
  exact (Measure.measurable_map Prod.fst measurable_fst).comp measurable_subtype_coe

/-- An explicit measurable section on the ENTIRE probability-law space. -/
def liftBelief (reference : H) (b : ProbabilityMeasure Y) : ProbabilityMeasure (Y × H) :=
  b.map (f := fun y => (y,reference)) (measurable_id.prodMk measurable_const).aemeasurable

@[fun_prop] theorem measurable_liftBelief (reference : H) :
    Measurable (liftBelief (Y := Y) reference) := by
  apply Measurable.subtype_mk
  exact (Measure.measurable_map (fun y => (y,reference)) (measurable_id.prodMk measurable_const)).comp
    measurable_subtype_coe

/-- The image and section obligations are theorems of the split source model. -/
theorem coordinate_liftBelief (reference : H) (b : ProbabilityMeasure Y) :
    coordinate (liftBelief reference b) = b := by
  apply Subtype.ext
  change (b.toMeasure.map (fun y => (y,reference))).map Prod.fst = b.toMeasure
  have hm : Measurable (fun y : Y => (y,reference)) := measurable_id.prodMk measurable_const
  rw [Measure.map_map measurable_fst hm]
  exact Measure.map_id

theorem coordinate_surjective (reference : H) :
    Function.Surjective (coordinate : ProbabilityMeasure (Y × H) → ProbabilityMeasure Y) :=
  fun b => ⟨liftBelief reference b, coordinate_liftBelief reference b⟩

/-- A visible safety event transports exactly; hidden events are not claimed. -/
theorem visible_event_probability (b : ProbabilityMeasure (Y × H))
    (s : Set Y) (hs : MeasurableSet s) :
    b.toMeasure (Prod.fst ⁻¹' s) = (coordinate b).toMeasure s :=
  (Measure.map_apply measurable_fst hs).symm

/-- Registered integrable rewards of the visible state preserve expectation. -/
theorem visible_reward_expectation (b : ProbabilityMeasure (Y × H)) (reward : Y → ℝ)
    (hreward : Integrable reward (coordinate b).toMeasure) :
    (∫ x, reward x.1 ∂b.toMeasure) = ∫ y, reward y ∂(coordinate b).toMeasure := by
  exact (integral_map measurable_fst.aemeasurable hreward.aestronglyMeasurable).symm

/-- Registered measurable future observation events. This stores no response
or closure assumption, just the legal observation sigma-algebra. -/
abbrev TestEvent (Y : Type*) [MeasurableSpace Y] := {s : Set Y // MeasurableSet s}

/-- Finite continuation cylinders are generated by prefixing a real source
transition and a registered measurable observation event. -/
def testResponse {Z : Type*} [MeasurableSpace Z] (K : Kernel (Z × A) Z) (q : Z → Y) :
    List (A × TestEvent Y) → Z → ℝ≥0∞
  | [], _ => 1
  | (a,s) :: word, x => ∫⁻ z, (q ⁻¹' s.val).indicator (testResponse K q word) z ∂K (x,a)

theorem measurable_testResponse {Z : Type*} [MeasurableSpace Z]
    (K : Kernel (Z × A) Z) [IsMarkovKernel K] (q : Z → Y) (hq : Measurable q)
    (word : List (A × TestEvent Y)) : Measurable (testResponse K q word) := by
  induction word with
  | nil => exact measurable_const
  | cons ao word ih =>
      exact ((ih.indicator (ao.2.property.preimage hq)).lintegral_kernel).comp
        (measurable_id.prodMk measurable_const)

/-- The actual source observation reads its visible coordinate. -/
def observation : Kernel ((Y × H) × A) Y :=
  Kernel.deterministic (fun u => u.1.1) measurable_fst.fst

instance observation_isMarkov : IsMarkovKernel (observation (Y := Y) (H := H) (A := A)) := by
  unfold observation
  infer_instance

private theorem fixed_observation (a : A) :
    fixedActionKernel (observation (Y := Y) (H := H) (A := A)) a =
      Kernel.deterministic Prod.fst measurable_fst := rfl

variable [StandardBorelSpace Y] [StandardBorelSpace H] [Nonempty Y] [Nonempty H]
variable (noise : Measure N) [IsProbabilityMeasure noise]
variable (visible : (Y × A) × N → Y) (hv : Measurable visible)
variable (hidden : ((Y × H) × A) × N → H) (hh : Measurable hidden)

omit [Nonempty Y] [Nonempty H] in
/-- Source-row descent follows from the primitive update, rather than an
assumed block-mass or posterior-kernel equality. -/
theorem source_projection (x : Y × H) (a : A) :
    (source noise visible hv hidden hh (x,a)).map Prod.fst = visibleKernel noise visible hv (x.1,a) := by
  have hm : Measurable (fun n => microscopicUpdate visible hidden ((x,a),n)) :=
    (measurable_microscopicUpdate visible hv hidden hh).comp measurable_prodMk_left
  rw [source, randomUpdate_apply, Measure.map_map measurable_fst hm,
    visibleKernel, randomUpdate_apply]
  rfl

omit [StandardBorelSpace Y] [StandardBorelSpace H] [Nonempty Y] [Nonempty H]
  [IsProbabilityMeasure noise] in
private theorem observationLaw_eq_map (b : ProbabilityMeasure (Y × H)) (a : A) :
    observationLaw b.toMeasure (source noise visible hv hidden hh) observation a =
      (predictedLaw b.toMeasure (source noise visible hv hidden hh) a).map Prod.fst := by
  rw [observationLaw]
  change Kernel.deterministic Prod.fst measurable_fst ∘ₘ _ = _
  exact Measure.deterministic_comp_eq_map measurable_fst

omit [Nonempty Y] [Nonempty H] in
/-- The predictive observation law depends on the computed observable belief
alone, for every probability input and every allowed action. -/
theorem observationLaw_factors (b : ProbabilityMeasure (Y × H)) (a : A) :
    observationLaw b.toMeasure (source noise visible hv hidden hh) observation a =
      predictedLaw (coordinate b).toMeasure (visibleKernel noise visible hv) a := by
  rw [observationLaw_eq_map, predictedLaw, Measure.map_comp b.toMeasure
    (fixedActionKernel (source noise visible hv hidden hh) a) measurable_fst]
  apply Measure.ext
  intro s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp only [Kernel.map_apply _ measurable_fst, fixedActionKernel, Kernel.comap_apply]
  simp_rw [source_projection]
  change _ = (fixedActionKernel (visibleKernel noise visible hv) a ∘ₘ b.toMeasure.map Prod.fst) s
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  exact (lintegral_map ((fixedActionKernel (visibleKernel noise visible hv) a).measurable_coe hs)
    measurable_fst).symm

/-- Null observations carry only their legitimate observation-a.e. identity. -/
theorem posterior_coordinate_ae (b : ProbabilityMeasure (Y × H)) (a : A) :
    ∀ᵐ y ∂observationLaw b.toMeasure (source noise visible hv hidden hh) observation a,
      coordinate (c1ParametricPosteriorBelief (source noise visible hv hidden hh) observation ((b,a),y)) =
        c1ProbDirac y := by
  have hpost := c1ParametricPosteriorKernel_ae_eq_existing
    (source noise visible hv hidden hh) observation b a
  have hdet := deterministic_comp_posterior
    (μ := predictedLaw b.toMeasure (source noise visible hv hidden hh) a) measurable_fst
  rw [← observationLaw_eq_map noise visible hv hidden hh b a] at hdet
  filter_upwards [hpost, hdet] with y hy hd
  apply Subtype.ext
  change (c1ParametricPosteriorKernel (source noise visible hv hidden hh) observation ((b,a),y)).map
    Prod.fst = Measure.dirac y
  rw [hy]
  simpa only [posteriorKernel, fixed_observation, Kernel.deterministic_comp_eq_map measurable_fst,
    Kernel.map_apply _ measurable_fst, Kernel.id_apply] using hd

/-- Actual C1 belief recursion descends to full observable probability states. -/
theorem actual_kernel_coordinate_law (b : ProbabilityMeasure (Y × H)) (a : A) :
    (c1BeliefTransitionKernel (source noise visible hv hidden hh) observation (b,a)).map coordinate =
      (predictedLaw (coordinate b).toMeasure (visibleKernel noise visible hv) a).map c1ProbDirac := by
  have hpostMeas : Measurable (fun y =>
      c1ParametricPosteriorBelief (source noise visible hv hidden hh) observation ((b,a),y)) :=
    (measurable_c1ParametricPosteriorBelief _ _).comp (measurable_const.prodMk measurable_id)
  calc
    _ = (observationLaw b.toMeasure (source noise visible hv hidden hh) observation a).map c1ProbDirac := by
      rw [c1BeliefTransitionKernel_apply_eq_map, Measure.map_map measurable_coordinate hpostMeas]
      apply Measure.map_congr
      exact posterior_coordinate_ae noise visible hv hidden hh b a
    _ = _ := by rw [observationLaw_factors]

/-- The measurable quotient is constructed from the actual source kernel at
its explicit probability-valued section, not supplied as an input. -/
def quotientKernel (reference : H) : Kernel (ProbabilityMeasure Y × A) (ProbabilityMeasure Y) :=
  ((c1BeliefTransitionKernel (source noise visible hv hidden hh) observation).comap
    (fun ba => (liftBelief reference ba.1,ba.2))
    (((measurable_liftBelief reference).comp measurable_fst).prodMk measurable_snd)).map coordinate

instance quotientKernel_isMarkov (reference : H) :
    IsMarkovKernel (quotientKernel noise visible hv hidden hh reference) := by
  unfold quotientKernel
  exact Kernel.IsMarkovKernel.map _ measurable_coordinate

/-- This is the actual downstream C1 consumer: one common jointly measurable
Markov quotient for every input belief/action in this general source class. -/
theorem quotientKernel_factor (reference : H) (b : ProbabilityMeasure (Y × H)) (a : A) :
    (c1BeliefTransitionKernel (source noise visible hv hidden hh) observation (b,a)).map coordinate =
      quotientKernel noise visible hv hidden hh reference (coordinate b,a) := by
  simp only [quotientKernel, Kernel.map_apply _ measurable_coordinate, Kernel.comap_apply]
  rw [actual_kernel_coordinate_law, actual_kernel_coordinate_law,
    coordinate_liftBelief]

/-- A measurable observable-belief policy is lifted through the proved
coordinate; it cannot inspect the hidden coordinate or a different posterior. -/
def controlledActual (policy : Kernel (ProbabilityMeasure Y) A) :
    Kernel (ProbabilityMeasure (Y × H)) (ProbabilityMeasure (Y × H)) :=
  Kernel.snd ((policy.comap coordinate measurable_coordinate) ⊗ₖ
    c1BeliefTransitionKernel (source noise visible hv hidden hh) observation)

/-- The same action policy drives the constructed observable quotient. -/
def controlledQuotient (reference : H) (policy : Kernel (ProbabilityMeasure Y) A) :
    Kernel (ProbabilityMeasure Y) (ProbabilityMeasure Y) :=
  Kernel.snd (policy ⊗ₖ quotientKernel noise visible hv hidden hh reference)

instance controlledActual_isMarkov (policy : Kernel (ProbabilityMeasure Y) A) [IsMarkovKernel policy] :
    IsMarkovKernel (controlledActual noise visible hv hidden hh policy) := by
  unfold controlledActual
  infer_instance

instance controlledQuotient_isMarkov (reference : H) (policy : Kernel (ProbabilityMeasure Y) A)
    [IsMarkovKernel policy] :
    IsMarkovKernel (controlledQuotient noise visible hv hidden hh reference policy) := by
  unfold controlledQuotient
  infer_instance

/-- Controlled compatibility is derived for the SAME observable-belief policy
and actual C1 recursion. No assumption of a controlled quotient is required. -/
theorem controlled_factor (reference : H) (policy : Kernel (ProbabilityMeasure Y) A)
    [IsMarkovKernel policy] (b : ProbabilityMeasure (Y × H)) :
    (controlledActual noise visible hv hidden hh policy b).map coordinate =
      controlledQuotient noise visible hv hidden hh reference policy (coordinate b) := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply measurable_coordinate hs, controlledActual,
    Kernel.snd_apply' _ _ (measurable_coordinate hs),
    Kernel.compProd_apply (measurable_snd (measurable_coordinate hs)),
    controlledQuotient, Kernel.snd_apply' _ _ hs, Kernel.compProd_apply (measurable_snd hs)]
  simp only [Kernel.comap_apply]
  change (∫⁻ a, c1BeliefTransitionKernel (source noise visible hv hidden hh) observation
    (b,a) (coordinate ⁻¹' s) ∂policy (coordinate b)) =
      ∫⁻ a, quotientKernel noise visible hv hidden hh reference (coordinate b,a) s ∂policy (coordinate b)
  apply lintegral_congr
  intro a
  rw [← Measure.map_apply measurable_coordinate hs]
  exact congrArg (fun μ : Measure (ProbabilityMeasure Y) => μ s)
    (quotientKernel_factor noise visible hv hidden hh reference b a)

/-- Uniqueness is on the entire observable-law space, supplied by the proved
section/surjectivity rather than a postulated Borel image. -/
theorem quotientKernel_unique (reference : H)
    (K : Kernel (ProbabilityMeasure Y × A) (ProbabilityMeasure Y))
    (hK : ∀ (b : ProbabilityMeasure (Y × H)) (a : A),
      (c1BeliefTransitionKernel (source noise visible hv hidden hh) observation (b,a)).map coordinate =
        K (coordinate b,a)) : K = quotientKernel noise visible hv hidden hh reference := by
  ext ⟨b,a⟩ s _hs
  have h1 := hK (liftBelief reference b) a
  have h2 := quotientKernel_factor noise visible hv hidden hh reference (liftBelief reference b) a
  rw [coordinate_liftBelief] at h1 h2
  exact congrArg (fun μ : Measure (ProbabilityMeasure Y) => μ s) (h1.symm.trans h2)

omit [Nonempty Y] [Nonempty H] in
/-- Closure under every finite measurable observation continuation is DERIVED
from the primitive source update; it is not a separate ClosedTests premise. -/
theorem continuation_tests_factor (word : List (A × TestEvent Y)) (x : Y × H) :
    testResponse (source noise visible hv hidden hh) Prod.fst word x =
      testResponse (visibleKernel noise visible hv) id word x.1 := by
  induction word generalizing x with
  | nil => rfl
  | cons ao word ih =>
      let g := ao.2.val.indicator (testResponse (visibleKernel noise visible hv) id word)
      have hg : Measurable g :=
        (measurable_testResponse (visibleKernel noise visible hv) id measurable_id word).indicator ao.2.property
      calc
        _ = ∫⁻ z, g z.1 ∂source noise visible hv hidden hh (x,ao.1) := by
          apply lintegral_congr
          intro z
          by_cases hz : z.1 ∈ ao.2.val <;> simp [Set.indicator, hz, g, ih]
        _ = ∫⁻ y, g y ∂(source noise visible hv hidden hh (x,ao.1)).map Prod.fst :=
          (lintegral_map hg measurable_fst).symm
        _ = _ := by rw [source_projection]; rfl

omit [Nonempty Y] [Nonempty H] in
/-- The computed observable law controls all these future test probabilities. -/
theorem same_coordinate_same_tests (b b' : ProbabilityMeasure (Y × H))
    (h : coordinate b = coordinate b') (word : List (A × TestEvent Y)) :
    (∫⁻ x, testResponse (source noise visible hv hidden hh) Prod.fst word x ∂b.toMeasure) =
      ∫⁻ x, testResponse (source noise visible hv hidden hh) Prod.fst word x ∂b'.toMeasure := by
  have hresponse : testResponse (source noise visible hv hidden hh) Prod.fst word =
      fun x => testResponse (visibleKernel noise visible hv) id word x.1 :=
    funext (continuation_tests_factor noise visible hv hidden hh word)
  have hm := measurable_testResponse (visibleKernel noise visible hv) id measurable_id word
  rw [hresponse, ← lintegral_map hm measurable_fst, ← lintegral_map hm measurable_fst]
  exact congrArg (fun μ : Measure Y => ∫⁻ y, testResponse (visibleKernel noise visible hv) id word y ∂μ)
    (congrArg (fun μ : ProbabilityMeasure Y => μ.toMeasure) h)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveSource
