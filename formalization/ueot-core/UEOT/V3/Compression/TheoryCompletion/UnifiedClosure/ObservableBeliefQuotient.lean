import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.C1ParametricBelief
import Mathlib

/-!
# A binary generating-test quotient of the actual C1 belief kernel

A known measurable observation q and its two explicit representatives define
one probability coordinate. Its image is the closed interval [0,1], with a
measurable two-Dirac section. Closure of the original source's two fibre tests
is equivalent to a unique measurable Markov quotient of the existing C1
posterior-belief kernel for every input belief. The target kernel is constructed
from that source, rather than supplied as a premise. Common-version identities
are used only observation-almost everywhere. Finite source-test expectations,
reward and safety bridges retain their distinct contracts. No general Borel
image, minimal-memory or arbitrary control-objective claim is made here.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ObservableBeliefQuotient

open MeasureTheory ProbabilityTheory
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure
open UEOT.V3.GeneralBayesPosterior
open scoped ENNReal

noncomputable section

variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

def coordinate (q : X → Bool) (b : ProbabilityMeasure X) : unitInterval :=
  ⟨b.toMeasure.real (q ⁻¹' {true}), measureReal_nonneg, measureReal_le_one⟩

@[fun_prop] theorem measurable_coordinate (q : X → Bool) (hq : Measurable q) :
    Measurable (coordinate q) := by
  apply Measurable.subtype_mk
  exact ENNReal.measurable_toReal.comp
    ((Measure.measurable_coe ((measurableSet_singleton true).preimage hq)).comp
      measurable_subtype_coe)

def liftBelief (zero one : X) (c : unitInterval) : ProbabilityMeasure X :=
  ⟨ENNReal.ofReal (1 - (c : ℝ)) • Measure.dirac zero +
      ENNReal.ofReal (c : ℝ) • Measure.dirac one, by
    rw [isProbabilityMeasure_iff]
    simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr c.property.2) c.property.1]
    norm_num⟩

@[fun_prop] theorem measurable_liftBelief (zero one : X) :
    Measurable (liftBelief zero one) := by
  apply Measurable.subtype_mk
  apply Measure.measurable_of_measurable_coe
  intro s _hs
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  exact ((by fun_prop : Measurable fun c : unitInterval =>
    ENNReal.ofReal (1 - (c : ℝ))).mul_const _).add
      ((by fun_prop : Measurable fun c : unitInterval =>
        ENNReal.ofReal (c : ℝ)).mul_const _)

theorem coordinate_liftBelief (q : X → Bool) (hq : Measurable q)
    (zero one : X) (hzero : q zero = false) (hone : q one = true) (c : unitInterval) :
    coordinate q (liftBelief zero one c) = c := by
  apply Subtype.ext
  change ((ENNReal.ofReal (1 - (c : ℝ)) • Measure.dirac zero +
    ENNReal.ofReal (c : ℝ) • Measure.dirac one) (q ⁻¹' {true})).toReal = c
  simp [Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply' _ ((measurableSet_singleton true).preimage hq),
    hzero, hone, ENNReal.toReal_ofReal c.property.1]

theorem coordinate_real_image (q : X → Bool) (hq : Measurable q)
    (zero one : X) (hzero : q zero = false) (hone : q one = true) :
    Set.range (fun b => (coordinate q b : ℝ)) = Set.Icc 0 1 := by
  ext c
  constructor
  · rintro ⟨b, rfl⟩
    exact (coordinate q b).property
  · intro hc
    refine ⟨liftBelief zero one ⟨c, hc⟩, ?_⟩
    exact congrArg Subtype.val (coordinate_liftBelief q hq zero one hzero hone ⟨c, hc⟩)

theorem coordinate_image_isClosed (q : X → Bool) (hq : Measurable q)
    (zero one : X) (hzero : q zero = false) (hone : q one = true) :
    IsClosed (Set.range (fun b => (coordinate q b : ℝ))) := by
  rw [coordinate_real_image q hq zero one hzero hone]
  exact isClosed_Icc

private def probabilityPush (q : X → Bool) (hq : Measurable q)
    (b : ProbabilityMeasure X) : ProbabilityMeasure Bool := b.map hq.aemeasurable

def observation (q : X → Bool) (hq : Measurable q) : Kernel (X × A) Bool :=
  Kernel.deterministic (fun xa => q xa.1) (hq.comp measurable_fst)

instance observation_isMarkov (q : X → Bool) (hq : Measurable q) :
    IsMarkovKernel (observation (A := A) q hq) := by
  unfold observation
  infer_instance

private theorem fixed_observation (q : X → Bool) (hq : Measurable q) (a : A) :
    fixedActionKernel (observation (A := A) q hq) a = Kernel.deterministic q hq := by
  rfl

private theorem observationLaw_eq_map (q : X → Bool) (hq : Measurable q)
    (P : Kernel (X × A) X) [IsMarkovKernel P] (b : ProbabilityMeasure X) (a : A) :
    observationLaw b.toMeasure P (observation q hq) a =
      (predictedLaw b.toMeasure P a).map q := by
  rw [observationLaw, fixed_observation q hq a, Measure.deterministic_comp_eq_map hq]

def vertex (y : Bool) : unitInterval := if y then 1 else 0

private theorem coordinate_probabilityPush (q : X → Bool) (hq : Measurable q)
    (b : ProbabilityMeasure X) :
    coordinate id (probabilityPush q hq b) = coordinate q b := by
  apply Subtype.ext
  change (((b : Measure X).map q) {true}).toReal = _
  rw [Measure.map_apply hq (measurableSet_singleton true)]
  rfl

private theorem coordinate_dirac (y : Bool) :
    coordinate id (c1ProbDirac y) = vertex y := by
  cases y <;> apply Subtype.ext <;>
    simp [coordinate, c1ProbDirac, vertex, Measure.real]

private theorem bool_probability_ext (μ ν : ProbabilityMeasure Bool)
    (h : μ.toMeasure.real {true} = ν.toMeasure.real {true}) : μ = ν := by
  apply Subtype.ext
  apply Measure.ext_of_singleton
  intro y
  apply (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top μ.toMeasure {y}) (measure_ne_top ν.toMeasure {y})).mp
  change μ.toMeasure.real {y} = ν.toMeasure.real {y}
  cases y with
  | true => exact h
  | false =>
      have hcomp : ({true} : Set Bool)ᶜ = {false} := by
        ext y
        cases y <;> decide
      have hm := probReal_add_probReal_compl (μ := μ.toMeasure) (measurableSet_singleton true)
      have hn := probReal_add_probReal_compl (μ := ν.toMeasure) (measurableSet_singleton true)
      rw [hcomp] at hm hn
      linarith

private theorem probabilityPush_eq_of_coordinate_eq (q : X → Bool) (hq : Measurable q)
    (b b' : ProbabilityMeasure X) (h : coordinate q b = coordinate q b') :
    probabilityPush q hq b = probabilityPush q hq b' := by
  apply bool_probability_ext
  have hc := (coordinate_probabilityPush q hq b).trans
    (h.trans (coordinate_probabilityPush q hq b').symm)
  exact congrArg (fun c : unitInterval => (c : ℝ)) hc

/-- Closure of the original source's binary generating response tests. -/
def ClosedTests (P : Kernel (X × A) X) (q : X → Bool) : Prop :=
  ∀ x x', q x = q x' → ∀ a,
    P (x, a) (q ⁻¹' {true}) = P (x', a) (q ⁻¹' {true})

private theorem source_row_push_eq (q : X → Bool) (hq : Measurable q)
    (P : Kernel (X × A) X) [IsMarkovKernel P] (hclosed : ClosedTests P q)
    (x x' : X) (hx : q x = q x') (a : A) :
    (P (x, a)).map q = (P (x', a)).map q := by
  let μ : ProbabilityMeasure Bool :=
    ⟨(P (x, a)).map q, (P (x, a)).isProbabilityMeasure_map hq.aemeasurable⟩
  let ν : ProbabilityMeasure Bool :=
    ⟨(P (x', a)).map q, (P (x', a)).isProbabilityMeasure_map hq.aemeasurable⟩
  have ht := congrArg ENNReal.toReal (hclosed x x' hx a)
  have heq : μ = ν := by
    apply bool_probability_ext
    simpa only [μ, ν, Measure.real, ProbabilityMeasure.coe_mk,
      Measure.map_apply hq (measurableSet_singleton true)] using ht
  exact congrArg Subtype.val heq

private theorem observationLaw_apply_integral (q : X → Bool) (hq : Measurable q)
    (P : Kernel (X × A) X) [IsMarkovKernel P] (b : ProbabilityMeasure X) (a : A)
    (s : Set Bool) (hs : MeasurableSet s) :
    observationLaw b.toMeasure P (observation q hq) a s =
      ∫⁻ x, (P (x, a)).map q s ∂b.toMeasure := by
  rw [observationLaw_eq_map q hq P b a, predictedLaw,
    Measure.map_comp b.toMeasure (fixedActionKernel P a) hq,
    Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp only [Kernel.map_apply _ hq, fixedActionKernel, Kernel.comap_apply]

variable [StandardBorelSpace X] [Nonempty X]

/-- The actual common C1 version retains the observed class almost surely.
Null observations are not assigned an invented pointwise posterior identity. -/
private theorem posterior_observable_ae (q : X → Bool) (hq : Measurable q)
    (P : Kernel (X × A) X) [IsMarkovKernel P] (b : ProbabilityMeasure X) (a : A) :
    ∀ᵐ y ∂observationLaw b.toMeasure P (observation q hq) a,
      probabilityPush q hq (c1ParametricPosteriorBelief P (observation q hq) ((b, a), y)) =
        c1ProbDirac y := by
  have hpost := c1ParametricPosteriorKernel_ae_eq_existing P (observation q hq) b a
  have hdet := deterministic_comp_posterior (μ := predictedLaw b.toMeasure P a) hq
  rw [← observationLaw_eq_map q hq P b a] at hdet
  filter_upwards [hpost, hdet] with y hy hd
  apply Subtype.ext
  change (c1ParametricPosteriorKernel P (observation q hq) ((b, a), y)).map q =
    Measure.dirac y
  rw [hy]
  simpa only [posteriorKernel, fixed_observation q hq a,
    Kernel.deterministic_comp_eq_map hq, Kernel.map_apply _ hq,
    Kernel.id_apply] using hd

/-- Exact scalar law of the actual C1 posterior-belief transition. -/
theorem actual_kernel_coordinate_law (q : X → Bool) (hq : Measurable q)
    (P : Kernel (X × A) X) [IsMarkovKernel P] (b : ProbabilityMeasure X) (a : A) :
    (c1BeliefTransitionKernel P (observation q hq) (b, a)).map (coordinate q) =
      (observationLaw b.toMeasure P (observation q hq) a).map vertex := by
  have hpostMeas : Measurable (fun y =>
      c1ParametricPosteriorBelief P (observation q hq) ((b, a), y)) :=
    (measurable_c1ParametricPosteriorBelief P (observation q hq)).comp
      (measurable_const.prodMk measurable_id)
  rw [c1BeliefTransitionKernel_apply_eq_map,
    Measure.map_map (measurable_coordinate q hq) hpostMeas]
  apply Measure.map_congr
  filter_upwards [posterior_observable_ae q hq P b a] with y hy
  simp only [Function.comp_apply]
  rw [← coordinate_probabilityPush q hq, hy]
  exact coordinate_dirac y

omit [StandardBorelSpace X] [Nonempty X] in
theorem closed_tests_predictive_law (q : X → Bool) (hq : Measurable q)
    (P : Kernel (X × A) X) [IsMarkovKernel P] (hclosed : ClosedTests P q)
    (zero one : X) (hzero : q zero = false) (hone : q one = true)
    (b b' : ProbabilityMeasure X) (h : coordinate q b = coordinate q b') (a : A) :
    observationLaw b.toMeasure P (observation q hq) a =
      observationLaw b'.toMeasure P (observation q hq) a := by
  have hpush : b.toMeasure.map q = b'.toMeasure.map q :=
    congrArg (fun μ : ProbabilityMeasure Bool => μ.toMeasure)
    (probabilityPush_eq_of_coordinate_eq q hq b b' h)
  let repr : Bool → X := fun y => if y then one else zero
  have hrepr (y : Bool) : q (repr y) = y := by cases y <;> simp [repr, hzero, hone]
  have hrow (x : X) : (P (x, a)).map q = (P (repr (q x), a)).map q :=
    source_row_push_eq q hq P hclosed x (repr (q x)) (hrepr (q x)).symm a
  apply Measure.ext
  intro s hs
  let row : Bool → ℝ≥0∞ := fun y => ((P (repr y, a)).map q) s
  have hm : Measurable row := measurable_of_countable _
  calc
    observationLaw b.toMeasure P (observation q hq) a s =
        ∫⁻ x, row (q x) ∂b.toMeasure := by
      rw [observationLaw_apply_integral q hq P b a s hs]
      apply lintegral_congr
      intro x
      exact congrArg (fun m : Measure Bool => m s) (hrow x)
    _ = ∫⁻ y, row y ∂b.toMeasure.map q := (lintegral_map hm hq).symm
    _ = ∫⁻ y, row y ∂b'.toMeasure.map q := by rw [hpush]
    _ = ∫⁻ x, row (q x) ∂b'.toMeasure := lintegral_map hm hq
    _ = observationLaw b'.toMeasure P (observation q hq) a s := by
      rw [observationLaw_apply_integral q hq P b' a s hs]
      apply lintegral_congr
      intro x
      exact congrArg (fun m : Measure Bool => m s) (hrow x).symm

/-- The quotient transition is constructed from this source's actual C1
kernel at the explicit measurable belief section. It is not an input. -/
def quotientKernel (q : X → Bool) (hq : Measurable q)
    (P : Kernel (X × A) X) [IsMarkovKernel P] (zero one : X) :
    Kernel (unitInterval × A) unitInterval :=
  ((c1BeliefTransitionKernel P (observation q hq)).comap
    (fun ca : unitInterval × A => (liftBelief zero one ca.1, ca.2))
    (((measurable_liftBelief zero one).comp measurable_fst).prodMk measurable_snd)).map
      (coordinate q)

instance quotientKernel_isMarkov (q : X → Bool) (hq : Measurable q)
    (P : Kernel (X × A) X) [IsMarkovKernel P] (zero one : X) :
    IsMarkovKernel (quotientKernel q hq P zero one) := by
  unfold quotientKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_coordinate q hq)

/-- Source-test closure yields exact descent of the actual measurable C1
belief kernel through the predictive coordinate. -/
theorem quotientKernel_factor (q : X → Bool) (hq : Measurable q)
    (P : Kernel (X × A) X) [IsMarkovKernel P] (hclosed : ClosedTests P q)
    (zero one : X) (hzero : q zero = false) (hone : q one = true)
    (b : ProbabilityMeasure X) (a : A) :
    (c1BeliefTransitionKernel P (observation q hq) (b, a)).map (coordinate q) =
      quotientKernel q hq P zero one (coordinate q b, a) := by
  simp only [quotientKernel, Kernel.map_apply _ (measurable_coordinate q hq),
    Kernel.comap_apply]
  rw [actual_kernel_coordinate_law q hq P b a,
    actual_kernel_coordinate_law q hq P (liftBelief zero one (coordinate q b)) a]
  exact congrArg (fun μ : Measure Bool => μ.map vertex)
    (closed_tests_predictive_law q hq P hclosed zero one hzero hone b
      (liftBelief zero one (coordinate q b))
      (coordinate_liftBelief q hq zero one hzero hone (coordinate q b)).symm a)

theorem quotientKernel_unique (q : X → Bool) (hq : Measurable q)
    (P : Kernel (X × A) X) [IsMarkovKernel P] (hclosed : ClosedTests P q)
    (zero one : X) (hzero : q zero = false) (hone : q one = true)
    (K : Kernel (unitInterval × A) unitInterval)
    (hK : ∀ (b : ProbabilityMeasure X) (a : A),
      (c1BeliefTransitionKernel P (observation q hq) (b, a)).map (coordinate q) =
        K (coordinate q b, a)) : K = quotientKernel q hq P zero one := by
  ext ⟨c, a⟩ s _hs
  have h₁ := hK (liftBelief zero one c) a
  have h₂ := quotientKernel_factor q hq P hclosed zero one hzero hone
    (liftBelief zero one c) a
  rw [coordinate_liftBelief q hq zero one hzero hone c] at h₁ h₂
  exact congrArg (fun μ : Measure unitInterval => μ s) (h₁.symm.trans h₂)

omit [StandardBorelSpace X] [Nonempty X] in
private theorem coordinate_point (q : X → Bool) (hq : Measurable q) (x : X) :
    coordinate q (c1ProbDirac x) = vertex (q x) := by
  cases hx : q x <;> apply Subtype.ext <;>
    simp [coordinate, c1ProbDirac, vertex, Measure.real,
      Measure.dirac_apply' _ ((measurableSet_singleton true).preimage hq), hx]

omit [StandardBorelSpace X] [Nonempty X] in
private theorem observationLaw_point_true (q : X → Bool) (hq : Measurable q)
    (P : Kernel (X × A) X) [IsMarkovKernel P] (x : X) (a : A) :
    observationLaw (c1ProbDirac x).toMeasure P (observation q hq) a {true} =
      P (x, a) (q ⁻¹' {true}) := by
  rw [observationLaw_eq_map q hq P (c1ProbDirac x) a]
  change ((fixedActionKernel P a ∘ₘ Measure.dirac x).map q) {true} = _
  rw [Measure.dirac_bind (fixedActionKernel P a).measurable x,
    Measure.map_apply hq (measurableSet_singleton true)]
  rfl

/-- Descent for every actual input belief forces closure of the original
source tests. This rules out a quotient even before asking it to be Markov. -/
theorem closed_tests_of_quotient (q : X → Bool) (hq : Measurable q)
    (P : Kernel (X × A) X) [IsMarkovKernel P]
    (K : Kernel (unitInterval × A) unitInterval)
    (hK : ∀ (b : ProbabilityMeasure X) (a : A),
      (c1BeliefTransitionKernel P (observation q hq) (b, a)).map (coordinate q) =
        K (coordinate q b, a)) : ClosedTests P q := by
  intro x x' hx a
  have hc : coordinate q (c1ProbDirac x) = coordinate q (c1ProbDirac x') := by
    rw [coordinate_point q hq x, coordinate_point q hq x', hx]
  have heq :
      (c1BeliefTransitionKernel P (observation q hq) (c1ProbDirac x, a)).map (coordinate q) =
      (c1BeliefTransitionKernel P (observation q hq) (c1ProbDirac x', a)).map (coordinate q) := by
    rw [hK, hK, hc]
  rw [actual_kernel_coordinate_law q hq P (c1ProbDirac x) a,
    actual_kernel_coordinate_law q hq P (c1ProbDirac x') a] at heq
  have hm : Measurable vertex := measurable_of_countable _
  have hpre : vertex ⁻¹' {(1 : unitInterval)} = {true} := by
    ext y
    cases y <;> norm_num [vertex]
  have ht := congrArg (fun μ : Measure unitInterval => μ {(1 : unitInterval)}) heq
  simpa only [Measure.map_apply hm (measurableSet_singleton (1 : unitInterval)), hpre,
    observationLaw_point_true q hq P x a, observationLaw_point_true q hq P x' a] using ht

/-- An explicit image/Borel section and source-test closure characterize a
unique measurable Markov quotient of the actual C1 belief kernel. -/
theorem closed_tests_iff_existsUnique_quotient (q : X → Bool) (hq : Measurable q)
    (P : Kernel (X × A) X) [IsMarkovKernel P]
    (zero one : X) (hzero : q zero = false) (hone : q one = true) :
    ClosedTests P q ↔ ∃! K : Kernel (unitInterval × A) unitInterval,
      IsMarkovKernel K ∧ ∀ (b : ProbabilityMeasure X) (a : A),
        (c1BeliefTransitionKernel P (observation q hq) (b, a)).map (coordinate q) =
          K (coordinate q b, a) := by
  constructor
  · intro hclosed
    refine ⟨quotientKernel q hq P zero one, ⟨inferInstance, ?_⟩, ?_⟩
    · exact quotientKernel_factor q hq P hclosed zero one hzero hone
    · intro K hK
      exact quotientKernel_unique q hq P hclosed zero one hzero hone K hK.2
  · rintro ⟨K, hK, _⟩
    exact closed_tests_of_quotient q hq P K hK.2

def testResponse (P : Kernel (X × A) X) (q : X → Bool) :
    List (A × Bool) → X → ℝ≥0∞
  | [], _ => 1
  | (a, o) :: word, x =>
      ∫⁻ z, if q z = o then testResponse P q word z else 0 ∂P (x, a)

def testExpectation (P : Kernel (X × A) X) (q : X → Bool)
    (b : ProbabilityMeasure X) (word : List (A × Bool)) : ℝ :=
  (∫⁻ x, testResponse P q word x ∂b.toMeasure).toReal

omit [StandardBorelSpace X] [Nonempty X] in
theorem closed_tests_prefix_response (q : X → Bool) (hq : Measurable q)
    (P : Kernel (X × A) X) [IsMarkovKernel P] (hclosed : ClosedTests P q)
    (zero one : X) (hzero : q zero = false) (hone : q one = true)
    (a : A) (o : Bool) (f : Bool → ℝ≥0∞) :
    ∃ g : Bool → ℝ≥0∞, ∀ x,
      (∫⁻ z, if q z = o then f (q z) else 0 ∂P (x, a)) = g (q x) := by
  let repr : Bool → X := fun y => if y then one else zero
  have hrepr (y : Bool) : q (repr y) = y := by cases y <;> simp [repr, hzero, hone]
  let continuation : Bool → ℝ≥0∞ := fun y => if y = o then f y else 0
  have hm : Measurable continuation := measurable_of_countable _
  refine ⟨fun y => ∫⁻ z, continuation (q z) ∂P (repr y, a), ?_⟩
  intro x
  change (∫⁻ z, continuation (q z) ∂P (x, a)) =
    ∫⁻ z, continuation (q z) ∂P (repr (q x), a)
  rw [← lintegral_map hm hq, ← lintegral_map hm hq]
  rw [source_row_push_eq q hq P hclosed x (repr (q x)) (hrepr (q x)).symm a]

omit [StandardBorelSpace X] [Nonempty X] in
theorem finite_test_response_factors (q : X → Bool) (hq : Measurable q)
    (P : Kernel (X × A) X) [IsMarkovKernel P] (hclosed : ClosedTests P q)
    (zero one : X) (hzero : q zero = false) (hone : q one = true)
    (word : List (A × Bool)) :
    ∃ g : Bool → ℝ≥0∞, ∀ x, testResponse P q word x = g (q x) := by
  induction word with
  | nil => exact ⟨fun _ => 1, fun _ => rfl⟩
  | cons ao word ih =>
      obtain ⟨f, hf⟩ := ih
      obtain ⟨g, hg⟩ := closed_tests_prefix_response q hq P hclosed
        zero one hzero hone ao.1 ao.2 f
      refine ⟨g, ?_⟩
      intro x
      simp only [testResponse]
      simp_rw [hf]
      exact hg x

omit [StandardBorelSpace X] [Nonempty X] in
theorem same_coordinate_same_tests (q : X → Bool) (hq : Measurable q)
    (P : Kernel (X × A) X) [IsMarkovKernel P] (hclosed : ClosedTests P q)
    (zero one : X) (hzero : q zero = false) (hone : q one = true)
    (b b' : ProbabilityMeasure X) (h : coordinate q b = coordinate q b')
    (word : List (A × Bool)) : testExpectation P q b word = testExpectation P q b' word := by
  obtain ⟨g, hg⟩ := finite_test_response_factors q hq P hclosed zero one hzero hone word
  have hpush : b.toMeasure.map q = b'.toMeasure.map q :=
    congrArg (fun μ : ProbabilityMeasure Bool => μ.toMeasure)
      (probabilityPush_eq_of_coordinate_eq q hq b b' h)
  have hm : Measurable g := measurable_of_countable _
  unfold testExpectation
  simp_rw [hg]
  rw [← lintegral_map hm hq, ← lintegral_map hm hq, hpush]

omit [StandardBorelSpace X] [Nonempty X] in
theorem testResponse_le_one (P : Kernel (X × A) X) [IsMarkovKernel P]
    (q : X → Bool) (word : List (A × Bool)) (x : X) :
    testResponse P q word x ≤ 1 := by
  induction word generalizing x with
  | nil => simp [testResponse]
  | cons ao word ih =>
      simp only [testResponse]
      calc
        _ ≤ ∫⁻ _z, (1 : ℝ≥0∞) ∂P (x, ao.1) := by
          apply lintegral_mono
          intro z
          dsimp only
          split_ifs
          · exact ih z
          · exact zero_le_one
        _ = 1 := by simp

omit [StandardBorelSpace X] [Nonempty X] in
theorem testExpectation_mem_unit (P : Kernel (X × A) X) [IsMarkovKernel P]
    (q : X → Bool) (b : ProbabilityMeasure X) (word : List (A × Bool)) :
    testExpectation P q b word ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  have hmass : (∫⁻ x, testResponse P q word x ∂b.toMeasure) ≤ 1 := by
    calc
      _ ≤ ∫⁻ _x, (1 : ℝ≥0∞) ∂b.toMeasure :=
        lintegral_mono (fun x => testResponse_le_one P q word x)
      _ = 1 := by simp
  exact ENNReal.toReal_mono ENNReal.one_ne_top hmass

omit [StandardBorelSpace X] [Nonempty X] in
theorem first_test_eq_observation (q : X → Bool) (hq : Measurable q)
    (P : Kernel (X × A) X) [IsMarkovKernel P] (b : ProbabilityMeasure X) (a : A) (o : Bool) :
    testExpectation P q b [(a, o)] =
      (observationLaw b.toMeasure P (observation q hq) a).real {o} := by
  have hresponse (x : X) : testResponse P q [(a, o)] x = P (x, a) (q ⁻¹' {o}) := by
    simpa only [testResponse, Set.indicator, Set.mem_preimage, Set.mem_singleton_iff,
      Pi.one_apply] using
      (lintegral_indicator_one (μ := P (x, a)) ((measurableSet_singleton o).preimage hq))
  have hobs := observationLaw_apply_integral q hq P b a {o} (measurableSet_singleton o)
  simp only [Measure.map_apply hq (measurableSet_singleton o)] at hobs
  unfold testExpectation
  simp_rw [hresponse]
  exact congrArg ENNReal.toReal hobs.symm

omit [StandardBorelSpace X] [Nonempty X] in
theorem safe_class_probability (q : X → Bool) (hq : Measurable q) (b : ProbabilityMeasure X) :
    b.toMeasure.real (q ⁻¹' {false}) = 1 - (coordinate q b : ℝ) := by
  have hcomp : (q ⁻¹' {true})ᶜ = q ⁻¹' {false} := by
    ext x
    cases hx : q x <;> simp [Set.mem_preimage, hx]
  have h := probReal_compl_eq_one_sub (μ := b.toMeasure)
    ((measurableSet_singleton true).preimage hq)
  simpa only [hcomp, coordinate] using h

omit [StandardBorelSpace X] [Nonempty X] in
theorem observation_reward_factors (q : X → Bool) (hq : Measurable q)
    (b : ProbabilityMeasure X) (r : Bool → ℝ) :
    (∫ x, r (q x) ∂b.toMeasure) =
      (1 - (coordinate q b : ℝ)) * r false + (coordinate q b : ℝ) * r true := by
  let μ := probabilityPush q hq b
  have hm : Measurable r := measurable_of_countable _
  have hi : Integrable r μ.toMeasure :=
    ⟨hm.aestronglyMeasurable, HasFiniteIntegral.of_finite⟩
  have ht : μ.toMeasure.real {true} = (coordinate q b : ℝ) :=
    congrArg (fun c : unitInterval => (c : ℝ)) (coordinate_probabilityPush q hq b)
  have hf : μ.toMeasure.real {false} = 1 - (coordinate q b : ℝ) := by
    have hcomp : ({true} : Set Bool)ᶜ = {false} := by ext y; cases y <;> decide
    simpa only [hcomp, ht] using
      (probReal_compl_eq_one_sub (μ := μ.toMeasure) (measurableSet_singleton true))
  calc
    _ = ∫ y, r y ∂μ.toMeasure :=
      (integral_map hq.aemeasurable hm.aestronglyMeasurable).symm
    _ = _ := by
      rw [integral_fintype hi]
      simp only [Fintype.sum_bool, smul_eq_mul, ht, hf]
      ring

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ObservableBeliefQuotient
