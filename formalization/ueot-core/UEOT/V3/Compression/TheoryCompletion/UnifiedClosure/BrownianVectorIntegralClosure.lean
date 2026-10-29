import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorRepresentation
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Isomorphisms

/-!
Original commitment: the actual vector-noise integral must extend native finite input representations without choosing another output.
Existing result: SAME joint-source Euclidean input classes and scalar output classes preserve all cross-partition distances.
Premise reduced: derive native Gram/kernel equality and construct actual Finsupp-factor/continuous extension returning literal outputs.
Model/witness: arbitrary finite d and finite deterministic0/T clock data with original joint START permissions, including d0/T0/repeats.
Consumer: later genuine joint-predictable-domain density; this domain is explicitly ONLY the elementary-span closure.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorIntegralClosure
open MeasureTheory ProbabilityTheory Set
open BrownianFiniteProductSource BrownianVectorTimeInput BrownianVectorRepresentation
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Actual finite input data and its causal permissions. There is no integral,
martingale, norm identity or desired output certificate among these fields. -/
structure ElementaryInput (d : ℕ) (T : ℝ≥0) where
  n : ℕ
  clock : Fin (n+1) → ℝ≥0
  coefficient : Fin n → Fin d → Sample d → ℝ
  clock_mono : Monotone clock
  clock_zero : clock 0 = 0
  clock_end : clock (Fin.last n) = T
  coefficient_past : ∀ i k, StronglyMeasurable[jointNaturalFiltration d (clock i.castSucc)] (coefficient i k)
  coefficient_bounded : ∀ i k, MemLp (coefficient i k) ∞ (productLaw d)

def inputValue {d : ℕ} {T : ℝ≥0} (r : ElementaryInput d T) : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T) :=
  inputClass T r.clock r.coefficient r.coefficient_bounded

def outputValue {d : ℕ} {T : ℝ≥0} (r : ElementaryInput d T) : Lp ℝ 2 (productLaw d) :=
  outputClass r.clock r.coefficient r.coefficient_bounded

theorem family_norm {d : ℕ} {T : ℝ≥0} (r : ElementaryInput d T) : ‖outputValue r‖ = ‖inputValue r‖ :=
  input_output_norm T r.clock r.coefficient r.clock_mono r.clock_end.le r.coefficient_past r.coefficient_bounded

theorem family_distance {d : ℕ} {T : ℝ≥0} (r s : ElementaryInput d T) :
    dist (outputValue r) (outputValue s) = dist (inputValue r) (inputValue s) :=
  input_output_distance T r.clock s.clock r.clock_mono s.clock_mono r.clock_zero s.clock_zero
    r.clock_end s.clock_end r.coefficient s.coefficient r.coefficient_past s.coefficient_past
    r.coefficient_bounded s.coefficient_bounded

/-- The Gram identity is derived from actual source norms and distances. -/
theorem family_inner {d : ℕ} {T : ℝ≥0} (r s : ElementaryInput d T) :
    inner ℝ (outputValue r) (outputValue s) = inner ℝ (inputValue r) (inputValue s) := by
  have hd := family_distance r s
  rw [dist_eq_norm,dist_eq_norm] at hd
  rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
    real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
    family_norm r,family_norm s,hd]

/-- Native finite linear combinations, not an alternative stochastic-integral
certificate or a new Hilbert-space representation. -/
def inputLinear (d : ℕ) (T : ℝ≥0) : (ElementaryInput d T →₀ ℝ) →ₗ[ℝ] Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T) :=
  Finsupp.linearCombination ℝ (inputValue (d := d) (T := T))

def outputLinear (d : ℕ) (T : ℝ≥0) : (ElementaryInput d T →₀ ℝ) →ₗ[ℝ] Lp ℝ 2 (productLaw d) :=
  Finsupp.linearCombination ℝ (outputValue (d := d) (T := T))

private theorem combination_inner (d : ℕ) (T : ℝ≥0) (a b : ElementaryInput d T →₀ ℝ) :
    inner ℝ (outputLinear d T a) (outputLinear d T b) = inner ℝ (inputLinear d T a) (inputLinear d T b) := by
  classical
  simp only [inputLinear,outputLinear,Finsupp.linearCombination_apply,Finsupp.sum,
    sum_inner,inner_sum,inner_smul_left,inner_smul_right,starRingEnd_apply,star_trivial,family_inner]

theorem combination_norm (d : ℕ) (T : ℝ≥0) (a : ElementaryInput d T →₀ ℝ) :
    ‖outputLinear d T a‖ = ‖inputLinear d T a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq,← real_inner_self_eq_norm_sq,combination_inner]

/-- The original native span of actual elementary input classes. Its closure
is not silently identified with all predictable L2 functions. -/
def elementarySpan (d : ℕ) (T : ℝ≥0) : Submodule ℝ (Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) := (inputLinear d T).range

theorem elementarySpan_eq_span (d : ℕ) (T : ℝ≥0) :
    elementarySpan d T = Submodule.span ℝ (Set.range (inputValue (T := T))) :=
  Finsupp.range_linearCombination ℝ

private theorem combination_bound (d : ℕ) (T : ℝ≥0) :
    ∃ C : ℝ, ∀ a, ‖outputLinear d T a‖ ≤ C * ‖inputLinear d T a‖ :=
  ⟨1,fun a => by rw [combination_norm,one_mul]⟩

/-- Native compLeftInverse descends the ACTUAL output combinations through
the proved common kernel, directly to the original elementary L2 span. -/
def elementaryIntegral (d : ℕ) (T : ℝ≥0) : elementarySpan d T →L[ℝ] Lp ℝ 2 (productLaw d) :=
  (outputLinear d T).compLeftInverse (inputLinear d T)

theorem elementaryIntegral_image (d : ℕ) (T : ℝ≥0) (a : ElementaryInput d T →₀ ℝ) :
    elementaryIntegral d T ⟨inputLinear d T a,⟨a,rfl⟩⟩ = outputLinear d T a :=
  LinearMap.compLeftInverse_apply_of_bdd _ _ (combination_bound d T) a _ rfl

theorem elementaryIntegral_norm (d : ℕ) (T : ℝ≥0) (x : elementarySpan d T) :
    ‖elementaryIntegral d T x‖ = ‖x‖ := by
  obtain ⟨a,ha⟩ := x.property
  have he : x = ⟨inputLinear d T a,⟨a,rfl⟩⟩ := Subtype.ext ha.symm
  rw [he,elementaryIntegral_image,combination_norm]
  rfl

/-- The completed source domain is explicitly only the elementary-span
closure in the original time-times-source L2 space. -/
def integralDomain (d : ℕ) (T : ℝ≥0) : Submodule ℝ (Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)) := (elementarySpan d T).topologicalClosure

def inclusionIsometry (d : ℕ) (T : ℝ≥0) : elementarySpan d T →ₗᵢ[ℝ] integralDomain d T :=
  { Submodule.inclusion (elementarySpan d T).le_topologicalClosure with norm_map' := fun _ => rfl }

theorem inclusion_dense (d : ℕ) (T : ℝ≥0) : DenseRange (inclusionIsometry d T) := by
  change DenseRange (Set.inclusion (elementarySpan d T).le_topologicalClosure)
  exact (denseRange_inclusion_iff (elementarySpan d T).le_topologicalClosure).mpr (Set.Subset.refl _)

/-- Actual native continuous LINEAR extension; no desired extension map is
supplied as an argument. -/
def integral (d : ℕ) (T : ℝ≥0) : integralDomain d T →L[ℝ] Lp ℝ 2 (productLaw d) :=
  (elementaryIntegral d T).extend (inclusionIsometry d T).toContinuousLinearMap

theorem integral_agrees_elementary (d : ℕ) (T : ℝ≥0) (x : elementarySpan d T) :
    integral d T (inclusionIsometry d T x) = elementaryIntegral d T x := by
  unfold integral
  exact ContinuousLinearMap.extend_eq (e := (inclusionIsometry d T).toContinuousLinearMap)
    (elementaryIntegral d T) (inclusion_dense d T) (inclusionIsometry d T).isometry.isUniformInducing x

/-- The isometry on the actual elementary inputs survives completion. -/
theorem integral_norm (d : ℕ) (T : ℝ≥0) (x : integralDomain d T) : ‖integral d T x‖ = ‖x‖ := by
  refine (inclusion_dense d T).induction_on x (isClosed_eq (integral d T).continuous.norm continuous_norm) ?_
  intro y
  rw [integral_agrees_elementary,elementaryIntegral_norm]
  rfl

/-- The actual constructed continuous linear stochastic integral on the
explicit closure domain, bundled using the original native LinearIsometry. -/
def integralIsometry (d : ℕ) (T : ℝ≥0) : integralDomain d T →ₗᵢ[ℝ] Lp ℝ 2 (productLaw d) :=
  { (integral d T).toLinearMap with norm_map' := integral_norm d T }

/-- The actual elementary input's point in the ORIGINAL native span. -/
def elementaryPoint {d : ℕ} {T : ℝ≥0} (r : ElementaryInput d T) : elementarySpan d T :=
  ⟨inputValue r,⟨Finsupp.single r 1,by simp [inputLinear]⟩⟩

/-- Actual input in the explicitly named closure domain, with no change to
its native time-times-source L2 class. -/
def representedInput {d : ℕ} {T : ℝ≥0} (r : ElementaryInput d T) : integralDomain d T :=
  inclusionIsometry d T (elementaryPoint r)

/-- The extended integral returns the SAME literal finite-strategy output
class for EVERY supplied elementary input record. -/
theorem integral_returns_literal {d : ℕ} {T : ℝ≥0} (r : ElementaryInput d T) :
    integral d T (representedInput r) = outputValue r := by
  rw [representedInput,integral_agrees_elementary]
  have he : elementaryPoint r =
      ⟨inputLinear d T (Finsupp.single r 1),⟨Finsupp.single r 1,rfl⟩⟩ := by
    apply Subtype.ext
    simp [elementaryPoint,inputLinear]
  rw [he,elementaryIntegral_image]
  simp [outputLinear]

/-- Native continuous limit consumer, for every input in the EXPLICIT closed
span domain; no claim of full predictable density occurs in its type. -/
theorem integral_tendsto (d : ℕ) (T : ℝ≥0) {f : ℕ → integralDomain d T} {x : integralDomain d T}
    (hf : Filter.Tendsto f Filter.atTop (𝓝 x)) :
    Filter.Tendsto (fun n => integral d T (f n)) Filter.atTop (𝓝 (integral d T x)) :=
  ((integral d T).continuous.tendsto x).comp hf

/-- A sequence of ACTUAL finite inputs converging in the original time-source
L2 norm yields convergence of their SAME literal output classes. -/
theorem literal_outputs_tendsto {d : ℕ} {T : ℝ≥0} (r : ℕ → ElementaryInput d T) (x : integralDomain d T)
    (hx : Filter.Tendsto (fun n => inputValue (r n)) Filter.atTop (𝓝 (x : Lp (EuclideanSpace ℝ (Fin d)) 2 (inputLaw d T)))) :
    Filter.Tendsto (fun n => outputValue (r n)) Filter.atTop (𝓝 (integral d T x)) := by
  have hsub : Filter.Tendsto (fun n => representedInput (r n)) Filter.atTop (𝓝 x) :=
    tendsto_subtype_rng.mpr hx
  simpa only [integral_returns_literal] using integral_tendsto d T hsub

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorIntegralClosure
