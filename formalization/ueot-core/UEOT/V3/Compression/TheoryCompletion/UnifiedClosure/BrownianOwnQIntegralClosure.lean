import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQRepresentation
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Isomorphisms

/-!
Original commitment: actual Q stochastic integration must extend the actual permitted finite outputs, rather than reuse P-integral labels.
Existing result: actual dt×Q inputs and actual W/Q outputs preserve every native L2 distance across original finite representations.
Premise reduced: construct native linear isometry and continuous extension on the EXPLICIT dt×Q elementary-span closure.
Model/witness: same bounded source-control f, own Q/W, original Fs permissions, any integration horizon including zero.
Consumer/boundary: actual bounded-control Q input membership and source consumers follow next; closure is NOT renamed full predictable L2.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQIntegralClosure
open MeasureTheory ProbabilityTheory Set Filter
open BrownianTimeIntegrand BrownianPredictableInputs BrownianIntegralClosure BrownianBoundedExponentialLimitSource
open BrownianOwnQTimeInput BrownianOwnQRepresentation
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory InnerProductSpace RealInnerProductSpace
noncomputable section
variable (A : ℝ≥0) (f : fullPredictableL2 A) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw A, |(f : Lp ℝ 2 (inputLaw A)) p|≤K)

/-- The Gram identity is derived from actual source norms and distances. -/
theorem family_inner {T : ℝ≥0} (r s : ElementaryInput T) :
    inner ℝ (outputValueQ A f K hK hbound r) (outputValueQ A f K hK hbound s) = inner ℝ (inputValueQ A f K hK hbound r) (inputValueQ A f K hK hbound s) := by
  have hd := BrownianOwnQRepresentation.family_distance A f K hK hbound r s
  rw [dist_eq_norm,dist_eq_norm] at hd
  rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
    real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
    BrownianOwnQTimeInput.family_norm A f K hK hbound r,BrownianOwnQTimeInput.family_norm A f K hK hbound s,hd]

/-- Native finite linear combinations, not an alternative stochastic-integral
certificate or a new Hilbert-space representation. -/
def inputLinear (T : ℝ≥0) : (ElementaryInput T →₀ ℝ) →ₗ[ℝ] Lp ℝ 2 (inputLawQ A f T) :=
  Finsupp.linearCombination ℝ (inputValueQ A f K hK hbound)

def outputLinear (T : ℝ≥0) : (ElementaryInput T →₀ ℝ) →ₗ[ℝ] Lp ℝ 2 (fullLaw A f) :=
  Finsupp.linearCombination ℝ (outputValueQ A f K hK hbound)

private theorem combination_inner (T : ℝ≥0) (a b : ElementaryInput T →₀ ℝ) :
    inner ℝ (outputLinear A f K hK hbound T a) (outputLinear A f K hK hbound T b) = inner ℝ (inputLinear A f K hK hbound T a) (inputLinear A f K hK hbound T b) := by
  classical
  simp only [inputLinear,outputLinear,Finsupp.linearCombination_apply,Finsupp.sum,
    sum_inner,inner_sum,inner_smul_left,inner_smul_right,starRingEnd_apply,star_trivial,family_inner]

theorem combination_norm (T : ℝ≥0) (a : ElementaryInput T →₀ ℝ) :
    ‖outputLinear A f K hK hbound T a‖ = ‖inputLinear A f K hK hbound T a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq,← real_inner_self_eq_norm_sq,combination_inner]

/-- The original native span of actual elementary input classes. Its closure
is not silently identified with all predictable L2 functions. -/
def elementarySpan (T : ℝ≥0) : Submodule ℝ (Lp ℝ 2 (inputLawQ A f T)) := (inputLinear A f K hK hbound T).range

theorem elementarySpan_eq_span (T : ℝ≥0) :
    elementarySpan A f K hK hbound T = Submodule.span ℝ (Set.range (inputValueQ A f K hK hbound (U := T))) :=
  Finsupp.range_linearCombination ℝ

private theorem combination_bound (T : ℝ≥0) :
    ∃ C : ℝ, ∀ a, ‖outputLinear A f K hK hbound T a‖ ≤ C * ‖inputLinear A f K hK hbound T a‖ :=
  ⟨1,fun a => by rw [combination_norm,one_mul]⟩

/-- Native compLeftInverse descends the ACTUAL output combinations through
the proved common kernel, directly to the original elementary L2 span. -/
def elementaryIntegral (T : ℝ≥0) : elementarySpan A f K hK hbound T →L[ℝ] Lp ℝ 2 (fullLaw A f) :=
  (outputLinear A f K hK hbound T).compLeftInverse (inputLinear A f K hK hbound T)

theorem elementaryIntegral_image (T : ℝ≥0) (a : ElementaryInput T →₀ ℝ) :
    elementaryIntegral A f K hK hbound T ⟨inputLinear A f K hK hbound T a,⟨a,rfl⟩⟩ = outputLinear A f K hK hbound T a :=
  LinearMap.compLeftInverse_apply_of_bdd _ _ (combination_bound A f K hK hbound T) a _ rfl

theorem elementaryIntegral_norm (T : ℝ≥0) (x : elementarySpan A f K hK hbound T) :
    ‖elementaryIntegral A f K hK hbound T x‖ = ‖x‖ := by
  obtain ⟨a,ha⟩ := x.property
  have he : x = ⟨inputLinear A f K hK hbound T a,⟨a,rfl⟩⟩ := Subtype.ext ha.symm
  rw [he,elementaryIntegral_image,combination_norm]
  rfl

/-- The completed source domain is explicitly only the elementary-span
closure in the actual time-times-OWN-Q L2 space. -/
def integralDomain (T : ℝ≥0) : Submodule ℝ (Lp ℝ 2 (inputLawQ A f T)) := (elementarySpan A f K hK hbound T).topologicalClosure

def inclusionIsometry (T : ℝ≥0) : elementarySpan A f K hK hbound T →ₗᵢ[ℝ] integralDomain A f K hK hbound T :=
  { Submodule.inclusion (elementarySpan A f K hK hbound T).le_topologicalClosure with norm_map' := fun _ => rfl }

theorem inclusion_dense (T : ℝ≥0) : DenseRange (inclusionIsometry A f K hK hbound T) := by
  change DenseRange (Set.inclusion (elementarySpan A f K hK hbound T).le_topologicalClosure)
  exact (denseRange_inclusion_iff (elementarySpan A f K hK hbound T).le_topologicalClosure).mpr (Set.Subset.refl _)

/-- Actual native continuous LINEAR extension; no desired extension map is
supplied as an argument. -/
def integral (T : ℝ≥0) : integralDomain A f K hK hbound T →L[ℝ] Lp ℝ 2 (fullLaw A f) :=
  (elementaryIntegral A f K hK hbound T).extend (inclusionIsometry A f K hK hbound T).toContinuousLinearMap

theorem integral_agrees_elementary (T : ℝ≥0) (x : elementarySpan A f K hK hbound T) :
    integral A f K hK hbound T (inclusionIsometry A f K hK hbound T x) = elementaryIntegral A f K hK hbound T x := by
  unfold integral
  exact ContinuousLinearMap.extend_eq (e := (inclusionIsometry A f K hK hbound T).toContinuousLinearMap)
    (elementaryIntegral A f K hK hbound T) (inclusion_dense A f K hK hbound T) (inclusionIsometry A f K hK hbound T).isometry.isUniformInducing x

/-- The isometry on the actual elementary inputs survives completion. -/
theorem integral_norm (T : ℝ≥0) (x : integralDomain A f K hK hbound T) : ‖integral A f K hK hbound T x‖ = ‖x‖ := by
  refine (inclusion_dense A f K hK hbound T).induction_on x (isClosed_eq (integral A f K hK hbound T).continuous.norm continuous_norm) ?_
  intro y
  rw [integral_agrees_elementary,elementaryIntegral_norm]
  rfl

/-- The actual constructed continuous linear stochastic integral on the
explicit closure domain, bundled using the original native LinearIsometry. -/
def integralIsometry (T : ℝ≥0) : integralDomain A f K hK hbound T →ₗᵢ[ℝ] Lp ℝ 2 (fullLaw A f) :=
  { (integral A f K hK hbound T).toLinearMap with norm_map' := integral_norm A f K hK hbound T }

/-- The actual elementary input's point in the ORIGINAL native span. -/
def elementaryPoint {T : ℝ≥0} (r : ElementaryInput T) : elementarySpan A f K hK hbound T :=
  ⟨inputValueQ A f K hK hbound r,⟨Finsupp.single r 1,by simp [inputLinear]⟩⟩

/-- Actual input in the explicitly named closure domain, with no change to
its native time-times-source L2 class. -/
def representedInput {T : ℝ≥0} (r : ElementaryInput T) : integralDomain A f K hK hbound T :=
  inclusionIsometry A f K hK hbound T (elementaryPoint A f K hK hbound r)

/-- The extended integral returns the SAME literal finite-strategy output
class for EVERY supplied elementary input record. -/
theorem integral_returns_literal {T : ℝ≥0} (r : ElementaryInput T) :
    integral A f K hK hbound T (representedInput A f K hK hbound r) = outputValueQ A f K hK hbound r := by
  rw [representedInput,integral_agrees_elementary]
  have he : elementaryPoint A f K hK hbound r =
      ⟨inputLinear A f K hK hbound T (Finsupp.single r 1),⟨Finsupp.single r 1,rfl⟩⟩ := by
    apply Subtype.ext
    simp [elementaryPoint,inputLinear]
  rw [he,elementaryIntegral_image]
  simp [outputLinear]

/-- Native continuous limit consumer, for every input in the EXPLICIT closed
span domain; no claim of full predictable density occurs in its type. -/
theorem integral_tendsto (T : ℝ≥0) {g : ℕ → integralDomain A f K hK hbound T} {x : integralDomain A f K hK hbound T}
    (hf : Filter.Tendsto g Filter.atTop (𝓝 x)) :
    Filter.Tendsto (fun n => integral A f K hK hbound T (g n)) Filter.atTop (𝓝 (integral A f K hK hbound T x)) :=
  ((integral A f K hK hbound T).continuous.tendsto x).comp hf

/-- A sequence of ACTUAL finite inputs converging in the original time-source
L2 norm yields convergence of their SAME literal output classes. -/
theorem literal_outputs_tendsto {T : ℝ≥0} (r : ℕ → ElementaryInput T) (x : integralDomain A f K hK hbound T)
    (hx : Filter.Tendsto (fun n => inputValueQ A f K hK hbound (r n)) Filter.atTop (𝓝 (x : Lp ℝ 2 (inputLawQ A f T)))) :
    Filter.Tendsto (fun n => outputValueQ A f K hK hbound (r n)) Filter.atTop (𝓝 (integral A f K hK hbound T x)) := by
  have hsub : Filter.Tendsto (fun n => representedInput A f K hK hbound (r n)) Filter.atTop (𝓝 x) :=
    tendsto_subtype_rng.mpr hx
  simpa only [integral_returns_literal] using integral_tendsto A f K hK hbound T hsub


end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQIntegralClosure
