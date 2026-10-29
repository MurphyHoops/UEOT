import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralRepresentation
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Isomorphisms

/-!
Original commitment: an actual stochastic integral source must extend beyond a chosen finite partition.
Existing result: actual elementary input/output classes preserve all native L2 distances across partitions.
Premise reduced: construct the native linear isometry on their span and continuous isometry on its L2 closure.
Model/witness: SAME source and declared horizon; fields contain only actual partition/coefficient permissions.
Consumer: actual L2-limit stochastic output; density in the full predictable L2 class remains a separate obligation.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralClosure
open MeasureTheory ProbabilityTheory Set
open BrownianContinuousSource BrownianProjectiveSource BrownianMartingaleSource
open BrownianTimeIntegrand BrownianIntegralRepresentation
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Actual finite input data and its causal permissions. There is no integral,
martingale, norm identity or desired output certificate among these fields. -/
structure ElementaryInput (T : ℝ≥0) where
  n : ℕ
  clock : Fin (n+1) → ℝ≥0
  coefficient : Fin n → (ℝ≥0 → ℝ) → ℝ
  clock_mono : Monotone clock
  clock_zero : clock 0 = 0
  clock_end : clock (Fin.last n) = T
  coefficient_past : ∀ i, StronglyMeasurable[naturalFiltration (clock i.castSucc)] (coefficient i)
  coefficient_bounded : ∀ i, MemLp (coefficient i) ∞ sourceLaw

def inputValue {T : ℝ≥0} (r : ElementaryInput T) : Lp ℝ 2 (inputLaw T) :=
  inputClass T r.clock r.coefficient r.coefficient_bounded

def outputValue {T : ℝ≥0} (r : ElementaryInput T) : Lp ℝ 2 sourceLaw :=
  outputClass r.clock r.coefficient r.coefficient_bounded

theorem family_norm {T : ℝ≥0} (r : ElementaryInput T) : ‖outputValue r‖ = ‖inputValue r‖ :=
  outputClass_norm T r.clock r.coefficient r.clock_mono r.clock_end.le r.coefficient_past r.coefficient_bounded

theorem family_distance {T : ℝ≥0} (r s : ElementaryInput T) :
    dist (outputValue r) (outputValue s) = dist (inputValue r) (inputValue s) :=
  input_output_distance T r.clock s.clock r.clock_mono s.clock_mono r.clock_zero s.clock_zero
    r.clock_end s.clock_end r.coefficient s.coefficient r.coefficient_past s.coefficient_past
    r.coefficient_bounded s.coefficient_bounded

/-- The Gram identity is derived from actual source norms and distances. -/
theorem family_inner {T : ℝ≥0} (r s : ElementaryInput T) :
    inner ℝ (outputValue r) (outputValue s) = inner ℝ (inputValue r) (inputValue s) := by
  have hd := family_distance r s
  rw [dist_eq_norm,dist_eq_norm] at hd
  rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
    real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
    family_norm r,family_norm s,hd]

/-- Native finite linear combinations, not an alternative stochastic-integral
certificate or a new Hilbert-space representation. -/
def inputLinear (T : ℝ≥0) : (ElementaryInput T →₀ ℝ) →ₗ[ℝ] Lp ℝ 2 (inputLaw T) :=
  Finsupp.linearCombination ℝ inputValue

def outputLinear (T : ℝ≥0) : (ElementaryInput T →₀ ℝ) →ₗ[ℝ] Lp ℝ 2 sourceLaw :=
  Finsupp.linearCombination ℝ outputValue

private theorem combination_inner (T : ℝ≥0) (a b : ElementaryInput T →₀ ℝ) :
    inner ℝ (outputLinear T a) (outputLinear T b) = inner ℝ (inputLinear T a) (inputLinear T b) := by
  classical
  simp only [inputLinear,outputLinear,Finsupp.linearCombination_apply,Finsupp.sum,
    sum_inner,inner_sum,inner_smul_left,inner_smul_right,starRingEnd_apply,star_trivial,family_inner]

theorem combination_norm (T : ℝ≥0) (a : ElementaryInput T →₀ ℝ) :
    ‖outputLinear T a‖ = ‖inputLinear T a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq,← real_inner_self_eq_norm_sq,combination_inner]

/-- The original native span of actual elementary input classes. Its closure
is not silently identified with all predictable L2 functions. -/
def elementarySpan (T : ℝ≥0) : Submodule ℝ (Lp ℝ 2 (inputLaw T)) := (inputLinear T).range

theorem elementarySpan_eq_span (T : ℝ≥0) :
    elementarySpan T = Submodule.span ℝ (Set.range (inputValue (T := T))) :=
  Finsupp.range_linearCombination ℝ

private theorem combination_bound (T : ℝ≥0) :
    ∃ C : ℝ, ∀ a, ‖outputLinear T a‖ ≤ C * ‖inputLinear T a‖ :=
  ⟨1,fun a => by rw [combination_norm,one_mul]⟩

/-- Native compLeftInverse descends the ACTUAL output combinations through
the proved common kernel, directly to the original elementary L2 span. -/
def elementaryIntegral (T : ℝ≥0) : elementarySpan T →L[ℝ] Lp ℝ 2 sourceLaw :=
  (outputLinear T).compLeftInverse (inputLinear T)

theorem elementaryIntegral_image (T : ℝ≥0) (a : ElementaryInput T →₀ ℝ) :
    elementaryIntegral T ⟨inputLinear T a,⟨a,rfl⟩⟩ = outputLinear T a :=
  LinearMap.compLeftInverse_apply_of_bdd _ _ (combination_bound T) a _ rfl

theorem elementaryIntegral_norm (T : ℝ≥0) (x : elementarySpan T) :
    ‖elementaryIntegral T x‖ = ‖x‖ := by
  obtain ⟨a,ha⟩ := x.property
  have he : x = ⟨inputLinear T a,⟨a,rfl⟩⟩ := Subtype.ext ha.symm
  rw [he,elementaryIntegral_image,combination_norm]
  rfl

/-- The completed source domain is explicitly only the elementary-span
closure in the original time-times-source L2 space. -/
def integralDomain (T : ℝ≥0) : Submodule ℝ (Lp ℝ 2 (inputLaw T)) := (elementarySpan T).topologicalClosure

def inclusionIsometry (T : ℝ≥0) : elementarySpan T →ₗᵢ[ℝ] integralDomain T :=
  { Submodule.inclusion (elementarySpan T).le_topologicalClosure with norm_map' := fun _ => rfl }

theorem inclusion_dense (T : ℝ≥0) : DenseRange (inclusionIsometry T) := by
  change DenseRange (Set.inclusion (elementarySpan T).le_topologicalClosure)
  exact (denseRange_inclusion_iff (elementarySpan T).le_topologicalClosure).mpr (Set.Subset.refl _)

/-- Actual native continuous LINEAR extension; no desired extension map is
supplied as an argument. -/
def integral (T : ℝ≥0) : integralDomain T →L[ℝ] Lp ℝ 2 sourceLaw :=
  (elementaryIntegral T).extend (inclusionIsometry T).toContinuousLinearMap

theorem integral_agrees_elementary (T : ℝ≥0) (x : elementarySpan T) :
    integral T (inclusionIsometry T x) = elementaryIntegral T x := by
  unfold integral
  exact ContinuousLinearMap.extend_eq (e := (inclusionIsometry T).toContinuousLinearMap)
    (elementaryIntegral T) (inclusion_dense T) (inclusionIsometry T).isometry.isUniformInducing x

/-- The isometry on the actual elementary inputs survives completion. -/
theorem integral_norm (T : ℝ≥0) (x : integralDomain T) : ‖integral T x‖ = ‖x‖ := by
  refine (inclusion_dense T).induction_on x (isClosed_eq (integral T).continuous.norm continuous_norm) ?_
  intro y
  rw [integral_agrees_elementary,elementaryIntegral_norm]
  rfl

/-- The actual constructed continuous linear stochastic integral on the
explicit closure domain, bundled using the original native LinearIsometry. -/
def integralIsometry (T : ℝ≥0) : integralDomain T →ₗᵢ[ℝ] Lp ℝ 2 sourceLaw :=
  { (integral T).toLinearMap with norm_map' := integral_norm T }

/-- The actual elementary input's point in the ORIGINAL native span. -/
def elementaryPoint {T : ℝ≥0} (r : ElementaryInput T) : elementarySpan T :=
  ⟨inputValue r,⟨Finsupp.single r 1,by simp [inputLinear]⟩⟩

/-- Actual input in the explicitly named closure domain, with no change to
its native time-times-source L2 class. -/
def representedInput {T : ℝ≥0} (r : ElementaryInput T) : integralDomain T :=
  inclusionIsometry T (elementaryPoint r)

/-- The extended integral returns the SAME literal finite-strategy output
class for EVERY supplied elementary input record. -/
theorem integral_returns_literal {T : ℝ≥0} (r : ElementaryInput T) :
    integral T (representedInput r) = outputValue r := by
  rw [representedInput,integral_agrees_elementary]
  have he : elementaryPoint r =
      ⟨inputLinear T (Finsupp.single r 1),⟨Finsupp.single r 1,rfl⟩⟩ := by
    apply Subtype.ext
    simp [elementaryPoint,inputLinear]
  rw [he,elementaryIntegral_image]
  simp [outputLinear]

/-- Native continuous limit consumer, for every input in the EXPLICIT closed
span domain; no claim of full predictable density occurs in its type. -/
theorem integral_tendsto (T : ℝ≥0) {f : ℕ → integralDomain T} {x : integralDomain T}
    (hf : Filter.Tendsto f Filter.atTop (𝓝 x)) :
    Filter.Tendsto (fun n => integral T (f n)) Filter.atTop (𝓝 (integral T x)) :=
  ((integral T).continuous.tendsto x).comp hf

/-- A sequence of ACTUAL finite inputs converging in the original time-source
L2 norm yields convergence of their SAME literal output classes. -/
theorem literal_outputs_tendsto {T : ℝ≥0} (r : ℕ → ElementaryInput T) (x : integralDomain T)
    (hx : Filter.Tendsto (fun n => inputValue (r n)) Filter.atTop (𝓝 (x : Lp ℝ 2 (inputLaw T)))) :
    Filter.Tendsto (fun n => outputValue (r n)) Filter.atTop (𝓝 (integral T x)) := by
  have hsub : Filter.Tendsto (fun n => representedInput (r n)) Filter.atTop (𝓝 x) :=
    tendsto_subtype_rng.mpr hx
  simpa only [integral_returns_literal] using integral_tendsto T hsub

/-- Concrete bounded left-past input for the actual source: coefficient one
on (0,T], used to witness that completion preserved genuine execution noise. -/
def unitInput (T : ℝ≥0) : ElementaryInput T where
  n := 1
  clock := ![0,T]
  coefficient := fun _ _ => 1
  clock_mono := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  clock_zero := rfl
  clock_end := rfl
  coefficient_past := fun _ => stronglyMeasurable_const
  coefficient_bounded := fun _ => memLp_top_const 1

/-- Positive elapsed-time energy is derived for an ACTUAL constructed input
and the extended integral, not supplied as a nondegeneracy field. -/
theorem integral_unit_energy (T : ℝ≥0) :
    ‖integral T (representedInput (unitInput T))‖ ^ 2 = (T : ℝ) := by
  rw [integral_returns_literal,family_norm]
  change ‖inputClass T (unitInput T).clock (unitInput T).coefficient
    (unitInput T).coefficient_bounded‖ ^ 2 = (T : ℝ)
  rw [inputClass_norm_sq,integrand_energy T _ _ (unitInput T).clock_mono
    (unitInput T).clock_end.le (unitInput T).coefficient_bounded]
  change (∑ i : Fin 1, (((![0,T] i.succ : ℝ≥0) : ℝ) - ((![0,T] i.castSucc : ℝ≥0) : ℝ)) *
    (∫ _ω : ℝ≥0 → ℝ, (1 : ℝ)^2 ∂sourceLaw)) = (T : ℝ)
  rw [Fin.sum_univ_one]
  simp

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralClosure
