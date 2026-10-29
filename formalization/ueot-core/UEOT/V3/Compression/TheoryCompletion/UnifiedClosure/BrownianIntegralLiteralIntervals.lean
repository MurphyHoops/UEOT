import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralConditionalStep

/-!
Original commitment: the actual full predictable integral must consume each supplied finite interval action.
Existing result: full predictable source is constructed and literal weighted increments have genuine conditional prefixes.
Premise reduced: bind actual bounded past interval inputs to their SAME literal source increments.
Model/witness: SAME fixed inputLaw T/sourceLaw and explicit clock[0,a,b,T], coefficients[0,H,0].
Consumer: actual truncation/conditional martingale bridge; no substitute output is chosen.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralLiteralIntervals
open MeasureTheory ProbabilityTheory Set
open BrownianContinuousSource BrownianProjectiveSource BrownianMartingaleSource BrownianOneStepIntegral
open BrownianSimplePredictableIntegral BrownianCommonRefinement BrownianTimeIntegrand BrownianIntegralClosure
open BrownianPredictableInputs BrownianPredictableDensity BrownianIntegralTimeTruncation BrownianIntegralConditionalStep
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Actual finite input record with zero before/after the one allowed block.
Only H's original START permission is supplied; no integral certificate is a field. -/
def intervalRecord (T a b : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T)
    (H : (ℝ≥0 → ℝ) → ℝ) (hHpast : StronglyMeasurable[naturalFiltration a] H)
    (hH : MemLp H ∞ sourceLaw) : ElementaryInput T where
  n := 3
  clock := ![0,a,b,T]
  coefficient := ![fun _ => 0,H,fun _ => 0]
  clock_mono := by
    have haT := hab.trans hbT
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  clock_zero := rfl
  clock_end := rfl
  coefficient_past := by
    intro i
    fin_cases i
    · exact stronglyMeasurable_const
    · exact hHpast
    · exact stronglyMeasurable_const
  coefficient_bounded := by
    intro i
    fin_cases i
    · exact MemLp.zero
    · exact hH
    · exact MemLp.zero

/-- Actual interval class inside the independently defined full predictable L2. -/
def intervalInput (T a b : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T)
    (H : (ℝ≥0 → ℝ) → ℝ) (hHpast : StronglyMeasurable[naturalFiltration a] H)
    (hH : MemLp H ∞ sourceLaw) : fullPredictableL2 T :=
  literalPredictableInput (intervalRecord T a b hab hbT H hHpast hH)

theorem intervalInput_coe (T a b : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T)
    (H : (ℝ≥0 → ℝ) → ℝ) (hHpast : StronglyMeasurable[naturalFiltration a] H)
    (hH : MemLp H ∞ sourceLaw) :
    (intervalInput T a b hab hbT H hHpast hH : Lp ℝ 2 (inputLaw T)) =ᵐ[inputLaw T] intervalIntegrand H a b := by
  let r := intervalRecord T a b hab hbT H hHpast hH
  apply (integrand_memLp_two T r.clock r.coefficient r.coefficient_bounded).coeFn_toLp.trans
  apply Filter.Eventually.of_forall
  intro p
  change (∑ i : Fin 3, intervalIntegrand (![fun _ => 0,H,fun _ => 0] i)
    (![0,a,b,T] i.castSucc) (![0,a,b,T] i.succ) p) = intervalIntegrand H a b p
  simp [Fin.sum_univ_succ,intervalIntegrand]

theorem intervalRecord_output (T a b : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T)
    (H : (ℝ≥0 → ℝ) → ℝ) (hHpast : StronglyMeasurable[naturalFiltration a] H)
    (hH : MemLp H ∞ sourceLaw) :
    outputValue (intervalRecord T a b hab hbT H hHpast hH) =
      (oneStep_memLp_two hH a b).toLp (oneStep H a b) := by
  let r := intervalRecord T a b hab hbT H hHpast hH
  apply Lp.ext
  apply (simpleIntegral_memLp_two r.clock r.coefficient r.coefficient_bounded).coeFn_toLp.trans
  apply Filter.EventuallyEq.trans _ (oneStep_memLp_two hH a b).coeFn_toLp.symm
  apply Filter.Eventually.of_forall
  intro ω
  change (∑ i : Fin 3, oneStep (![fun _ => 0,H,fun _ => 0] i)
    (![0,a,b,T] i.castSucc) (![0,a,b,T] i.succ) ω) = oneStep H a b ω
  simp [Fin.sum_univ_succ,oneStep]

/-- Full predictableIntegral returns the SAME literal H times actual source
increment for the explicit supplied block input. -/
theorem integral_interval_literal (T a b : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T)
    (H : (ℝ≥0 → ℝ) → ℝ) (hHpast : StronglyMeasurable[naturalFiltration a] H)
    (hH : MemLp H ∞ sourceLaw) :
    predictableIntegral T (intervalInput T a b hab hbT H hHpast hH) =
      (oneStep_memLp_two hH a b).toLp (oneStep H a b) := by
  rw [intervalInput,predictableIntegral_returns_literal,intervalRecord_output]

private theorem cutoff_interval_eq (T a b u : ℝ≥0) (hbT : b ≤ T)
    (H : (ℝ≥0 → ℝ) → ℝ) :
    (timeSet T u).indicator (intervalIntegrand H a b) = intervalIntegrand H a (clamp a b u) := by
  funext p
  have hmem : (p ∈ timeSet T u ∧ p.1 ∈ Ioc (a : ℝ) (b : ℝ)) ↔
      p.1 ∈ Ioc (a : ℝ) (clamp a b u : ℝ≥0) := by
    simp only [timeSet,mem_prod,mem_Ioc,mem_univ,and_true,clamp,NNReal.coe_max,NNReal.coe_min]
    constructor
    · intro h
      exact ⟨h.2.1,(le_min h.2.2 (h.1.2.trans (min_le_left _ _))).trans (le_max_right _ _)⟩
    · intro h
      have hx : p.1 ≤ min (b : ℝ) (u : ℝ) := (le_max_iff.mp h.2).resolve_left (not_le.mpr h.1)
      have hbt : (b : ℝ) ≤ (T : ℝ) := by exact_mod_cast hbT
      exact ⟨⟨a.coe_nonneg.trans_lt h.1,
        le_min (hx.trans (min_le_right _ _)) ((hx.trans (min_le_left _ _)).trans hbt)⟩,
        ⟨h.1,hx.trans (min_le_left _ _)⟩⟩
  by_cases hc : p ∈ timeSet T u
  · by_cases hi : p.1 ∈ Ioc (a : ℝ) (b : ℝ)
    · have hp := hmem.mp ⟨hc,hi⟩
      simp [intervalIntegrand,hc,hi,hp]
    · have hp : p.1 ∉ Ioc (a : ℝ) (clamp a b u : ℝ≥0) := fun hp => hi (hmem.mpr hp).2
      simp [intervalIntegrand,hc,hi,hp]
  · have hp : p.1 ∉ Ioc (a : ℝ) (clamp a b u : ℝ≥0) := fun hp => hc (hmem.mpr hp).1
    simp [intervalIntegrand,hc,hp]

/-- The ACTUAL cutoff operator on a supplied interval input is precisely the
same interval input with its source endpoint clamped. -/
theorem truncate_intervalInput (T a b u : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T)
    (H : (ℝ≥0 → ℝ) → ℝ) (hHpast : StronglyMeasurable[naturalFiltration a] H)
    (hH : MemLp H ∞ sourceLaw) :
    truncate T u (intervalInput T a b hab hbT H hHpast hH) =
      intervalInput T a (clamp a b u) (clamp_bounds a b u hab).1
        ((clamp_bounds a b u hab).2.trans hbT) H hHpast hH := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [truncate_coe T u (intervalInput T a b hab hbT H hHpast hH),
    intervalInput_coe T a b hab hbT H hHpast hH,
    intervalInput_coe T a (clamp a b u) (clamp_bounds a b u hab).1
      ((clamp_bounds a b u hab).2.trans hbT) H hHpast hH] with p hp hi hj
  rw [hp,hj]
  calc
    _ = (timeSet T u).indicator (intervalIntegrand H a b) p := by
      by_cases hc : p ∈ timeSet T u <;> simp [hc,hi]
    _ = _ := congrFun (cutoff_interval_eq T a b u hbT H) p

/-- The actual truncated full-integral source agrees with the genuine natural
conditional projection of the original SAME interval output. -/
theorem projection_integral_interval (T a b u : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T)
    (H : (ℝ≥0 → ℝ) → ℝ) (hHpast : StronglyMeasurable[naturalFiltration a] H)
    (hH : MemLp H ∞ sourceLaw) :
    naturalProjection u (predictableIntegral T (intervalInput T a b hab hbT H hHpast hH)) =
      integralClassProcess T (intervalInput T a b hab hbT H hHpast hH) u := by
  rw [integral_interval_literal,oneStep_projection_prefix a b u hab hHpast hH,
    integralClassProcess,truncate_intervalInput,integral_interval_literal]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralLiteralIntervals
