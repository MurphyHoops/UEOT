import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralTimeTruncation

/-!
Original commitment: the actual truncated integral must be the natural conditional prefix of its original output.
Existing result: actual source increments have zero conditional mean at their START, with original bounded-past outputs.
Premise reduced: derive arbitrary-observation-time conditional prefixes without granting future access to coefficients.
Model/witness: SAME actual process/sourceLaw/natural filtration and literal H times source increment.
Consumer: finite literal integration and native condExpL2 continuity; no full martingale field is assumed.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralConditionalStep
open MeasureTheory ProbabilityTheory Set
open BrownianContinuousSource BrownianProjectiveSource BrownianMartingaleSource BrownianOneStepIntegral
open BrownianCommonRefinement BrownianIntegralTimeTruncation
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Observation before a step uses the TOWER through its own start sigma;
its future coefficient is never pulled directly out of an earlier conditional expectation. -/
theorem oneStep_condExp_prefix {H : (ℝ≥0 → ℝ) → ℝ} (a b u : ℝ≥0) (hab : a ≤ b)
    (hHpast : StronglyMeasurable[naturalFiltration a] H) (hH : MemLp H ∞ sourceLaw) :
    sourceLaw[oneStep H a b | naturalFiltration u] =ᵐ[sourceLaw] oneStep H a (clamp a b u) := by
  by_cases hua : u ≤ a
  · have htower := condExp_condExp_of_le (μ := sourceLaw) (f := oneStep H a b)
      (naturalFiltration.mono hua) (naturalFiltration.le a)
    have hc : sourceLaw[sourceLaw[oneStep H a b | naturalFiltration a] | naturalFiltration u] =ᵐ[sourceLaw]
        sourceLaw[(0 : (ℝ≥0 → ℝ) → ℝ) | naturalFiltration u] :=
      condExp_congr_ae (oneStep_condExp_zero a b hab hHpast hH)
    rw [condExp_zero] at hc
    have hz := htower.symm.trans hc
    have he : clamp a b u = a := by simp only [clamp,min_eq_right (hua.trans hab),max_eq_left hua]
    filter_upwards [hz] with ω hω
    rw [hω]
    simp [oneStep,increment,he]
  · have hau : a ≤ u := (lt_of_not_ge hua).le
    by_cases hbu : b ≤ u
    · have hm := (oneStep_stronglyMeasurable_end a b hab hHpast).mono (naturalFiltration.mono hbu)
      have he : clamp a b u = b := by simp only [clamp,min_eq_left hbu,max_eq_right hab]
      rw [he,condExp_of_stronglyMeasurable (naturalFiltration.le u) hm (oneStep_integrable hH a b)]
    · have hub : u ≤ b := (lt_of_not_ge hbu).le
      have he : oneStep H a b = oneStep H a u+oneStep H u b := by
        funext ω
        simp only [oneStep,Pi.add_apply,Pi.mul_apply,increment]
        ring
      have hp := condExp_of_stronglyMeasurable (naturalFiltration.le u)
        (oneStep_stronglyMeasurable_end a u hau hHpast) (oneStep_integrable hH a u)
      have hf := oneStep_condExp_zero u b hub (hHpast.mono (naturalFiltration.mono hau)) hH
      have ha := condExp_add (oneStep_integrable hH a u) (oneStep_integrable hH u b) (naturalFiltration u)
      rw [he]
      apply ha.trans
      rw [hp]
      have hc : clamp a b u = u := by simp only [clamp,min_eq_right hub,max_eq_right hau]
      filter_upwards [hf] with ω hω
      simp only [Pi.add_apply,hω,add_zero,hc]

/-- Native L2 natural conditional projection on the ORIGINAL source law. -/
def naturalProjection (u : ℝ≥0) : Lp ℝ 2 sourceLaw →L[ℝ] Lp ℝ 2 sourceLaw :=
  (lpMeas ℝ ℝ (naturalFiltration u) 2 sourceLaw).subtypeL.comp
    (condExpL2 ℝ ℝ (naturalFiltration.le u))

/-- The proved conditional prefix identity, now in the original native source
L2 space, is the exact continuous interface used by the general integral. -/
theorem oneStep_projection_prefix {H : (ℝ≥0 → ℝ) → ℝ} (a b u : ℝ≥0) (hab : a ≤ b)
    (hHpast : StronglyMeasurable[naturalFiltration a] H) (hH : MemLp H ∞ sourceLaw) :
    naturalProjection u ((oneStep_memLp_two hH a b).toLp (oneStep H a b)) =
      (oneStep_memLp_two hH a (clamp a b u)).toLp (oneStep H a (clamp a b u)) := by
  apply Lp.ext
  exact ((oneStep_memLp_two hH a b).condExpL2_ae_eq_condExp (𝕜 := ℝ) (naturalFiltration.le u)).trans
    ((oneStep_condExp_prefix a b u hab hHpast hH).trans (oneStep_memLp_two hH a (clamp a b u)).coeFn_toLp.symm)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralConditionalStep
