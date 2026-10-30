import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQIntegralClosure
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralConditionalStep

/-!
Original commitment: actual ownQ integration needs genuine original-Fs conditional prefixes, not only mean-zero terminal outputs.
Existing result: SAME W is Brownian with whole future independent of ENTIRE original Fs under actual normalized Q; actual bounded START step moments are derived.
Premise reduced: prove arbitrary observation-time conditional prefix by native tower/splitting and expose native condExpL2 projection on SAME Q.
Model/witness: fixed original bounded control f/A/K/Q, arbitrary a≤b and observation u, H only original Fs_a measurable and Q-essentially bounded, u before/within/after block.
Consumer/boundary: actual literal-Q time paths and closed-span conditional process; no shifted-natural-filtration equality, fullQ predictable density or general Ito field is assumed.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQConditionalStep
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianMartingaleSource BrownianCommonRefinement
open BrownianTimeIntegrand BrownianPredictableInputs BrownianBoundedControlSource BrownianBoundedExponentialLimitSource
open BrownianOwnQOneStepIntegral
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
variable (A : ℝ≥0) (f : fullPredictableL2 A) (K : ℝ) (hK : 0≤K)
    (hF : ∀ᵐ p ∂inputLaw A, |(f : Lp ℝ 2 (inputLaw A)) p|≤K)
include hK hF

/-- Before the block, tower through its START sigma-algebra. Future H is
never pulled out of an earlier conditional expectation. Inside, split the
actual W increment at u; after, use actual original-Fs endpoint measurability. -/
theorem oneStep_condExp_prefix {H : (ℝ≥0 → ℝ) → ℝ} (a b u : ℝ≥0) (hab : a≤b)
    (hHpast : StronglyMeasurable[naturalFiltration a] H) (hH : MemLp H ∞ (fullLaw A f)) :
    (fullLaw A f)[oneStep A f K H a b | naturalFiltration u]=ᵐ[fullLaw A f]
      oneStep A f K H a (clamp a b u) := by
  let _ := fullLaw_probability A f K hK hF
  by_cases hua : u≤a
  · have htower := condExp_condExp_of_le (μ := fullLaw A f) (f := oneStep A f K H a b)
      (naturalFiltration.mono hua) (naturalFiltration.le a)
    have hc : (fullLaw A f)[(fullLaw A f)[oneStep A f K H a b | naturalFiltration a] | naturalFiltration u]=ᵐ[fullLaw A f]
        (fullLaw A f)[(0 : (ℝ≥0 → ℝ) → ℝ) | naturalFiltration u] :=
      condExp_congr_ae (oneStep_condExp_zero A f K hK hF a b hab hHpast hH)
    rw [condExp_zero] at hc
    have hz := htower.symm.trans hc
    have he : clamp a b u=a := by simp only [clamp,min_eq_right (hua.trans hab),max_eq_left hua]
    filter_upwards [hz] with ω hω
    rw [hω]
    simp [oneStep,BrownianBoundedGirsanovSource.fullIncrement,he]
  · have hau : a≤u := (lt_of_not_ge hua).le
    by_cases hbu : b≤u
    · have hm := (oneStep_past_end A f K a b hab hHpast).mono (naturalFiltration.mono hbu)
      have he : clamp a b u=b := by simp only [clamp,min_eq_left hbu,max_eq_right hab]
      rw [he,condExp_of_stronglyMeasurable (naturalFiltration.le u) hm
        ((oneStep_memLp_two A f K hK hF hH a b).integrable one_le_two)]
    · have hub : u≤b := (lt_of_not_ge hbu).le
      have he : oneStep A f K H a b=oneStep A f K H a u+oneStep A f K H u b := by
        funext ω
        simp only [oneStep,Pi.add_apply,Pi.mul_apply,BrownianBoundedGirsanovSource.fullIncrement]
        ring
      have hp := condExp_of_stronglyMeasurable (naturalFiltration.le u)
        (oneStep_past_end A f K a u hau hHpast) ((oneStep_memLp_two A f K hK hF hH a u).integrable one_le_two)
      have hf := oneStep_condExp_zero A f K hK hF u b hub (hHpast.mono (naturalFiltration.mono hau)) hH
      have ha := condExp_add ((oneStep_memLp_two A f K hK hF hH a u).integrable one_le_two)
        ((oneStep_memLp_two A f K hK hF hH u b).integrable one_le_two) (naturalFiltration u)
      rw [he]
      apply ha.trans
      rw [hp]
      have hc : clamp a b u=u := by simp only [clamp,min_eq_right hub,max_eq_right hau]
      filter_upwards [hf] with ω hω
      simp only [Pi.add_apply,hω,add_zero,hc]

/-- Native conditional L2 projection under SAME actual Q and ORIGINAL Fs. -/
def naturalProjection (u : ℝ≥0) : Lp ℝ 2 (fullLaw A f) →L[ℝ] Lp ℝ 2 (fullLaw A f) :=
  (lpMeas ℝ ℝ (naturalFiltration u) 2 (fullLaw A f)).subtypeL.comp
    (condExpL2 ℝ ℝ (naturalFiltration.le u))

theorem oneStep_projection_prefix {H : (ℝ≥0 → ℝ) → ℝ} (a b u : ℝ≥0) (hab : a≤b)
    (hHpast : StronglyMeasurable[naturalFiltration a] H) (hH : MemLp H ∞ (fullLaw A f)) :
    naturalProjection A f u ((oneStep_memLp_two A f K hK hF hH a b).toLp (oneStep A f K H a b))=
      (oneStep_memLp_two A f K hK hF hH a (clamp a b u)).toLp (oneStep A f K H a (clamp a b u)) := by
  let _ := fullLaw_probability A f K hK hF
  apply Lp.ext
  exact ((oneStep_memLp_two A f K hK hF hH a b).condExpL2_ae_eq_condExp (𝕜 := ℝ) (naturalFiltration.le u)).trans
    ((oneStep_condExp_prefix A f K hK hF a b u hab hHpast hH).trans
      (oneStep_memLp_two A f K hK hF hH a (clamp a b u)).coeFn_toLp.symm)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQConditionalStep
