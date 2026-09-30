import UEOT.V3.Compression.ApproximateHistoryEncoder
import UEOT.V3.Compression.StructuralDefectControlLimit

/-!
# Vanishing history-encoder defects -> exact control descent

This module closes the finite approximate-history-encoder lane back onto the
exact control quotient interface.

The key point is reuse: the proof does not reimplement zero-defect exactness.
It feeds the encoder-generated representative macro model into the existing
second-order structural-defect closure theorem
`exactControlQuotient_of_vanishing_defects`.
-/

namespace UEOT.V3.Compression.HistoryEncoderExactClosure

open Filter Topology
open UEOT.V3
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.ApproximateHistoryEncoder
open UEOT.V3.Compression.StructuralDefectControlLimit

universe uH uS uA

/-- If the within-encoder-fibre reward and encoded-transition defects have
uniform envelopes tending to zero, the representative macro model is not only
approximately compatible with the micro model: it forms an exact control
quotient. -/
noncomputable def exactControlQuotient_of_vanishing_fiber_defects
    {H : Type uH} [Fintype H]
    {S : Type uS} [Fintype S]
    {Act : Type uA} [Fintype Act] [Nonempty Act]
    (C : H → S) (hC : Function.Surjective C)
    (micro : Model H (fun _ => Act))
    (εr εp : ℕ → ℝ)
    (hεr : Tendsto εr atTop (𝓝 0))
    (hεp : Tendsto εp atTop (𝓝 0))
    (hrewardFiber : ∀ n h h' a,
      C h = C h' →
        |micro.reward h a - micro.reward h' a| ≤ εr n)
    (htransitionFiber : ∀ n h h' a,
      C h = C h' →
        FiniteProbabilityRow.tvDist
          (pushforwardTransitionPMF C micro h a)
          (pushforwardTransitionPMF C micro h' a) ≤ εp n) :
    ExactControlQuotient H S (fun _ => Act) := by
  let macroModel := representativeMacroModel C hC micro
  apply exactControlQuotient_of_vanishing_defects
    C hC micro macroModel rfl εr εp hεr hεp
  · intro n h a
    change
      |micro.reward h a -
          micro.reward (representative C hC (C h)) a| ≤ εr n
    apply hrewardFiber n h (representative C hC (C h)) a
    exact (encoder_representative C hC (C h)).symm
  · intro n h a
    rw [representativeMacroModel_transitionPMF]
    apply htransitionFiber n h (representative C hC (C h)) a
    exact (encoder_representative C hC (C h)).symm

/-- Exact P-QUO-01 consequences generated from vanishing encoder-fibre
defects: exact optimal-value descent, exact optimal action-value descent, and
macro-greedy policy lifting against the full causal randomized policy class. -/
theorem p_quo_01_of_vanishing_fiber_defects
    {H : Type uH} [Fintype H]
    {S : Type uS} [Fintype S]
    {Act : Type uA} [Fintype Act] [Nonempty Act]
    (C : H → S) (hC : Function.Surjective C)
    (micro : Model H (fun _ => Act))
    (εr εp : ℕ → ℝ)
    (hεr : Tendsto εr atTop (𝓝 0))
    (hεp : Tendsto εp atTop (𝓝 0))
    (hrewardFiber : ∀ n h h' a,
      C h = C h' →
        |micro.reward h a - micro.reward h' a| ≤ εr n)
    (htransitionFiber : ∀ n h h' a,
      C h = C h' →
        FiniteProbabilityRow.tvDist
          (pushforwardTransitionPMF C micro h a)
          (pushforwardTransitionPMF C micro h' a) ≤ εp n) :
    let Q := exactControlQuotient_of_vanishing_fiber_defects
      C hC micro εr εp hεr hεp hrewardFiber htransitionFiber
    (∀ h : H,
      Q.micro.optimalValue h = Q.macroModel.optimalValue (Q.f h)) ∧
    (∀ (h : H) (a : Act),
      Q.micro.qValue Q.micro.optimalValue h a =
        Q.macroModel.qValue Q.macroModel.optimalValue (Q.f h) a) ∧
    (∀ {t : ℕ} (h : H),
      CausalPolicy.infiniteValue
          (selectorPolicy (Q.liftSelector Q.macroModel.greedyAction))
          Q.micro (t := t) h =
        Q.micro.optimalValue h) ∧
    (∀ (π : CausalPolicy H (fun _ => Act)) {t : ℕ} (h : π.Memory t),
      CausalPolicy.infiniteValue π Q.micro h ≤
        Q.micro.optimalValue (π.current h)) := by
  dsimp only
  exact (exactControlQuotient_of_vanishing_fiber_defects
    C hC micro εr εp hεr hεp hrewardFiber htransitionFiber).p_quo_01

/-- Zero fibre defects are the degenerate special case of the vanishing-defect
closure theorem. -/
noncomputable def exactControlQuotient_of_zero_fiber_defects
    {H : Type uH} [Fintype H]
    {S : Type uS} [Fintype S]
    {Act : Type uA} [Fintype Act] [Nonempty Act]
    (C : H → S) (hC : Function.Surjective C)
    (micro : Model H (fun _ => Act))
    (hrewardFiber : ∀ h h' a,
      C h = C h' →
        |micro.reward h a - micro.reward h' a| ≤ 0)
    (htransitionFiber : ∀ h h' a,
      C h = C h' →
        FiniteProbabilityRow.tvDist
          (pushforwardTransitionPMF C micro h a)
          (pushforwardTransitionPMF C micro h' a) ≤ 0) :
    ExactControlQuotient H S (fun _ => Act) := by
  apply exactControlQuotient_of_vanishing_fiber_defects
    C hC micro (fun _ => 0) (fun _ => 0)
      tendsto_const_nhds tendsto_const_nhds
  · intro n h h' a hsame
    exact hrewardFiber h h' a hsame
  · intro n h h' a hsame
    exact htransitionFiber h h' a hsame

end UEOT.V3.Compression.HistoryEncoderExactClosure
