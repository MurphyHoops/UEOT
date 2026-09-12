import UEOT.V3.HilbertMeanPastActiveAssembly
import UEOT.V3.HilbertMeanDoobStatisticBridge
import Mathlib.MeasureTheory.Integral.Prod

/-!
# P-STAT-06 — continuation as a past/active block function

The explicit source continuation depends only on the revealed prefix.  Since a
revealed prefix is exactly strict past plus the active coordinate, this module
factors the continuation through `(past i → H) × H`.  That representation is
the input needed by the block-independence conditional-expectation theorem.
-/

namespace UEOT.V3.HilbertMeanPastActiveContinuation

open MeasureTheory ProbabilityTheory
open UEOT.V3.HilbertMeanDoobBlocks
open UEOT.V3.HilbertMeanPrefixFiltration
open UEOT.V3.HilbertMeanProductBlockIndependence
open UEOT.V3.HilbertMeanPastActiveAssembly
open UEOT.V3.HilbertMeanSplitStatistic
open UEOT.V3.HilbertMeanDoobStatisticBridge

universe uH

variable {H : Type uH}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H]

/-- Continuation value as a function of an already assembled revealed prefix. -/
noncomputable def prefixContinuation {N : ℕ}
    (μ : Fin N → Measure H) (i : Fin N) (μH : H)
    (x : prefixBlock (N := N) i.1 → H) : ℝ :=
  ∫ y, splitMeanError i μH (x, y) ∂blockLaw μ (future i)

/-- The existing source continuation is exactly the prefix continuation applied
to the revealed-prefix projection. -/
theorem sourceContinuation_eq_prefixContinuation
    {N : ℕ} (μ : Fin N → Measure H) (i : Fin N) (μH : H)
    (ω : Fin N → H) :
    sourceContinuation μ i μH ω =
      prefixContinuation μ i μH
        (blockProjection (prefixBlock (N := N) i.1) ω) := by
  rfl

/-- Continuation value represented directly by strict-past and active blocks. -/
noncomputable def pastActiveContinuation {N : ℕ}
    (μ : Fin N → Measure H) (i : Fin N) (μH : H)
    (z : (past i → H) × H) : ℝ :=
  prefixContinuation μ i μH (assemblePastActive i z.1 z.2)

/-- On a full canonical sample, the past/active representation reproduces the
existing source continuation exactly. -/
@[simp] theorem pastActiveContinuation_blockProjection
    {N : ℕ} (μ : Fin N → Measure H) (i : Fin N) (μH : H)
    (ω : Fin N → H) :
    pastActiveContinuation μ i μH (blockProjection (past i) ω, ω i) =
      sourceContinuation μ i μH ω := by
  unfold pastActiveContinuation prefixContinuation sourceContinuation
  rw [assemblePastActive_blockProjection]

/-- Keeping the strict past fixed and inserting an arbitrary active value `a`
produces exactly the source continuation of the coordinate-updated sample. -/
@[simp] theorem pastActiveContinuation_blockProjection_update
    {N : ℕ} (μ : Fin N → Measure H) (i : Fin N) (μH : H)
    (ω : Fin N → H) (a : H) :
    pastActiveContinuation μ i μH (blockProjection (past i) ω, a) =
      sourceContinuation μ i μH (Function.update ω i a) := by
  unfold pastActiveContinuation prefixContinuation sourceContinuation
  rw [assemblePastActive_blockProjection_update]

/-- The past/active continuation is strongly measurable.  Future integration
preserves strong measurability because the strict-future block law is finite. -/
theorem stronglyMeasurable_pastActiveContinuation
    [BorelSpace H] [MeasurableAdd₂ H] [MeasurableSub H]
    {N : ℕ}
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (i : Fin N) (μH : H) :
    StronglyMeasurable (pastActiveContinuation μ i μH) := by
  letI : IsProbabilityMeasure (blockLaw μ (future i)) :=
    blockLaw_isProbability μ (future i)
  have hp : Measurable
      (fun z : ((past i → H) × H) × (future i → H) =>
        (assemblePastActive i z.1.1 z.1.2, z.2)) := by
    exact ((measurable_assemblePastActive (H := H) i).comp measurable_fst).prodMk
      measurable_snd
  have hg : StronglyMeasurable
      (fun z : ((past i → H) × H) × (future i → H) =>
        splitMeanError i μH (assemblePastActive i z.1.1 z.1.2, z.2)) :=
    ((measurable_splitMeanError (H := H) i μH).comp hp).stronglyMeasurable
  change StronglyMeasurable
    (fun z : (past i → H) × H =>
      ∫ y, splitMeanError i μH (assemblePastActive i z.1 z.2, y)
        ∂blockLaw μ (future i))
  exact hg.integral_prod_right

end UEOT.V3.HilbertMeanPastActiveContinuation
