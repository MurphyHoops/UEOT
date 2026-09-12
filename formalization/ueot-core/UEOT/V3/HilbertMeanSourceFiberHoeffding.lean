import UEOT.V3.HilbertMeanSourcePastFiber
import UEOT.V3.HilbertMeanAzuma
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic

/-!
# P-STAT-06 — ordinary Hoeffding on the source active-coordinate fiber

For a fixed source sample and active coordinate, the future-averaged active
section has oscillation at most `2/N` on the source unit ball.  After the
source-compatible clipping already established in `HilbertMeanUnitClip`, its
centered version therefore has ordinary sub-Gaussian proxy exactly `1/N²` under
the active marginal `μ i`.

This is the past-wise scalar input for the final conditional-MGF bridge.
-/

namespace UEOT.V3.HilbertMeanSourceFiberHoeffding

open MeasureTheory ProbabilityTheory Real
open scoped NNReal
open UEOT.V3.HilbertMeanAzuma
open UEOT.V3.HilbertMeanSourceCenteredFiber
open UEOT.V3.HilbertMeanSourceActiveIntegrability
open UEOT.V3.HilbertMeanSourcePastFiber
open UEOT.V3.HilbertMeanUnitClip

universe uH

variable {H : Type uH}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H]

/-- The clipped source active section centered by its own active-marginal mean. -/
noncomputable def centeredClippedActiveSection {N : ℕ}
    (μ : Fin N → Measure H) (i : Fin N) (μH : H)
    (ω : Fin N → H) (a : H) : ℝ :=
  unitClip (sourceActiveSection μ i μH ω) a -
    ∫ b, unitClip (sourceActiveSection μ i μH ω) b ∂μ i

private theorem hasSubgaussianMGF_centeredClippedActiveSection_of_data
    {N : ℕ} (hN : 0 < N)
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (ω : Fin N → H) (i : Fin N) (μH : H)
    (hunit : ∀ᵐ z ∂μ i, ‖z‖ ≤ 1)
    (hq : Integrable (sourceActiveSection μ i μH ω) (μ i))
    (hosc : ∀ a b, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
      |sourceActiveSection μ i μH ω a - sourceActiveSection μ i μH ω b| ≤
        2 / (N : ℝ)) :
    HasSubgaussianMGF
      (centeredClippedActiveSection μ i μH ω)
      (HilbertMeanAzuma.invSqParam N)
      (μ i) := by
  let q : H → ℝ := sourceActiveSection μ i μH ω
  let qc : H → ℝ := unitClip q
  let m : ℝ := ∫ a, qc a ∂μ i
  let a0 : ℝ := sInf (Set.range qc) - m
  let b0 : ℝ := sSup (Set.range qc) - m
  have hqc : Integrable qc (μ i) := by
    exact (integrable_unitClip_iff (μ i) q hunit).2 hq
  have hXmeas : AEMeasurable (centeredClippedActiveSection μ i μH ω) (μ i) := by
    have hsm : AEStronglyMeasurable qc (μ i) := hqc.1
    exact (hsm.sub aestronglyMeasurable_const).aemeasurable
  have hmem : ∀ᵐ x ∂μ i,
      centeredClippedActiveSection μ i μH ω x ∈ Set.Icc a0 b0 := by
    filter_upwards with x
    simpa [centeredClippedActiveSection, q, qc, m, a0, b0] using
      centered_unitClip_mem_exact_Icc (μ i) q hq hunit hosc x
  have hzero :
      (∫ x, centeredClippedActiveSection μ i μH ω x ∂μ i) = 0 := by
    simpa [centeredClippedActiveSection, q, qc, m] using
      integral_centered_unitClip_eq_zero (μ i) q hq hunit
  have hbase : HasSubgaussianMGF
      (centeredClippedActiveSection μ i μH ω)
      ((‖b0 - a0‖₊ / 2) ^ 2)
      (μ i) :=
    hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hXmeas hmem hzero
  have hoscNN : ∀ a b, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
      |q a - q b| ≤ (((2 : ℝ≥0) / (N : ℝ≥0)) : ℝ) := by
    intro a b ha hb
    simpa [q, NNReal.coe_div] using hosc a b ha hb
  have hwidth : ‖b0 - a0‖₊ ≤ (2 : ℝ≥0) / (N : ℝ≥0) := by
    simpa [q, qc, m, a0, b0] using
      centered_unitClip_exact_interval_nnnorm_le
        (μ i) q (c := (2 : ℝ≥0) / (N : ℝ≥0)) hq hunit hoscNN
  have hparam :
      (‖b0 - a0‖₊ / 2) ^ 2 ≤ HilbertMeanAzuma.invSqParam N := by
    have hNnn : (N : ℝ≥0) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hN)
    have hhalf :
        ((2 : ℝ≥0) / (N : ℝ≥0)) / 2 = (N : ℝ≥0)⁻¹ := by
      field_simp [hNnn]
    rw [HilbertMeanAzuma.invSqParam, ← hhalf]
    gcongr
  refine ⟨hbase.integrable_exp_mul, ?_⟩
  intro t
  calc
    mgf (centeredClippedActiveSection μ i μH ω) (μ i) t
        ≤ exp ((((‖b0 - a0‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) * t ^ 2 / 2) :=
      hbase.mgf_le t
    _ ≤ exp (((HilbertMeanAzuma.invSqParam N : ℝ≥0) : ℝ) * t ^ 2 / 2) := by
      apply Real.exp_le_exp.mpr
      gcongr

/-- For every fixed source sample, the centered clipped active fiber is exactly
`1/N²`-sub-Gaussian under the active marginal. -/
theorem hasSubgaussianMGF_centeredClippedActiveSection_invSqParam
    [BorelSpace H] [MeasurableAdd₂ H] [MeasurableSub H]
    {N : ℕ} (hN : 0 < N)
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (ω : Fin N → H) (hω : ∀ j, ‖ω j‖ ≤ 1)
    (i : Fin N) (μH : H) (hμH : ‖μH‖ ≤ 1)
    (hunit : ∀ j, ∀ᵐ z ∂μ j, ‖z‖ ≤ 1) :
    HasSubgaussianMGF
      (centeredClippedActiveSection μ i μH ω)
      (HilbertMeanAzuma.invSqParam N)
      (μ i) := by
  apply hasSubgaussianMGF_centeredClippedActiveSection_of_data
    hN μ ω i μH (hunit i)
  · exact integrable_sourceActiveSection_of_unit hN μ ω hω i μH hμH hunit
  · exact sourceActiveSection_pairwise_le_two_div_of_unit
      hN μ ω hω i μH hμH hunit

/-- The source-facing version needed by the conditional-MGF lift: only the
strict past must be pointwise in the unit ball.  The active and future
coordinates are controlled by their marginal a.e. support assumptions. -/
theorem hasSubgaussianMGF_centeredClippedActiveSection_invSqParam_of_pastUnit
    [BorelSpace H] [MeasurableAdd₂ H] [MeasurableSub H]
    {N : ℕ} (hN : 0 < N)
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (ω : Fin N → H) (i : Fin N)
    (hpast : ∀ j : UEOT.V3.HilbertMeanDoobBlocks.past i,
      ‖ω (j : Fin N)‖ ≤ 1)
    (μH : H) (hμH : ‖μH‖ ≤ 1)
    (hunit : ∀ j, ∀ᵐ z ∂μ j, ‖z‖ ≤ 1) :
    HasSubgaussianMGF
      (centeredClippedActiveSection μ i μH ω)
      (HilbertMeanAzuma.invSqParam N)
      (μ i) := by
  apply hasSubgaussianMGF_centeredClippedActiveSection_of_data
    hN μ ω i μH (hunit i)
  · exact integrable_sourceActiveSection_of_pastUnit
      hN μ ω i hpast μH hμH hunit
  · intro a b ha hb
    simpa [sourceActiveSection] using
      sourceContinuation_update_pairwise_le_two_div_of_pastUnit
        hN μ ω i hpast μH hμH a b ha hb hunit

end UEOT.V3.HilbertMeanSourceFiberHoeffding
