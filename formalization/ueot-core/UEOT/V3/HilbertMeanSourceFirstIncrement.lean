import UEOT.V3.HilbertMeanDoobStatisticBridge
import UEOT.V3.HilbertMeanSourceFiberHoeffding
import UEOT.V3.HilbertMeanSubGaussianLawTransfer
import UEOT.V3.HilbertMeanPastActiveIndependence
import Mathlib.Tactic

/-!
# P-STAT-06 — first source Doob increment

At time zero the prefix consists of exactly coordinate `0`.  Hence the first
Doob increment is the active-coordinate continuation centered by its source
marginal mean.  This module isolates that representation and transfers the
exact `1/N²` Hoeffding proxy from the active marginal to the full product law.
-/

namespace UEOT.V3.HilbertMeanSourceFirstIncrement

open MeasureTheory ProbabilityTheory Real
open scoped NNReal
open UEOT.V3.HilbertMeanAzuma
open UEOT.V3.HilbertMeanConcentration
open UEOT.V3.HilbertMeanDoobBlocks
open UEOT.V3.HilbertMeanDoobCore
open UEOT.V3.HilbertMeanDoobStatisticBridge
open UEOT.V3.HilbertMeanPastActiveIndependence
open UEOT.V3.HilbertMeanPrefixFiltration
open UEOT.V3.HilbertMeanProductBlockIndependence
open UEOT.V3.HilbertMeanSourceActiveIntegrability
open UEOT.V3.HilbertMeanSourceCenteredFiber
open UEOT.V3.HilbertMeanSourceFiberHoeffding
open UEOT.V3.HilbertMeanSplitStatistic
open UEOT.V3.HilbertMeanSubGaussianLawTransfer
open UEOT.V3.HilbertMeanUnitClip

universe uH

variable {H : Type uH}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [MeasurableSpace H]

/-- The first valid sample index. -/
def firstIndex {N : ℕ} (hN : 0 < N) : Fin N := ⟨0, hN⟩

/-- A canonical zero background sample used only to parameterize the first
active-coordinate section. -/
def zeroSample {N : ℕ} : Fin N → H := fun _ => 0

/-- At time zero the revealed prefix of any sample agrees with the zero
background sample updated at coordinate `0` by the observed value. -/
theorem blockProjection_prefixBlock_zero_eq_update_zero
    {N : ℕ} (hN : 0 < N) (ω : Fin N → H) :
    blockProjection (prefixBlock (N := N) 0) ω =
      blockProjection (prefixBlock (N := N) 0)
        (Function.update (zeroSample (H := H)) (firstIndex hN)
          (ω (firstIndex hN))) := by
  funext j
  have hj0 : (j : Fin N).1 = 0 :=
    Nat.eq_zero_of_le_zero ((mem_prefixBlock_iff 0 (j : Fin N)).1 j.2)
  have hji : (j : Fin N) = firstIndex hN := Fin.ext hj0
  simp [blockProjection, zeroSample, hji]

/-- The time-zero source continuation is exactly a scalar section of the first
coordinate. -/
theorem sourceContinuation_first_eq_activeSection
    {N : ℕ} (hN : 0 < N)
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (μH : H) (ω : Fin N → H) :
    sourceContinuation μ (firstIndex hN) μH ω =
      sourceActiveSection μ (firstIndex hN) μH
        (zeroSample (H := H)) (ω (firstIndex hN)) := by
  unfold sourceActiveSection sourceContinuation
  have hblock :
      blockProjection (prefixBlock (N := N) (firstIndex hN).1) ω =
        blockProjection (prefixBlock (N := N) (firstIndex hN).1)
          (Function.update (zeroSample (H := H)) (firstIndex hN)
            (ω (firstIndex hN))) := by
    simpa [firstIndex] using
      blockProjection_prefixBlock_zero_eq_update_zero (H := H) hN ω
  rw [hblock]

/-- Raw first-coordinate continuation centered by its original marginal mean. -/
noncomputable def firstRawCentered
    {N : ℕ} (hN : 0 < N)
    (μ : Fin N → Measure H) (μH : H) (a : H) : ℝ :=
  sourceActiveSection μ (firstIndex hN) μH (zeroSample (H := H)) a -
    ∫ b, sourceActiveSection μ (firstIndex hN) μH
      (zeroSample (H := H)) b ∂μ (firstIndex hN)

/-- The actual first Doob increment is almost everywhere the raw centered first
active-coordinate section evaluated at the observed coordinate. -/
theorem doobIncrement_zero_ae_eq_firstRawCentered
    [BorelSpace H] [StandardBorelSpace H] [Nonempty H]
    [MeasurableAdd₂ H] [MeasurableSub H]
    {N : ℕ} (hN : 0 < N)
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (μH : H) (hμH : ‖μH‖ ≤ 1)
    (hunit : ∀ j, ∀ᵐ x ∂μ j, ‖x‖ ≤ 1) :
    doobIncrement
        (Measure.pi μ)
        (prefixFiltration (H := H) (N := N))
        (fun ω : Fin N → H => ‖empiricalMean ω - μH‖)
        0
      =ᵐ[Measure.pi μ]
      fun ω => firstRawCentered hN μ μH (ω (firstIndex hN)) := by
  let i0 : Fin N := firstIndex hN
  let P : Measure (Fin N → H) := Measure.pi μ
  let ℱ := prefixFiltration (H := H) (N := N)
  let F : (Fin N → H) → ℝ := fun ω => ‖empiricalMean ω - μH‖
  let q : H → ℝ :=
    sourceActiveSection μ i0 μH (zeroSample (H := H))
  have hzero : ∀ j : Fin N, ‖zeroSample (H := H) j‖ ≤ 1 := by
    intro j
    simp [zeroSample]
  have hqint : Integrable q (μ i0) := by
    simpa [q] using
      integrable_sourceActiveSection_of_unit
        hN μ (zeroSample (H := H)) hzero i0 μH hμH hunit
  have hdoob :=
    doobValue_meanError_ae_eq_sourceContinuation_of_unit
      hN μ i0 μH hμH hunit
  have hdoob0 :
      doobValue P ℱ F 0 =ᵐ[P]
        fun ω => q (ω i0) := by
    have hdoob' : doobValue P ℱ F 0 =ᵐ[P]
        sourceContinuation μ i0 μH := by
      simpa [P, ℱ, F, i0, firstIndex] using hdoob
    refine hdoob'.trans (Filter.Eventually.of_forall ?_)
    intro ω
    simpa [q, i0] using
      sourceContinuation_first_eq_activeSection hN μ μH ω
  have hcoord := activeCoordinate_hasLaw μ i0
  have hqcomp :
      (∫ ω, q (ω i0) ∂P) = ∫ a, q a ∂μ i0 := by
    have h := hcoord.integral_comp hqint.1
    simpa [P, Function.comp_def] using h
  have hcond :
      (∫ ω, doobValue P ℱ F 0 ω ∂P) = ∫ ω, F ω ∂P := by
    unfold doobValue
    exact integral_condExp (ℱ.le 0)
  have hmean :
      (∫ ω, F ω ∂P) = ∫ a, q a ∂μ i0 := by
    calc
      (∫ ω, F ω ∂P) = ∫ ω, doobValue P ℱ F 0 ω ∂P := hcond.symm
      _ = ∫ ω, q (ω i0) ∂P := integral_congr_ae hdoob0
      _ = ∫ a, q a ∂μ i0 := hqcomp
  change doobIncrement P ℱ F 0 =ᵐ[P]
    fun ω => firstRawCentered hN μ μH (ω (firstIndex hN))
  filter_upwards [hdoob0] with ω hω
  simp only [doobIncrement]
  rw [hω, hmean]
  rfl

/-- Exact ordinary sub-Gaussian proxy `1/N²` for the first source Doob
increment.  This is the `h0` input required by the Azuma layer. -/
theorem hasSubgaussianMGF_doobIncrement_zero_invSqParam
    [BorelSpace H] [StandardBorelSpace H] [Nonempty H]
    [MeasurableAdd₂ H] [MeasurableSub H]
    {N : ℕ} (hN : 0 < N)
    (μ : Fin N → Measure H) [∀ j, IsProbabilityMeasure (μ j)]
    (μH : H) (hμH : ‖μH‖ ≤ 1)
    (hunit : ∀ j, ∀ᵐ x ∂μ j, ‖x‖ ≤ 1) :
    HasSubgaussianMGF
      (doobIncrement
        (Measure.pi μ)
        (prefixFiltration (H := H) (N := N))
        (fun ω : Fin N → H => ‖empiricalMean ω - μH‖)
        0)
      (invSqParam N)
      (Measure.pi μ) := by
  let i0 : Fin N := firstIndex hN
  let q : H → ℝ := sourceActiveSection μ i0 μH (zeroSample (H := H))
  have hzero : ∀ j : Fin N, ‖zeroSample (H := H) j‖ ≤ 1 := by
    intro j
    simp [zeroSample]
  have hfiber :=
    hasSubgaussianMGF_centeredClippedActiveSection_invSqParam
      hN μ (zeroSample (H := H)) hzero i0 μH hμH hunit
  have hclipraw :
      centeredClippedActiveSection μ i0 μH (zeroSample (H := H))
        =ᵐ[μ i0]
      firstRawCentered hN μ μH := by
    have hclip := unitClip_ae_eq (μ i0) q (hunit i0)
    have hint := integral_unitClip_eq (μ i0) q (hunit i0)
    filter_upwards [hclip] with a ha
    simp [centeredClippedActiveSection, firstRawCentered, q, i0, ha, hint]
  have hraw : HasSubgaussianMGF
      (firstRawCentered hN μ μH) (invSqParam N) (μ i0) := by
    exact hfiber.congr_ae hclipraw
  have hcoord := activeCoordinate_hasLaw μ i0
  have hprod : HasSubgaussianMGF
      (fun ω : Fin N → H => firstRawCentered hN μ μH (ω i0))
      (invSqParam N) (Measure.pi μ) := by
    exact hraw.comp_hasLaw hcoord
  have hdoob := doobIncrement_zero_ae_eq_firstRawCentered
    hN μ μH hμH hunit
  exact hprod.congr_ae (by
    simpa [i0] using hdoob.symm)

end UEOT.V3.HilbertMeanSourceFirstIncrement
