import UEOT.V3.InformationPredictiveCMI
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# P-INFO-02 — frozen-source wrapper

Frozen UEOT Core v3 P-INFO-02:

* `H,Y,M,U` are standard Borel;
* `M=fM(H)` and `U=fU(H)` are deterministic history statistics;
* `ε = I(H;Y | M,U)`;
* the expected TV distance between `P(Y|H)` and `P(Y|M,U)` is at most
  `sqrt(ε/2)`.

The pair statistic `h ↦ (fM h, fU h)` is the single deterministic statistic
used by the source-faithful predictive conditional-information layer.
-/

namespace UEOT.V3.InformationPInfo02

open MeasureTheory ProbabilityTheory
open UEOT.V3.TotalVariation
open UEOT.V3.InformationPredictiveCMI

universe uH uY uM uU

variable {H : Type uH} {Y : Type uY} {M : Type uM} {U : Type uU}
variable [MeasurableSpace H] [MeasurableSpace Y]
variable [MeasurableSpace M] [MeasurableSpace U]

/-- Pair the two source history statistics into the sufficient conditioning
statistic `(M,U)`. -/
def historyInterfaceStatistic
    (fM : H → M) (fU : H → U) : H → M × U :=
  fun h => (fM h, fU h)

theorem measurable_historyInterfaceStatistic
    {fM : H → M} {fU : H → U}
    (hfM : Measurable fM) (hfU : Measurable fU) :
    Measurable (historyInterfaceStatistic fM fU) :=
  hfM.prodMk hfU

/-- **P-INFO-02, finite-information real form.**

This is the literal predictive-kernel inequality in the frozen source, with
`ε` represented by `predictiveConditionalInfoStatistic` for the pair statistic
`(M,U)`.  The explicit `≠ ⊤` premise is only the typing condition needed to
render the right-hand side as an ordinary real square root. -/
theorem p_info_02_finite
    [StandardBorelSpace H] [StandardBorelSpace Y]
    [StandardBorelSpace M] [StandardBorelSpace U]
    [Nonempty Y]
    (μ : Measure (H × Y)) [IsProbabilityMeasure μ]
    (fM : H → M) (fU : H → U)
    (hfM : Measurable fM) (hfU : Measurable fU)
    (hfin :
      predictiveConditionalInfoStatistic μ
        (historyInterfaceStatistic fM fU)
        (measurable_historyInterfaceStatistic hfM hfU) ≠ ⊤) :
    (∫ h, tvDist
        (historyPredictiveKernel μ h)
        (statisticPredictiveKernel μ
          (historyInterfaceStatistic fM fU)
          (measurable_historyInterfaceStatistic hfM hfU) h) ∂μ.fst) ≤
      Real.sqrt
        ((predictiveConditionalInfoStatistic μ
          (historyInterfaceStatistic fM fU)
          (measurable_historyInterfaceStatistic hfM hfU)).toReal / 2) := by
  exact predictive_tv_le_sqrt_conditionalInfo μ
    (historyInterfaceStatistic fM fU)
    (measurable_historyInterfaceStatistic hfM hfU)
    hfin

/-- **P-INFO-02, all-cases extended-real form.**

This removes the finite-information side condition from the source interface.
For finite conditional information it is exactly `p_info_02_finite` after the
canonical `ℝ → ℝ≥0∞` coercion.  If the conditional information is infinite,
the extended-real right-hand side is infinite and the bound is automatic.
Thus no absolute-continuity or finiteness hypothesis is added to the frozen
source statement. -/
theorem p_info_02_ennreal
    [StandardBorelSpace H] [StandardBorelSpace Y]
    [StandardBorelSpace M] [StandardBorelSpace U]
    [Nonempty Y]
    (μ : Measure (H × Y)) [IsProbabilityMeasure μ]
    (fM : H → M) (fU : H → U)
    (hfM : Measurable fM) (hfU : Measurable fU) :
    ENNReal.ofReal
        (∫ h, tvDist
          (historyPredictiveKernel μ h)
          (statisticPredictiveKernel μ
            (historyInterfaceStatistic fM fU)
            (measurable_historyInterfaceStatistic hfM hfU) h) ∂μ.fst) ≤
      (predictiveConditionalInfoStatistic μ
          (historyInterfaceStatistic fM fU)
          (measurable_historyInterfaceStatistic hfM hfU) / 2) ^
        (1 / 2 : ℝ) := by
  let ε : ENNReal :=
    predictiveConditionalInfoStatistic μ
      (historyInterfaceStatistic fM fU)
      (measurable_historyInterfaceStatistic hfM hfU)
  change ENNReal.ofReal
      (∫ h, tvDist
        (historyPredictiveKernel μ h)
        (statisticPredictiveKernel μ
          (historyInterfaceStatistic fM fU)
          (measurable_historyInterfaceStatistic hfM hfU) h) ∂μ.fst) ≤
    (ε / 2) ^ (1 / 2 : ℝ)
  by_cases htop : ε = ⊤
  · rw [htop, ENNReal.top_div_of_ne_top (by norm_num : (2 : ENNReal) ≠ ⊤),
      ENNReal.top_rpow_of_pos (by norm_num : 0 < (1 / 2 : ℝ))]
    exact le_top
  · have hreal := p_info_02_finite μ fM fU hfM hfU (by simpa [ε] using htop)
    have hbound := ENNReal.ofReal_le_ofReal hreal
    have hbase : ENNReal.ofReal (ε.toReal / 2) = ε / 2 := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
        ENNReal.ofReal_toReal htop]
      norm_num
    have hrhs :
        ENNReal.ofReal (Real.sqrt (ε.toReal / 2)) =
          (ε / 2) ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      rw [← ENNReal.ofReal_rpow_of_nonneg
        (div_nonneg ENNReal.toReal_nonneg (by norm_num))
        (by norm_num : 0 ≤ (1 / 2 : ℝ))]
      rw [hbase]
    rw [hrhs] at hbound
    exact hbound

section SourceExact

variable [StandardBorelSpace H] [StandardBorelSpace Y]
variable [StandardBorelSpace M] [StandardBorelSpace U]
variable (μ : Measure (H × Y)) [IsProbabilityMeasure μ]

/-- A probability law on `H × Y` already implies that the target type `Y` is
nonempty.  Keeping this as a local instance removes the implementation-only
`[Nonempty Y]` premise from the canonical frozen-source theorem. -/
noncomputable local instance sourceTargetNonempty : Nonempty Y :=
  ⟨(nonempty_of_isProbabilityMeasure μ).some.2⟩

/-- **P-INFO-02, canonical frozen-source theorem.**

This theorem exposes exactly the source assumptions: standard-Borel variables,
a probability experiment law, and measurable deterministic history statistics
`M=fM(H)` and `U=fU(H)`.  Target nonemptiness is derived from the probability
law rather than added as an assumption.  The conclusion is the all-cases
extended-real form of `E TV ≤ sqrt(I(H;Y|M,U)/2)`. -/
theorem p_info_02_source
    (fM : H → M) (fU : H → U)
    (hfM : Measurable fM) (hfU : Measurable fU) :
    ENNReal.ofReal
        (∫ h, tvDist
          (historyPredictiveKernel μ h)
          (statisticPredictiveKernel μ
            (historyInterfaceStatistic fM fU)
            (measurable_historyInterfaceStatistic hfM hfU) h) ∂μ.fst) ≤
      (predictiveConditionalInfoStatistic μ
          (historyInterfaceStatistic fM fU)
          (measurable_historyInterfaceStatistic hfM hfU) / 2) ^
        (1 / 2 : ℝ) := by
  exact p_info_02_ennreal μ fM fU hfM hfU

end SourceExact

end UEOT.V3.InformationPInfo02
