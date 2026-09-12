import UEOT.V3.InformationPredictiveCMI

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
render the right-hand side as an ordinary real square root; an extended-real
wrapper can discharge the infinite case separately. -/
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

end UEOT.V3.InformationPInfo02
