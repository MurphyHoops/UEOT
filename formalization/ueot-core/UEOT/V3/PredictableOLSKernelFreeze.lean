import Mathlib.Probability.Kernel.Condexp
import Mathlib.Tactic

/-!
# P-INV-05 — conditional-kernel freezing

A predictable coefficient is random globally but constant on conditional
fibres determined by the past sigma-algebra.  The clean route is through the
joint law of the conditioning point and its conditional copy:

`(μ.trim hm) ⊗ₘ condExpKernel μ m = μ.map Function.diag`.

The right-hand side is concentrated on the diagonal, so every `m`-measurable
coefficient has the same value at the conditioning point and at the conditional
copy, almost everywhere.
-/

namespace UEOT.V3.PredictableOLSKernelFreeze

open MeasureTheory ProbabilityTheory Filter

universe uΩ

variable {Ω : Type uΩ} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- A past-measurable coefficient is constant on almost every fibre of the
conditional-expectation kernel.  This is the precise freezing statement needed
for predictable random multipliers in the P-INV-05 conditional-MGF proof. -/
theorem predictable_ae_eq_const
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (A : Ω → ℝ) (hA : @Measurable Ω ℝ m inferInstance A) :
    ∀ᵐ ω ∂(μ.trim hm), ∀ᵐ y ∂(condExpKernel (mΩ := mΩ) μ m ω), A y = A ω := by
  have hAΩ : @Measurable Ω ℝ mΩ inferInstance A := hA.mono hm le_rfl
  letI mprod : MeasurableSpace (Ω × Ω) := m.prod mΩ
  have hdiag : @Measurable Ω (Ω × Ω) mΩ mprod Function.diag := by
    exact (measurable_id'' hm).prodMk measurable_id
  have hfst : Measurable (fun p : Ω × Ω => A p.1) := hA.comp measurable_fst
  have hsnd : Measurable (fun p : Ω × Ω => A p.2) := hAΩ.comp measurable_snd
  have hp : MeasurableSet {p : Ω × Ω | A p.2 = A p.1} :=
    measurableSet_eq_fun hsnd hfst
  refine Measure.ae_ae_of_ae_compProd
    (μ := μ.trim hm) (κ := condExpKernel (mΩ := mΩ) μ m)
    (p := fun p : Ω × Ω => A p.2 = A p.1) ?_
  rw [compProd_trim_condExpKernel (mΩ := mΩ) (μ := μ) hm]
  exact (ae_map_iff hdiag.aemeasurable hp).2 (Eventually.of_forall fun ω => rfl)

end UEOT.V3.PredictableOLSKernelFreeze
