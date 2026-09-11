import Mathlib.Probability.Kernel.Condexp
import Mathlib.Tactic

/-!
# P-INV-05 — conditional-kernel freezing

A predictable coefficient is random globally but constant on the conditional
fibres determined by the past sigma-algebra.  This module isolates that fact at
the kernel level: mapping the conditional-expectation kernel through a
past-measurable real-valued function gives the deterministic kernel at its
current value.
-/

namespace UEOT.V3.PredictableOLSKernelFreeze

open MeasureTheory ProbabilityTheory

universe uΩ

variable {Ω : Type uΩ} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- A function measurable with respect to the conditioning sigma-algebra is
frozen on the fibres of `condExpKernel`.

Equivalently, conditionally on the past, its conditional law is the Dirac mass
at the already-observed value. -/
theorem condExpKernel_map_eq_deterministic
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) [Nonempty Ω]
    (A : Ω → ℝ) (hA : @Measurable Ω ℝ m inferInstance A) :
    Kernel.map (condExpKernel (mΩ := mΩ) μ m) A =ᵐ[μ.trim hm]
      @Kernel.deterministic Ω ℝ m inferInstance A hA := by
  have hinf : m ⊓ mΩ = m := inf_of_le_left hm
  have hminf : m ≤ m ⊓ mΩ := le_inf le_rfl hm
  have hAΩ : @Measurable Ω ℝ mΩ inferInstance A := by
    exact hA.mono hm le_rfl
  have hAinf : @Measurable Ω ℝ (m ⊓ mΩ) inferInstance A := by
    exact hA.mono hminf le_rfl
  have hcomp :=
    condDistrib_comp (μ := μ) (mβ := m ⊓ mΩ)
      (Y := (id : Ω → Ω))
      (id : Ω → Ω) measurable_id.aemeasurable hAΩ
  have hself :=
    condDistrib_comp_self (μ := μ) (mβ := m ⊓ mΩ) (Ω := ℝ)
      (id : Ω → Ω) hAinf
  have hmap := hcomp.symm.trans hself
  rw [condExpKernel_eq]
  rw [Kernel.comap_map_comm _ (measurable_id'' inf_le_left) hAΩ]
  rw [trim_eq_map hm]
  simpa [hinf] using hmap

end UEOT.V3.PredictableOLSKernelFreeze
