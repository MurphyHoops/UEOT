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
    (A : Ω → ℝ) (hA : Measurable[m] A) :
    (condExpKernel μ m).map A =ᵐ[μ.trim hm]
      Kernel.deterministic A hA := by
  have hAΩ : Measurable A := hA.mono hm le_rfl
  have hcomp :=
    condDistrib_comp (μ := μ) (mβ := m)
      (Y := (id : Ω → Ω)) (id : Ω → Ω)
      measurable_id.aemeasurable hAΩ
  have hself :=
    condDistrib_comp_self (μ := μ) (mβ := m) (Ω := ℝ)
      (id : Ω → Ω) hA
  have hmap := hcomp.symm.trans hself
  rw [trim_eq_map hm, condExpKernel_eq]
  have hinf : m ⊓ mΩ = m := inf_of_le_left hm
  simpa [hinf] using hmap

end UEOT.V3.PredictableOLSKernelFreeze
