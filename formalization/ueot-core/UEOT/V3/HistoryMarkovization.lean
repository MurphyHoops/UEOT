import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# P-PROC-01 — Markovization by history augmentation

A history-dependent controlled process can be represented as a time-homogeneous
Markov control problem once the full information needed by the original
transition law is carried as the state.

The carrier H is intentionally abstract: it may be the full growing history
(including time), and no finite-memory or finite-dimensional claim is made.

HistoryMachine.step : Kernel (H × A) X is the original history-dependent
one-step law. advance appends the sampled next state and the chosen action to
the history carrier. read recovers the newest physical state.

The Markovized transition is the single kernel on the augmented state:
  (h,a) ↦ sample x' ~ step(h,a); return advance((h,a),x').

The recovery theorem proves that reading the newest physical state after the
augmented transition gives exactly the original one-step kernel.
-/

namespace UEOT.V3.HistoryMarkovization

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe uH uA uX

variable {H : Type uH} {A : Type uA} {X : Type uX}
variable [MeasurableSpace H] [MeasurableSpace A] [MeasurableSpace X]

structure HistoryMachine (H : Type uH) (A : Type uA) (X : Type uX)
    [MeasurableSpace H] [MeasurableSpace A] [MeasurableSpace X] where
  step : Kernel (H × A) X
  advance : ((H × A) × X) → H
  measurable_advance : Measurable advance
  read : H → X
  measurable_read : Measurable read
  read_advance : ∀ z, read (advance z) = z.2

namespace HistoryMachine

noncomputable def markovized
    (M : HistoryMachine H A X) : Kernel (H × A) H :=
  (Kernel.id ×ₖ M.step).map M.advance

theorem isMarkovKernel_markovized
    (M : HistoryMachine H A X) [IsMarkovKernel M.step] :
    IsMarkovKernel M.markovized := by
  unfold markovized
  exact Kernel.IsMarkovKernel.map _ M.measurable_advance

theorem read_comp_advance
    (M : HistoryMachine H A X) :
    M.read ∘ M.advance = Prod.snd := by
  funext z
  exact M.read_advance z

theorem markovized_readout_eq_step
    (M : HistoryMachine H A X) [IsMarkovKernel M.step] :
    M.markovized.map M.read = M.step := by
  unfold markovized
  rw [← Kernel.map_comp_right _ M.measurable_advance M.measurable_read]
  rw [M.read_comp_advance]
  rw [← Kernel.snd_eq]
  simpa using Kernel.snd_prod Kernel.id M.step

/-- Existence form matching P-PROC-01: once the complete history carrier is
used as state, the history-dependent one-step law is represented by one
time-homogeneous Markov kernel on the augmented state, and the physical
next-state law is recovered by the measurable readout. -/
theorem exists_markovized_kernel
    (M : HistoryMachine H A X) [IsMarkovKernel M.step] :
    ∃ Q : Kernel (H × A) H,
      IsMarkovKernel Q ∧ Q.map M.read = M.step := by
  exact ⟨M.markovized,
    isMarkovKernel_markovized M,
    M.markovized_readout_eq_step⟩

theorem markovized_readout_apply
    (M : HistoryMachine H A X) [IsMarkovKernel M.step]
    (h : H) (a : A) :
    (M.markovized (h, a)).map M.read = M.step (h, a) := by
  have hEq := congrArg (fun κ : Kernel (H × A) X => κ (h, a))
    M.markovized_readout_eq_step
  rw [Kernel.map_apply _ M.measurable_read] at hEq
  exact hEq

theorem markovized_readout_event
    (M : HistoryMachine H A X) [IsMarkovKernel M.step]
    (h : H) (a : A) (B : Set X) (hB : MeasurableSet B) :
    M.markovized (h, a) (M.read ⁻¹' B) = M.step (h, a) B := by
  have hEq := congrArg (fun μ : Measure X => μ B)
    (M.markovized_readout_apply h a)
  simpa [Measure.map_apply M.measurable_read hB] using hEq


/-- Pointwise source-facing form of the Markovization witness: after augmenting
the state by history, one Markov step followed by the physical readout
recovers exactly the original history-dependent one-step law. -/
theorem markovized_kernel_readout_apply
    (M : HistoryMachine H A X) [IsMarkovKernel M.step]
    (h : H) (a : A) :
    (M.markovized (h, a)).map M.read = M.step (h, a) :=
  M.markovized_readout_apply h a

end HistoryMachine

end UEOT.V3.HistoryMarkovization
