import UEOT.V3.FiniteHistoryMeasurable
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# P-PROC-01 — concrete growing-history Markovization

For an arbitrary family of history-dependent controlled kernels

  q n : Kernel (HistoryFiber X A n × A) X,

we first form the fixed-time augmented transition that samples the next state
and appends the selected action and sample to the full history.  We then glue
these fixed-time kernels along the countable Sigma carrier.  The result is one
kernel whose definition no longer changes with external time: the time index
is part of its state-action input.

No finite-memory claim is made; the history fiber grows with n.
-/

namespace UEOT.V3.ConcreteHistoryMarkovization

open MeasureTheory ProbabilityTheory
open UEOT.V3.FiniteHistory
open UEOT.V3.FiniteHistoryMeasurable
open scoped ProbabilityTheory

universe uX uA uY

variable {X : Type uX} {A : Type uA} {Y : Type uY}
variable [MeasurableSpace X] [MeasurableSpace A]

/-- State-action carrier with the time index internalized.  It is the Sigma
reassociation of `(Σ n, H_n) × A`. -/
abbrev ControlCarrier (X : Type uX) (A : Type uA) :=
  Sigma fun n => HistoryFiber X A n × A

/-- Branchwise measurable criterion for the dependent state-action carrier. -/
theorem measurable_of_forall_controlFiber
    [MeasurableSpace Y]
    (f : ControlCarrier X A → Y)
    (hf : ∀ n, Measurable
      (fun z : HistoryFiber X A n × A => f ⟨n, z⟩)) :
    Measurable f := by
  rw [measurable_iff_comap_le]
  change _ ≤
    ⨅ n, (inferInstance : MeasurableSpace (HistoryFiber X A n × A)).map
      (Sigma.mk n)
  refine le_iInf fun n => ?_
  apply MeasurableSpace.comap_le_iff_le_map.1
  change
    MeasurableSpace.comap (Sigma.mk n)
        (MeasurableSpace.comap f (inferInstance : MeasurableSpace Y)) ≤
      (inferInstance : MeasurableSpace (HistoryFiber X A n × A))
  rw [MeasurableSpace.comap_comp]
  exact (hf n).comap_le

/-- The supplied time-indexed family is already one measurable kernel after
time is internalized as the Sigma tag. -/
noncomputable def controlStep
    (q : ∀ n, Kernel (HistoryFiber X A n × A) X) :
    Kernel (ControlCarrier X A) X where
  toFun z := q z.1 z.2
  measurable' :=
    measurable_of_forall_controlFiber
      (fun z : ControlCarrier X A => q z.1 z.2)
      (fun n => Kernel.measurable (q n))

@[simp] theorem controlStep_apply
    (q : ∀ n, Kernel (HistoryFiber X A n × A) X)
    (n : ℕ) (z : HistoryFiber X A n × A) :
    controlStep q ⟨n, z⟩ = q n z := rfl

/-- Fixed-time augmented step: preserve the full current history/action,
sample x' from q_n, then append action and x'. -/
noncomputable def fixedAugmented
    (n : ℕ) (q : Kernel (HistoryFiber X A n × A) X) :
    Kernel (HistoryFiber X A n × A) (Carrier X A) :=
  (Kernel.id ×ₖ q).map
    (fun p : (HistoryFiber X A n × A) × X =>
      Carrier.advance (⟨n, p.1.1⟩ : Carrier X A) p.1.2 p.2)

theorem fixedAugmented_apply
    (n : ℕ) (q : Kernel (HistoryFiber X A n × A) X)
    (z : HistoryFiber X A n × A) :
    fixedAugmented n q z =
      ((Kernel.id ×ₖ q) z).map
        (fun p : (HistoryFiber X A n × A) × X =>
          Carrier.advance (⟨n, p.1.1⟩ : Carrier X A) p.1.2 p.2) := by
  rw [fixedAugmented, Kernel.map_apply]
  exact measurable_advance_fixed n

/-- One global time-homogeneous controlled transition on the augmented
state-action carrier. -/
noncomputable def augmentedKernel
    (q : ∀ n, Kernel (HistoryFiber X A n × A) X) :
    Kernel (ControlCarrier X A) (Carrier X A) where
  toFun z := fixedAugmented z.1 (q z.1) z.2
  measurable' :=
    measurable_of_forall_controlFiber
      (fun z : ControlCarrier X A => fixedAugmented z.1 (q z.1) z.2)
      (fun n => Kernel.measurable (fixedAugmented n (q n)))

@[simp] theorem augmentedKernel_apply
    (q : ∀ n, Kernel (HistoryFiber X A n × A) X)
    (n : ℕ) (z : HistoryFiber X A n × A) :
    augmentedKernel q ⟨n, z⟩ = fixedAugmented n (q n) z := rfl

/-- The deterministic history update used by the augmented kernel advances
the internal time tag by exactly one.  This is the source transition
`(t,h,a,x') ↦ (t+1,h,a,x')` at the carrier level. -/
theorem augmentedStep_time
    (n : ℕ) (z : HistoryFiber X A n × A) (x' : X) :
    Carrier.time
        (Carrier.advance (⟨n, z.1⟩ : Carrier X A) z.2 x') =
      n + 1 := by
  rfl


/-- A fixed-time augmented step is Markov whenever the supplied next-state
kernel is Markov. -/
theorem isMarkovKernel_fixedAugmented
    (n : ℕ) (q : Kernel (HistoryFiber X A n × A) X)
    [IsMarkovKernel q] :
    IsMarkovKernel (fixedAugmented n q) := by
  unfold fixedAugmented
  exact Kernel.IsMarkovKernel.map _ (measurable_advance_fixed n)

/-- The countably glued augmented transition is a Markov kernel whenever every
source history-dependent kernel q_t is Markov. -/
theorem isMarkovKernel_augmentedKernel
    (q : ∀ n, Kernel (HistoryFiber X A n × A) X)
    (hq : ∀ n, IsMarkovKernel (q n)) :
    IsMarkovKernel (augmentedKernel q) := by
  constructor
  rintro ⟨n, z⟩
  letI : IsMarkovKernel (q n) := hq n
  letI : IsMarkovKernel (fixedAugmented n (q n)) :=
    isMarkovKernel_fixedAugmented n (q n)
  change IsProbabilityMeasure (fixedAugmented n (q n) z)
  infer_instance

/-- Reading the newest physical state after a fixed-time augmented transition
recovers exactly the original history-dependent next-state kernel. -/
theorem fixedAugmented_current_eq
    (n : ℕ) (q : Kernel (HistoryFiber X A n × A) X)
    [IsMarkovKernel q] :
    (fixedAugmented n q).map Carrier.current = q := by
  unfold fixedAugmented
  rw [← Kernel.map_comp_right _ (measurable_advance_fixed n) measurable_current]
  have hcomp :
      Carrier.current ∘
          (fun p : (HistoryFiber X A n × A) × X =>
            Carrier.advance
              (⟨n, p.1.1⟩ : Carrier X A) p.1.2 p.2) =
        Prod.snd := by
    funext p
    exact Carrier.current_advance
      (⟨n, p.1.1⟩ : Carrier X A) p.1.2 p.2
  rw [hcomp]
  rw [← Kernel.snd_eq]
  simpa using Kernel.snd_prod Kernel.id q

/-- Source-facing pointwise recovery clause for P-PROC-01. -/
theorem augmentedKernel_current_apply
    (q : ∀ n, Kernel (HistoryFiber X A n × A) X)
    (hq : ∀ n, IsMarkovKernel (q n))
    (n : ℕ) (z : HistoryFiber X A n × A) :
    (augmentedKernel q ⟨n, z⟩).map Carrier.current = q n z := by
  letI : IsMarkovKernel (q n) := hq n
  have hEq := congrArg
    (fun κ : Kernel (HistoryFiber X A n × A) X => κ z)
    (fixedAugmented_current_eq n (q n))
  rw [Kernel.map_apply _ measurable_current] at hEq
  simpa using hEq

/-- P-PROC-01 source wrapper: an arbitrary family of history-dependent Markov
control kernels is represented by one time-homogeneous Markov kernel on the
time-tagged augmented state-action carrier, and its physical readout is exactly
the supplied q_t at every branch. -/
theorem p_proc_01_history_markovization
    (q : ∀ n, Kernel (HistoryFiber X A n × A) X)
    (hq : ∀ n, IsMarkovKernel (q n)) :
    IsMarkovKernel (augmentedKernel q) ∧
      ∀ n (z : HistoryFiber X A n × A),
        (augmentedKernel q ⟨n, z⟩).map Carrier.current = q n z :=
  ⟨isMarkovKernel_augmentedKernel q hq,
    augmentedKernel_current_apply q hq⟩

end UEOT.V3.ConcreteHistoryMarkovization
