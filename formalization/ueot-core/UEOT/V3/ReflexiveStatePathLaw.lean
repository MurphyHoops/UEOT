import UEOT.V3.ReflexiveStateAugmentation
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# P-REF-01 path-law layer — Ionescu--Tulcea extension

This layer feeds the causal complete-history Markov kernel into Mathlib's
Ionescu--Tulcea construction.  The canonical infinite history law is therefore
built from the source initial law, causal policy and controlled reflexive kernel,
while the physical reflexive-state path law is its measurable readout.
-/

namespace UEOT.V3.ReflexiveStatePathLaw

open Function Finset MeasurableEquiv MeasurableSpace MeasureTheory Preorder ProbabilityTheory
open UEOT.V3.FiniteHistory
open UEOT.V3.FiniteHistoryMeasurable
open UEOT.V3.ReflexiveStateAugmentation
open scoped ProbabilityTheory

universe uZ uA

variable {Z : Type uZ} {A : Type uA}
variable [MeasurableSpace Z] [MeasurableSpace A]

/-- Embed the source initial law on `Z` as a time-zero complete history. -/
noncomputable def initialHistoryLaw (mu0 : Measure Z) :
    Measure (Carrier Z A) :=
  mu0.map (Carrier.singleton (A := A))

instance isProbabilityMeasure_initialHistoryLaw
    (mu0 : Measure Z) [IsProbabilityMeasure mu0] :
    IsProbabilityMeasure (initialHistoryLaw (A := A) mu0) := by
  unfold initialHistoryLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_singleton (X := Z) (A := A)).aemeasurable

/-- Present one homogeneous history kernel in the history-dependent kernel shape
required by Ionescu--Tulcea: a finite trajectory prefix is sent to its final
history coordinate. -/
noncomputable def trajectoryStep
    (Q : Kernel (Carrier Z A) (Carrier Z A))
    (n : ℕ) :
    Kernel (Π _ : Iic n, Carrier Z A) (Carrier Z A) := by
  let last : Iic n := ⟨n, mem_Iic.2 le_rfl⟩
  exact Q.comap (fun h => h last) (measurable_pi_apply last)

instance isMarkovKernel_trajectoryStep
    (Q : Kernel (Carrier Z A) (Carrier Z A))
    [IsMarkovKernel Q] (n : ℕ) :
    IsMarkovKernel (trajectoryStep Q n) := by
  unfold trajectoryStep
  infer_instance

/-- The constant-state Ionescu--Tulcea family induced by the global
complete-history transition.  Naming this family makes the dependent `X n`
parameter explicit to Lean while leaving the mathematical state space constant. -/
noncomputable def historyTrajectoryStep
    (K : Kernel (Z × A) Z)
    (pi : CausalPolicy Z A) :
    (n : ℕ) → Kernel (Π _ : Iic n, Carrier Z A) (Carrier Z A) :=
  fun n => trajectoryStep (historyKernel K pi) n

instance isMarkovKernel_historyTrajectoryStep
    (K : Kernel (Z × A) Z)
    (pi : CausalPolicy Z A)
    [IsMarkovKernel K]
    [∀ n, IsMarkovKernel (pi n)]
    (n : ℕ) :
    IsMarkovKernel (historyTrajectoryStep K pi n) := by
  unfold historyTrajectoryStep
  infer_instance

/-- Canonical infinite complete-history law under initial law `mu0`, source
controlled kernel `K`, and arbitrary causal randomized policy `pi`. -/
noncomputable def historyPathLaw
    (mu0 : Measure Z)
    (K : Kernel (Z × A) Z)
    (pi : CausalPolicy Z A)
    [IsMarkovKernel K]
    [∀ n, IsMarkovKernel (pi n)] :
    Measure (ℕ → Carrier Z A) :=
  Kernel.trajMeasure
    (initialHistoryLaw (A := A) mu0)
    (historyTrajectoryStep K pi)

instance isProbabilityMeasure_historyPathLaw
    (mu0 : Measure Z)
    (K : Kernel (Z × A) Z)
    (pi : CausalPolicy Z A)
    [IsProbabilityMeasure mu0]
    [IsMarkovKernel K]
    [∀ n, IsMarkovKernel (pi n)] :
    IsProbabilityMeasure (historyPathLaw mu0 K pi) := by
  unfold historyPathLaw
  infer_instance

/-- The time-zero singleton-product version of the embedded initial history law.
This is exactly the initial measure consumed by Mathlib's `trajMeasure`. -/
noncomputable def initialHistoryPrefixLaw (mu0 : Measure Z) :
    Measure (Π _ : Iic 0, Carrier Z A) :=
  (initialHistoryLaw (A := A) mu0).map
    (MeasurableEquiv.piUnique (fun _ : Iic 0 => Carrier Z A)).symm

/-- The recursively composed finite trajectory kernel from time zero through `n`.
The explicit constant family argument fixes the dependent `X : ℕ → Type*`
expected by Mathlib before the result is coerced for measure--kernel composition. -/
noncomputable def finiteHistoryKernel
    (K : Kernel (Z × A) Z)
    (pi : CausalPolicy Z A)
    (n : ℕ) :
    Kernel (Π _ : Iic 0, Carrier Z A) (Π _ : Iic n, Carrier Z A) :=
  Kernel.partialTraj
    (X := fun _ : ℕ => Carrier Z A)
    (historyTrajectoryStep K pi) 0 n

instance isMarkovKernel_finiteHistoryKernel
    (K : Kernel (Z × A) Z)
    (pi : CausalPolicy Z A)
    [IsMarkovKernel K]
    [∀ n, IsMarkovKernel (pi n)]
    (n : ℕ) :
    IsMarkovKernel (finiteHistoryKernel K pi n) := by
  unfold finiteHistoryKernel
  infer_instance

/-- Independently specified finite-prefix law obtained by composing only the
first `n` Ionescu--Tulcea kernels with the embedded initial law. -/
noncomputable def finiteHistoryLaw
    (mu0 : Measure Z)
    (K : Kernel (Z × A) Z)
    (pi : CausalPolicy Z A)
    (n : ℕ) :
    Measure (Π _ : Iic n, Carrier Z A) :=
  finiteHistoryKernel K pi n ∘ₘ initialHistoryPrefixLaw (A := A) mu0

/-- Every canonical finite prefix is exactly the recursively composed finite law.
This is the finite-dimensional consistency interface used by the uniqueness
layer; it is not a definition-by-equality of candidate infinite measures. -/
theorem historyPathLaw_prefix
    (mu0 : Measure Z)
    (K : Kernel (Z × A) Z)
    (pi : CausalPolicy Z A)
    [IsMarkovKernel K]
    [∀ n, IsMarkovKernel (pi n)]
    (n : ℕ) :
    (historyPathLaw mu0 K pi).map (frestrictLe n) =
      finiteHistoryLaw mu0 K pi n := by
  unfold historyPathLaw finiteHistoryLaw finiteHistoryKernel
    initialHistoryPrefixLaw Kernel.trajMeasure
  rw [Measure.map_comp _ _ (measurable_frestrictLe n)]
  rw [Kernel.traj_map_frestrictLe]

/-- Coordinatewise physical/reflexive state readout from complete histories. -/
def statePathReadout :
    (ℕ → Carrier Z A) → (ℕ → Z) :=
  fun omega n => Carrier.current (omega n)

theorem measurable_statePathReadout :
    Measurable (statePathReadout (Z := Z) (A := A)) := by
  rw [measurable_pi_iff]
  intro n
  exact measurable_current.comp (measurable_pi_apply n)

/-- Canonical source `Z`-path law.  It is a measurable pushforward of the
complete-history Ionescu--Tulcea law, so the full causal policy remains encoded
without being mistaken for a Markov-only policy on `Z`. -/
noncomputable def reflexivePathLaw
    (mu0 : Measure Z)
    (K : Kernel (Z × A) Z)
    (pi : CausalPolicy Z A)
    [IsMarkovKernel K]
    [∀ n, IsMarkovKernel (pi n)] :
    Measure (ℕ → Z) :=
  (historyPathLaw mu0 K pi).map statePathReadout

instance isProbabilityMeasure_reflexivePathLaw
    (mu0 : Measure Z)
    (K : Kernel (Z × A) Z)
    (pi : CausalPolicy Z A)
    [IsProbabilityMeasure mu0]
    [IsMarkovKernel K]
    [∀ n, IsMarkovKernel (pi n)] :
    IsProbabilityMeasure (reflexivePathLaw mu0 K pi) := by
  unfold reflexivePathLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_statePathReadout (Z := Z) (A := A)).aemeasurable

end UEOT.V3.ReflexiveStatePathLaw
