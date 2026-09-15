import UEOT.V3.RecoveryHittingFirstStep

/-!
# P-REC-03 — initial-law bridges

This layer connects the two equivalent Ionescu--Tulcea presentations already
used by the recovery formalization: `homTrajMeasure (dirac x) P` and the fixed
initial-prefix law `markovPathLaw P x`.  It also records the Tonelli mixture
identity for an arbitrary initial law.
-/

namespace UEOT.V3.RecoveryHittingInitial

open Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder ProbabilityTheory
open UEOT.V3.DynamicsKernel
open UEOT.V3.RecoveryHitting
open UEOT.V3.RecoveryHittingNonnegative
open UEOT.V3.RecoveryHittingFirstStep
open scoped ENNReal ProbabilityTheory

universe uX

variable {X : Type uX} [MeasurableSpace X]

/-- A deterministic initial state in the `trajMeasure` representation is the
same path law as the fixed-prefix `traj` representation. -/
theorem homTrajMeasure_dirac_eq_markovPathLaw
    (P : Kernel X X) [IsMarkovKernel P] (x : X) :
    homTrajMeasure (Measure.dirac x) P = markovPathLaw P x := by
  letI : ∀ n, IsMarkovKernel (homHistoryKernel P n) :=
    fun n => isMarkovKernel_homHistoryKernel P n
  unfold homTrajMeasure markovPathLaw
  rw [Kernel.trajMeasure,
    Measure.map_dirac' (MeasurableEquiv.piUnique (fun _ : Iic 0 => X)).symm.measurable,
    Measure.dirac_bind (Kernel.measurable _)]
  congr with i

/-- The canonical extended hitting-time potential is measurable in the initial
state. -/
theorem measurable_expectedHittingTime
    (P : Kernel X X) [IsMarkovKernel P]
    {A : Set X} (hA : MeasurableSet A) :
    Measurable (fun x => expectedHittingTime P x A) := by
  letI : ∀ n, IsMarkovKernel (homHistoryKernel P n) :=
    fun n => isMarkovKernel_homHistoryKernel P n
  have hf : Measurable (hittingValue A) := measurable_hittingValue hA
  have hpair :
      Measurable
        (Function.uncurry
          (fun (_ : (i : Iic 0) → X) (ω : ℕ → X) => hittingValue A ω)) := by
    exact hf.comp measurable_snd
  have hinner :
      Measurable
        (fun h : (i : Iic 0) → X =>
          ∫⁻ ω, hittingValue A ω
            ∂Kernel.traj (X := fun _ : ℕ => X) (homHistoryKernel P) 0 h) := by
    exact hpair.lintegral_kernel_prod_right
  simp_rw [expectedHittingTime, homTrajMeasure_dirac_eq_markovPathLaw]
  unfold markovPathLaw
  exact hinner.comp (by fun_prop)

/-- Tonelli decomposition over the initial law.  In particular, starting the
homogeneous Markov chain from a mixed law and then measuring its hitting time is
exactly the mixture of the canonical deterministic-start potentials. -/
theorem lintegral_hittingValue_homTrajMeasure_eq
    (P : Kernel X X) [IsMarkovKernel P]
    (μ : Measure X) {A : Set X} (hA : MeasurableSet A) :
    (∫⁻ ω, hittingValue A ω ∂homTrajMeasure μ P) =
      ∫⁻ y, expectedHittingTime P y A ∂μ := by
  letI : ∀ n, IsMarkovKernel (homHistoryKernel P n) :=
    fun n => isMarkovKernel_homHistoryKernel P n
  let e : ((i : Iic 0) → X) ≃ᵐ X :=
    MeasurableEquiv.piUnique (fun _ : Iic 0 => X)
  have hf : Measurable (hittingValue A) := measurable_hittingValue hA
  have hpair :
      Measurable
        (Function.uncurry
          (fun (_ : (i : Iic 0) → X) (ω : ℕ → X) => hittingValue A ω)) := by
    exact hf.comp measurable_snd
  have hinner :
      Measurable
        (fun h : (i : Iic 0) → X =>
          ∫⁻ ω, hittingValue A ω
            ∂Kernel.traj (X := fun _ : ℕ => X) (homHistoryKernel P) 0 h) := by
    exact hpair.lintegral_kernel_prod_right
  unfold homTrajMeasure
  rw [Kernel.trajMeasure]
  rw [Measure.lintegral_bind (Kernel.measurable _).aemeasurable hf.aemeasurable]
  change
    (∫⁻ h : (i : Iic 0) → X,
      (∫⁻ ω, hittingValue A ω
        ∂Kernel.traj (X := fun _ : ℕ => X) (homHistoryKernel P) 0 h)
      ∂μ.map e.symm) = _
  rw [lintegral_map hinner e.symm.measurable]
  apply lintegral_congr
  intro y
  rw [expectedHittingTime, homTrajMeasure_dirac_eq_markovPathLaw]
  unfold markovPathLaw
  congr 1

end UEOT.V3.RecoveryHittingInitial
