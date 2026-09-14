import UEOT.V3.DynamicsKernel
import Mathlib.Probability.Martingale.OptionalStopping

/-!
# P-REC-04 — Markov drift and hitting-time recovery

This module starts the source-facing P-REC-04 lane.  The first layer establishes
that the homogeneous Markov path used by UEOT has the literal one-step
conditional expectation dictated by the state kernel.  No stopped-process or
hitting-time estimate is assumed here.
-/

namespace UEOT.V3.RecoveryHitting

open Filter Finset Function MeasurableSpace MeasureTheory Preorder ProbabilityTheory
open UEOT.V3.DynamicsKernel
open scoped ENNReal ProbabilityTheory

universe uX

variable {X : Type uX} [MeasurableSpace X]

/-- Canonical homogeneous Markov path started at the deterministic state `x`.
It is the fixed-prefix form of Mathlib's Ionescu--Tulcea trajectory kernel. -/
noncomputable def markovPathLaw
    (P : Kernel X X) [IsMarkovKernel P] (x : X) : Measure (ℕ → X) := by
  letI : ∀ n, IsMarkovKernel (homHistoryKernel P n) :=
    fun n => isMarkovKernel_homHistoryKernel P n
  exact Kernel.traj (homHistoryKernel P) 0 (fun _ => x)

instance isProbabilityMeasure_markovPathLaw
    (P : Kernel X X) [IsMarkovKernel P] (x : X) :
    IsProbabilityMeasure (markovPathLaw P x) := by
  unfold markovPathLaw
  infer_instance

/-- Integrating a potential of the next coordinate against the continuation
trajectory is exactly integration against the source transition kernel at the
current coordinate.  This is the state-kernel-to-path bridge needed by
P-REC-04. -/
theorem integral_traj_next_eq_kernel
    (P : Kernel X X) [IsMarkovKernel P]
    (V : X → ℝ) (hV : StronglyMeasurable V)
    (n : ℕ) (ω : ℕ → X) :
    (∫ ξ, V (ξ (n + 1))
      ∂Kernel.traj (homHistoryKernel P) n (frestrictLe n ω)) =
      ∫ y, V y ∂P (ω n) := by
  letI : ∀ k, IsMarkovKernel (homHistoryKernel P k) :=
    fun k => isMarkovKernel_homHistoryKernel P k
  have hmap :
      (Kernel.traj (homHistoryKernel P) n (frestrictLe n ω)).map
          (fun ξ => ξ (n + 1)) =
        homHistoryKernel P n (frestrictLe n ω) := by
    have hk := Kernel.map_traj_succ_self (κ := homHistoryKernel P) (a := n)
    have hk' := congrArg
      (fun K : Kernel ((i : Iic n) → X) X => K (frestrictLe n ω)) hk
    simpa [Kernel.map_apply _ (measurable_pi_apply (n + 1))] using hk'
  calc
    (∫ ξ, V (ξ (n + 1))
      ∂Kernel.traj (homHistoryKernel P) n (frestrictLe n ω)) =
        ∫ y, V y ∂(Kernel.traj (homHistoryKernel P) n
          (frestrictLe n ω)).map (fun ξ => ξ (n + 1)) := by
            symm
            exact integral_map_of_stronglyMeasurable
              (measurable_pi_apply (n + 1)) hV
    _ = ∫ y, V y ∂homHistoryKernel P n (frestrictLe n ω) := by
      rw [hmap]
    _ = ∫ y, V y ∂P (ω n) := by
      simp [homHistoryKernel, lastHistoryIndex, Kernel.comap_apply,
        frestrictLe_apply]

/-- Literal one-step Markov conditional-expectation identity on the canonical
path law.  This theorem derives the path conditional drift from `P`; it does
not postulate it as an extra process hypothesis. -/
theorem condExp_next_potential
    (P : Kernel X X) [IsMarkovKernel P]
    (x : X) (V : X → ℝ)
    (hV : StronglyMeasurable V)
    (hVint : ∀ n, Integrable (fun ω : ℕ → X => V (ω n)) (markovPathLaw P x))
    (n : ℕ) :
    (markovPathLaw P x)[fun ω : ℕ → X => V (ω (n + 1)) | Filtration.piLE n]
      =ᵐ[markovPathLaw P x]
        fun ω => ∫ y, V y ∂P (ω n) := by
  letI : ∀ k, IsMarkovKernel (homHistoryKernel P k) :=
    fun k => isMarkovKernel_homHistoryKernel P k
  unfold markovPathLaw at hVint ⊢
  have hcond := Kernel.condExp_traj
    (κ := homHistoryKernel P) (a := 0) (b := n) (Nat.zero_le n)
    (x₀ := fun _ => x)
    (f := fun ω : ℕ → X => V (ω (n + 1)))
    (hVint (n + 1))
  filter_upwards [hcond] with ω hω
  rw [hω]
  exact integral_traj_next_eq_kernel P V hV n ω

end UEOT.V3.RecoveryHitting
