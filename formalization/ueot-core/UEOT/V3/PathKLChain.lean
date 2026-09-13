import UEOT.V3.DynamicsKernel
import UEOT.V3.InformationKernelKL
import UEOT.V3.InformationStatistic
import Mathlib.InformationTheory.KullbackLeibler.ChainRule

/-!
# P-KL-03 — finite-horizon path KL chain rule

The frozen Core 3 theorem allows genuinely history-dependent discrete kernels.
This file therefore works with a kernel family
`K n : Kernel (History X n) X`, not with a homogeneous one-step Markov kernel.
The finite path law is the `n`-prefix of Mathlib's Ionescu--Tulcea trajectory
measure.  At each step, the KL chain rule is applied before the history/next
state pair is reassembled into a longer history.
-/

namespace UEOT.V3.PathKLChain

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open Finset Function MeasurableEquiv
open scoped ENNReal ProbabilityTheory
open UEOT.V3.DynamicsKernel
open UEOT.V3.InformationKernelKL
open UEOT.V3.InformationStatistic

universe uX

variable {X : Type uX}
variable [MeasurableSpace X] [StandardBorelSpace X]
variable [Countable X] [MeasurableSingletonClass X] [Nonempty X]

abbrev History (X : Type uX) [MeasurableSpace X] (n : ℕ) :=
  (i : Finset.Iic n) → X

/-- Restrict an `(n+1)`-history to its first `n+1` coordinates indexed by
`Iic n`. -/
def prefixSucc (n : ℕ) (x : History X (n + 1)) : History X n :=
  fun i => x ⟨i.1, Finset.mem_Iic.mpr
    (Nat.le_trans (Finset.mem_Iic.mp i.2) (Nat.le_succ n))⟩

lemma measurable_prefixSucc (n : ℕ) :
    Measurable (prefixSucc (X := X) n) := by
  apply measurable_pi_iff.mpr
  intro i
  let j : Finset.Iic (n + 1) :=
    ⟨i.1, Finset.mem_Iic.mpr
      (Nat.le_trans (Finset.mem_Iic.mp i.2) (Nat.le_succ n))⟩
  exact measurable_pi_apply j

/-- Split a longer history into its old prefix and its newly appended state. -/
def splitHistory (n : ℕ) (x : History X (n + 1)) : History X n × X :=
  (prefixSucc n x, x (lastHistoryIndex (n + 1)))

lemma measurable_splitHistory (n : ℕ) :
    Measurable (splitHistory (X := X) n) := by
  exact (measurable_prefixSucc n).prodMk
    (measurable_pi_apply (lastHistoryIndex (n + 1)))

/-- `splitHistory` is a measurable left inverse of the existing UEOT history
append map.  Hence KL is unchanged when a `(history,next)` pair is repacked as
a longer finite path. -/
theorem splitHistory_appendHistory (n : ℕ) :
    Function.LeftInverse (splitHistory (X := X) n) (appendHistory (X := X) n) := by
  intro p
  apply Prod.ext
  · funext i
    have hi : (i : ℕ) ≤ n := Finset.mem_Iic.mp i.2
    simp [splitHistory, prefixSucc, appendHistory, IicProdIoc_def, hi]
  · simp [splitHistory, appendHistory, lastHistoryIndex, IicProdIoc_def,
      MeasurableEquiv.piSingleton]

/-- Finite path law through time `n`, obtained from the Ionescu--Tulcea law. -/
noncomputable def pathLaw
    (μ0 : Measure X)
    (K : ∀ n, Kernel (History X n) X)
    [∀ n, IsMarkovKernel (K n)]
    (n : ℕ) : Measure (History X n) :=
  (ProbabilityTheory.Kernel.trajMeasure
      (X := fun _ : ℕ => X) μ0 K).map (Preorder.frestrictLe n)

instance pathLaw_isProbability
    (μ0 : Measure X) [IsProbabilityMeasure μ0]
    (K : ∀ n, Kernel (History X n) X)
    [∀ n, IsMarkovKernel (K n)]
    (n : ℕ) : IsProbabilityMeasure (pathLaw μ0 K n) := by
  unfold pathLaw
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- The time-zero prefix depends only on the common initial law. -/
theorem pathLaw_zero
    (μ0 : Measure X) [IsProbabilityMeasure μ0]
    (K : ∀ n, Kernel (History X n) X)
    [∀ n, IsMarkovKernel (K n)] :
    pathLaw μ0 K 0 =
      μ0.map
        (MeasurableEquiv.piUnique
          (fun _ : Finset.Iic 0 => X)).symm := by
  rw [pathLaw, ProbabilityTheory.Kernel.trajMeasure,
    Measure.map_comp _ _ (by fun_prop),
    ProbabilityTheory.Kernel.traj_map_frestrictLe,
    ProbabilityTheory.Kernel.partialTraj_self,
    Measure.id_comp]

/-- One Ionescu--Tulcea step: extend the current history law by the next
history-dependent kernel and repack the pair into the next finite history. -/
theorem pathLaw_succ
    (μ0 : Measure X) [IsProbabilityMeasure μ0]
    (K : ∀ n, Kernel (History X n) X)
    [∀ n, IsMarkovKernel (K n)]
    (n : ℕ) :
    ((pathLaw μ0 K n) ⊗ₘ K n).map (appendHistory (X := X) n) =
      pathLaw μ0 K (n + 1) := by
  have hstep :=
    ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (X := fun _ : ℕ => X) (μ₀ := μ0) (κ := K) (a := n)
  have hstep' :
      (pathLaw μ0 K n) ⊗ₘ K n =
        (ProbabilityTheory.Kernel.trajMeasure
          (X := fun _ : ℕ => X) μ0 K).map
          (fun x => (Preorder.frestrictLe n x, x (n + 1))) := by
    simpa [pathLaw] using hstep
  rw [hstep']
  rw [Measure.map_map (measurable_appendHistory n) (by fun_prop)]
  have hcomp :
      appendHistory (X := X) n ∘
          (fun x : ℕ → X => (Preorder.frestrictLe n x, x (n + 1))) =
        Preorder.frestrictLe (n + 1) := by
    funext x
    exact appendHistory_prefix_next n x
  rw [hcomp]
  rfl

/-- **P-KL-03.**  For the same initial law and history-dependent discrete
kernels with rowwise absolute continuity, finite-path KL is the sum of the
expected one-step conditional KL divergences under the `P` path law. -/
theorem p_kl_03
    (μ0 : Measure X) [IsProbabilityMeasure μ0]
    (P Q : ∀ n, Kernel (History X n) X)
    [∀ n, IsMarkovKernel (P n)] [∀ n, IsMarkovKernel (Q n)]
    (hPQ : ∀ n h, P n h ≪ Q n h) :
    ∀ T : ℕ,
      klDiv (pathLaw μ0 P T) (pathLaw μ0 Q T) =
        ∑ t ∈ Finset.range T,
          ∫⁻ h, klDiv (P t h) (Q t h) ∂pathLaw μ0 P t := by
  intro T
  induction T with
  | zero =>
      rw [pathLaw_zero μ0 P, pathLaw_zero μ0 Q]
      simp
  | succ n ih =>
      have hPstep := pathLaw_succ μ0 P n
      have hQstep := pathLaw_succ μ0 Q n
      have hpack :
          klDiv (pathLaw μ0 P (n + 1)) (pathLaw μ0 Q (n + 1)) =
            klDiv ((pathLaw μ0 P n) ⊗ₘ P n)
              ((pathLaw μ0 Q n) ⊗ₘ Q n) := by
        rw [← hPstep, ← hQstep]
        exact klDiv_map_eq_of_measurable_leftInverse
          ((pathLaw μ0 P n) ⊗ₘ P n)
          ((pathLaw μ0 Q n) ⊗ₘ Q n)
          (appendHistory (X := X) n)
          (splitHistory (X := X) n)
          (measurable_appendHistory n)
          (measurable_splitHistory n)
          (splitHistory_appendHistory (X := X) n)
      have hchain := InformationTheory.klDiv_compProd_eq_add
        (pathLaw μ0 P n) (pathLaw μ0 Q n) (P n) (Q n)
      have hrow : ∀ᵐ h ∂pathLaw μ0 P n, P n h ≪ Q n h :=
        Filter.Eventually.of_forall (hPQ n)
      have hfiber :=
        klDiv_compProd_right_eq_lintegral
          (μ := pathLaw μ0 P n) (κ := P n) (η := Q n) hrow
      rw [hpack, hchain, hfiber, ih]
      rw [Finset.sum_range_succ]

/-- Frozen P-KL-03 extension for distinct initial laws: the initial KL is added
before the same history-dependent conditional-KL ledger. -/
theorem p_kl_03_general
    (μ0 ν0 : Measure X) [IsProbabilityMeasure μ0] [IsProbabilityMeasure ν0]
    (P Q : ∀ n, Kernel (History X n) X)
    [∀ n, IsMarkovKernel (P n)] [∀ n, IsMarkovKernel (Q n)]
    (hPQ : ∀ n h, P n h ≪ Q n h) :
    ∀ T : ℕ,
      klDiv (pathLaw μ0 P T) (pathLaw ν0 Q T) =
        klDiv μ0 ν0 +
          ∑ t ∈ Finset.range T,
            ∫⁻ h, klDiv (P t h) (Q t h) ∂pathLaw μ0 P t := by
  intro T
  induction T with
  | zero =>
      rw [pathLaw_zero μ0 P, pathLaw_zero ν0 Q]
      simp only [Finset.range_zero, Finset.sum_empty, add_zero]
      exact klDiv_map_eq_of_measurable_leftInverse
        μ0 ν0
        (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => X)).symm
        (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => X))
        (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => X)).symm.measurable
        (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => X)).measurable
        (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => X)).symm.left_inv
  | succ n ih =>
      have hPstep := pathLaw_succ μ0 P n
      have hQstep := pathLaw_succ ν0 Q n
      have hpack :
          klDiv (pathLaw μ0 P (n + 1)) (pathLaw ν0 Q (n + 1)) =
            klDiv ((pathLaw μ0 P n) ⊗ₘ P n)
              ((pathLaw ν0 Q n) ⊗ₘ Q n) := by
        rw [← hPstep, ← hQstep]
        exact klDiv_map_eq_of_measurable_leftInverse
          ((pathLaw μ0 P n) ⊗ₘ P n)
          ((pathLaw ν0 Q n) ⊗ₘ Q n)
          (appendHistory (X := X) n)
          (splitHistory (X := X) n)
          (measurable_appendHistory n)
          (measurable_splitHistory n)
          (splitHistory_appendHistory (X := X) n)
      have hchain := InformationTheory.klDiv_compProd_eq_add
        (pathLaw μ0 P n) (pathLaw ν0 Q n) (P n) (Q n)
      have hrow : ∀ᵐ h ∂pathLaw μ0 P n, P n h ≪ Q n h :=
        Filter.Eventually.of_forall (hPQ n)
      have hfiber :=
        klDiv_compProd_right_eq_lintegral
          (μ := pathLaw μ0 P n) (κ := P n) (η := Q n) hrow
      rw [hpack, hchain, hfiber, ih, Finset.sum_range_succ]
      exact add_assoc _ _ _

end

end UEOT.V3.PathKLChain
