import UEOT.V3.RecoveryHittingInitial

/-!
# P-REC-03 — homogeneous Markov restart

For the homogeneous Ionescu--Tulcea path law, deleting the initial coordinate
produces the same path law as first drawing the one-step state and then
restarting the same homogeneous kernel from that state.  This is the exact
Markov restart bridge needed by the first-step hitting-time identity.
-/

namespace UEOT.V3.RecoveryHittingRestart

open Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder ProbabilityTheory
open UEOT.V3.DynamicsKernel
open UEOT.V3.RecoveryHitting
open UEOT.V3.RecoveryHittingNonnegative
open UEOT.V3.RecoveryHittingFirstStep
open UEOT.V3.RecoveryHittingInitial
open scoped ENNReal ProbabilityTheory

universe uX

variable {X : Type uX} [MeasurableSpace X]

/-- Delete the first coordinate from a finite prefix of length `n+2`. -/
def dropFirstHistory (n : ℕ)
    (h : (i : Iic (n + 1)) → X) : (i : Iic n) → X :=
  fun i => h ⟨i.1 + 1, mem_Iic.mpr (Nat.succ_le_succ (mem_Iic.mp i.2))⟩

theorem measurable_dropFirstHistory (n : ℕ) :
    Measurable (dropFirstHistory (X := X) n) := by
  apply measurable_pi_iff.mpr
  intro i
  let j : Iic (n + 1) :=
    ⟨i.1 + 1, mem_Iic.mpr (Nat.succ_le_succ (mem_Iic.mp i.2))⟩
  exact measurable_pi_apply j

/-- Restricting a shifted path is the same as restricting one step farther and
then deleting the first coordinate. -/
theorem dropFirstHistory_frestrictLe
    (n : ℕ) (ω : ℕ → X) :
    dropFirstHistory n (frestrictLe (n + 1) ω) =
      frestrictLe n (pathShift ω) := by
  ext i
  simp [dropFirstHistory, pathShift, frestrictLe_apply]

/-- Deleting the first coordinate commutes with appending a new terminal
state. -/
theorem dropFirstHistory_appendHistory
    (n : ℕ) (h : (i : Iic (n + 1)) → X) (y : X) :
    dropFirstHistory (n + 1) (appendHistory (n + 1) (h, y)) =
      appendHistory n (dropFirstHistory n h, y) := by
  ext i
  by_cases hi : (i : ℕ) ≤ n
  · simp [dropFirstHistory, appendHistory, IicProdIoc_def, hi]
  · have hin : (i : ℕ) = n + 1 := by
      have hle : (i : ℕ) ≤ n + 1 := mem_Iic.mp i.2
      omega
    have hieq :
        i = (⟨n + 1, mem_Iic.mpr le_rfl⟩ : Iic (n + 1)) :=
      Subtype.ext hin
    rw [hieq]
    simp [dropFirstHistory, appendHistory, IicProdIoc_def,
      MeasurableEquiv.piSingleton]

/-- The homogeneous history kernel is insensitive to the discarded initial
coordinate because it reads only the current (last) state. -/
theorem homHistoryKernel_dropFirst
    (P : Kernel X X) (n : ℕ) :
    Kernel.comap (homHistoryKernel P n)
        (dropFirstHistory n) (measurable_dropFirstHistory n) =
      homHistoryKernel P (n + 1) := by
  ext h B hB
  rw [Kernel.comap_apply']
  unfold homHistoryKernel
  rw [Kernel.comap_apply', Kernel.comap_apply']
  rfl

/-- Mapping a one-step history extension after deleting its first coordinate is
the same as first deleting that coordinate and then extending with the same
homogeneous transition kernel. -/
theorem homHistory_compProd_dropFirst
    (μh : Measure ((i : Iic (n + 1)) → X)) [SFinite μh]
    (P : Kernel X X) [IsMarkovKernel P] :
    (μh ⊗ₘ homHistoryKernel P (n + 1)).map
        (Prod.map (dropFirstHistory n) id) =
      (μh.map (dropFirstHistory n)) ⊗ₘ homHistoryKernel P n := by
  letI : IsMarkovKernel (homHistoryKernel P (n + 1)) :=
    isMarkovKernel_homHistoryKernel P (n + 1)
  letI : IsMarkovKernel (homHistoryKernel P n) :=
    isMarkovKernel_homHistoryKernel P n
  have hid : Measurable (id : X → X) := measurable_id
  have hprod :
      Measurable
        (Prod.map (dropFirstHistory (X := X) n) (id : X → X)) :=
    (measurable_dropFirstHistory (X := X) n).prodMap hid
  ext s hs
  rw [Measure.map_apply hprod hs,
    Measure.compProd_apply (hprod hs),
    Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs)
      (measurable_dropFirstHistory n)]
  congr with h

/-- For an arbitrary initial law, the marginal at time one is the one-step
pushforward `P ∘ₘ μ`. -/
theorem homTrajMeasure_time_one
    (μ : Measure X) [IsProbabilityMeasure μ]
    (P : Kernel X X) [IsMarkovKernel P] :
    (homTrajMeasure μ P).map (fun z : ℕ → X => z 1) =
      P ∘ₘ μ := by
  let μpath := homTrajMeasure μ P
  have hstep := homTrajMeasure_prefix_succ μ P 0
  have hzero := homTrajMeasure_prefix_zero μ P
  letI : IsMarkovKernel (homHistoryKernel P 0) :=
    isMarkovKernel_homHistoryKernel P 0
  let e : ((i : Iic 0) → X) ≃ᵐ X :=
    MeasurableEquiv.piUnique (fun _ : Iic 0 => X)
  have hlast_append :
      (fun h : (i : Iic 1) → X => h (lastHistoryIndex 1)) ∘
          appendHistory 0 =
        Prod.snd := by
    funext p
    simp [appendHistory, lastHistoryIndex, IicProdIoc_def,
      MeasurableEquiv.piSingleton]
  calc
    μpath.map (fun z : ℕ → X => z 1) =
        (μpath.map (frestrictLe 1)).map
          (fun h : (i : Iic 1) → X => h (lastHistoryIndex 1)) := by
      symm
      rw [Measure.map_map
        (μ := μpath)
        (measurable_pi_apply (lastHistoryIndex 1))
        (measurable_frestrictLe 1)]
      rfl
    _ =
        ((((μpath.map (frestrictLe 0)) ⊗ₘ homHistoryKernel P 0).map
          (appendHistory 0))).map
          (fun h : (i : Iic 1) → X => h (lastHistoryIndex 1)) := by
      rw [hstep]
    _ =
        ((μpath.map (frestrictLe 0)) ⊗ₘ homHistoryKernel P 0).map
          Prod.snd := by
      rw [Measure.map_map
        (measurable_pi_apply (lastHistoryIndex 1))
        (measurable_appendHistory 0)]
      rw [hlast_append]
    _ =
        homHistoryKernel P 0 ∘ₘ (μpath.map (frestrictLe 0)) := by
      simpa [Measure.snd] using
        (Measure.snd_compProd (μpath.map (frestrictLe 0))
          (homHistoryKernel P 0))
    _ =
        homHistoryKernel P 0 ∘ₘ μ.map e.symm := by
      rw [hzero]
    _ = P ∘ₘ μ := by
      ext s hs
      rw [Measure.bind_apply hs (Kernel.aemeasurable _),
        Measure.bind_apply hs (Kernel.aemeasurable _),
        lintegral_map (Kernel.measurable_coe _ hs) e.symm.measurable]
      congr with y

/-- Prefix form of the homogeneous restart law. -/
theorem homTrajMeasure_shift_prefix
    (μ : Measure X) [IsProbabilityMeasure μ]
    (P : Kernel X X) [IsMarkovKernel P]
    (n : ℕ) :
    (((homTrajMeasure μ P).map pathShift).map (frestrictLe n)) =
      (homTrajMeasure (P ∘ₘ μ) P).map (frestrictLe n) := by
  letI : IsProbabilityMeasure (P ∘ₘ μ) := by infer_instance
  induction n with
  | zero =>
      let e : ((i : Iic 0) → X) ≃ᵐ X :=
        MeasurableEquiv.piUnique (fun _ : Iic 0 => X)
      have hcomp :
          frestrictLe 0 ∘ pathShift =
            e.symm ∘ (fun z : ℕ → X => z 1) := by
        funext z
        ext i
        have hi : i = default := Subsingleton.elim _ _
        subst i
        rfl
      rw [Measure.map_map (measurable_frestrictLe 0) measurable_pathShift,
        hcomp, ← Measure.map_map e.symm.measurable (measurable_pi_apply 1),
        homTrajMeasure_time_one μ P]
      exact (homTrajMeasure_prefix_zero (P ∘ₘ μ) P).symm
  | succ n ih =>
      let μpath := homTrajMeasure μ P
      let ρpath := homTrajMeasure (P ∘ₘ μ) P
      have hshift_n :
          ((μpath.map pathShift).map (frestrictLe n)) =
            (μpath.map (frestrictLe (n + 1))).map
              (dropFirstHistory n) := by
        rw [Measure.map_map (measurable_frestrictLe n) measurable_pathShift,
          Measure.map_map (measurable_dropFirstHistory n)
            (measurable_frestrictLe (n + 1))]
        congr 1
      have hshift_succ :
          ((μpath.map pathShift).map (frestrictLe (n + 1))) =
            (μpath.map (frestrictLe (n + 2))).map
              (dropFirstHistory (n + 1)) := by
        rw [Measure.map_map (measurable_frestrictLe (n + 1)) measurable_pathShift,
          Measure.map_map (measurable_dropFirstHistory (n + 1))
            (measurable_frestrictLe (n + 2))]
        congr 1
      rw [hshift_succ]
      rw [← homTrajMeasure_prefix_succ μ P (n + 1)]
      rw [Measure.map_map
        (measurable_dropFirstHistory (n + 1))
        (measurable_appendHistory (n + 1))]
      have hid : Measurable (id : X → X) := measurable_id
      have hprod :
          Measurable
            (Prod.map (dropFirstHistory (X := X) n) (id : X → X)) :=
        (measurable_dropFirstHistory (X := X) n).prodMap hid
      have hcomp :
          dropFirstHistory (n + 1) ∘ appendHistory (n + 1) =
            appendHistory n ∘
              Prod.map (dropFirstHistory (X := X) n) (id : X → X) := by
        funext p
        exact dropFirstHistory_appendHistory n p.1 p.2
      rw [hcomp]
      rw [← Measure.map_map (measurable_appendHistory n) hprod]
      rw [homHistory_compProd_dropFirst
        (μh := μpath.map (frestrictLe (n + 1))) P]
      rw [← hshift_n]
      change
        (((μpath.map pathShift).map (frestrictLe n)) ⊗ₘ
            homHistoryKernel P n).map (appendHistory n) =
          ρpath.map (frestrictLe (n + 1))
      rw [ih]
      exact homTrajMeasure_prefix_succ (P ∘ₘ μ) P n

/-- **Homogeneous one-step restart law.**  Deleting the initial coordinate of
a Markov path started from `μ` is exactly the same as restarting the same
homogeneous kernel from the one-step law `P ∘ₘ μ`. -/
theorem homTrajMeasure_shift
    (μ : Measure X) [IsProbabilityMeasure μ]
    (P : Kernel X X) [IsMarkovKernel P] :
    (homTrajMeasure μ P).map pathShift =
      homTrajMeasure (P ∘ₘ μ) P := by
  letI : IsProbabilityMeasure (P ∘ₘ μ) := by infer_instance
  letI : IsProbabilityMeasure ((homTrajMeasure μ P).map pathShift) :=
    Measure.isProbabilityMeasure_map measurable_pathShift.aemeasurable
  apply pathMeasure_eq_of_prefix_eq
  intro n
  exact homTrajMeasure_shift_prefix μ P n

end UEOT.V3.RecoveryHittingRestart