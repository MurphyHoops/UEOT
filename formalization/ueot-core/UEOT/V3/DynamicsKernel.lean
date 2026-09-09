import Mathlib.Probability.Kernel.Composition.CompMap
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# P-DYN-01 — general Markov-kernel lumpability

This module formalizes the exact kernel intertwining condition from clause (2)
of P-DYN-01 and propagates it to every finite-step transition kernel.

It does **not** yet identify this with the full conditional-history/path-law
Markov statement in clause (1).  That final bridge remains an explicit
source-level obligation.
-/

namespace UEOT.V3.DynamicsKernel

open MeasureTheory ProbabilityTheory
open Finset Function MeasurableEquiv
open scoped ProbabilityTheory

universe uX uM
variable {X : Type uX} {M : Type uM}
variable [MeasurableSpace X] [MeasurableSpace M]

def StrongLumpability
    (P : Kernel X X) (Pbar : Kernel M M)
    (f : X → M) (hf : Measurable f) : Prop :=
  Kernel.map P f = Kernel.comap Pbar f hf

theorem strongLumpability_iff_apply
    (P : Kernel X X) (Pbar : Kernel M M)
    (f : X → M) (hf : Measurable f) :
    StrongLumpability P Pbar f hf ↔
      ∀ x, (P x).map f = Pbar (f x) := by
  constructor
  · intro h x
    have hx := congrArg (fun κ : Kernel X M => κ x) h
    unfold StrongLumpability at h
    rw [Kernel.map_apply _ hf, Kernel.comap_apply] at hx
    exact hx
  · intro h
    unfold StrongLumpability
    ext x B hB
    rw [Kernel.map_apply' _ hf _ hB, Kernel.comap_apply']
    have hx := congrArg (fun μ : Measure M => μ B) (h x)
    simpa [Measure.map_apply hf hB] using hx

theorem strongLumpability_iff_preimage
    (P : Kernel X X) (Pbar : Kernel M M)
    (f : X → M) (hf : Measurable f) :
    StrongLumpability P Pbar f hf ↔
      ∀ x B, MeasurableSet B →
        P x (f ⁻¹' B) = Pbar (f x) B := by
  rw [strongLumpability_iff_apply]
  constructor
  · intro h x B hB
    have hx := congrArg (fun μ : Measure M => μ B) (h x)
    simpa [Measure.map_apply hf hB] using hx
  · intro h x
    ext B hB
    rw [Measure.map_apply hf hB]
    exact h x B hB

theorem strongLumpability_fiber_constant
    (P : Kernel X X) (Pbar : Kernel M M)
    (f : X → M) (hf : Measurable f)
    (h : StrongLumpability P Pbar f hf)
    {x y : X} (hxy : f x = f y) :
    (P x).map f = (P y).map f := by
  rw [(strongLumpability_iff_apply P Pbar f hf).1 h x,
      (strongLumpability_iff_apply P Pbar f hf).1 h y, hxy]

noncomputable def iterateKernel (P : Kernel X X) : ℕ → Kernel X X
  | 0 => Kernel.id
  | n + 1 => P ∘ₖ iterateKernel P n

@[simp]
theorem iterateKernel_zero (P : Kernel X X) :
    iterateKernel P 0 = Kernel.id := rfl

@[simp]
theorem iterateKernel_succ (P : Kernel X X) (n : ℕ) :
    iterateKernel P (n + 1) = P ∘ₖ iterateKernel P n := rfl

theorem iterateKernel_strongLumpability
    (P : Kernel X X) (Pbar : Kernel M M)
    (f : X → M) (hf : Measurable f)
    (h : StrongLumpability P Pbar f hf) :
    ∀ n, StrongLumpability (iterateKernel P n) (iterateKernel Pbar n) f hf := by
  intro n
  induction n with
  | zero =>
      unfold StrongLumpability
      simp [iterateKernel, Kernel.id_map, Kernel.id_comap, hf]
  | succ n ih =>
      unfold StrongLumpability at ih ⊢
      simp only [iterateKernel_succ]
      calc
        Kernel.map (P ∘ₖ iterateKernel P n) f
            = Kernel.map P f ∘ₖ iterateKernel P n :=
          Kernel.map_comp (iterateKernel P n) P f
        _ = Kernel.comap Pbar f hf ∘ₖ iterateKernel P n := by
          rw [h]
        _ = Pbar ∘ₖ Kernel.map (iterateKernel P n) f := by
          symm
          exact Kernel.comp_map (iterateKernel P n) Pbar hf
        _ = Pbar ∘ₖ Kernel.comap (iterateKernel Pbar n) f hf := by
          rw [ih]
        _ = (Pbar ∘ₖ iterateKernel Pbar n) ∘ₖ Kernel.deterministic f hf := by
          rw [← Kernel.comp_deterministic_eq_comap (iterateKernel Pbar n) hf,
              ← Kernel.comp_assoc]
        _ = Kernel.comap (Pbar ∘ₖ iterateKernel Pbar n) f hf :=
          Kernel.comp_deterministic_eq_comap _ hf

theorem iterateKernel_pushforward
    (P : Kernel X X) (Pbar : Kernel M M)
    (f : X → M) (hf : Measurable f)
    (h : StrongLumpability P Pbar f hf)
    (n : ℕ) (x : X) :
    (iterateKernel P n x).map f = iterateKernel Pbar n (f x) := by
  exact
    (strongLumpability_iff_apply (iterateKernel P n) (iterateKernel Pbar n) f hf).1
      (iterateKernel_strongLumpability P Pbar f hf h n) x

theorem iterateKernel_preimage
    (P : Kernel X X) (Pbar : Kernel M M)
    (f : X → M) (hf : Measurable f)
    (h : StrongLumpability P Pbar f hf)
    (n : ℕ) (x : X) (B : Set M) (hB : MeasurableSet B) :
    iterateKernel P n x (f ⁻¹' B) =
      iterateKernel Pbar n (f x) B := by
  exact
    (strongLumpability_iff_preimage (iterateKernel P n) (iterateKernel Pbar n) f hf).1
      (iterateKernel_strongLumpability P Pbar f hf h n) x B hB


/-- Coordinatewise map of a finite history. -/
def mapHistory (f : X → M) (n : ℕ)
    (x : (i : Finset.Iic n) → X) :
    (i : Finset.Iic n) → M :=
  fun i => f (x i)

theorem measurable_mapHistory
    (f : X → M) (hf : Measurable f) (n : ℕ) :
    Measurable (mapHistory f n) := by
  apply measurable_pi_iff.mpr
  intro i
  exact hf.comp (measurable_pi_apply i)

def lastHistoryIndex (n : ℕ) : Finset.Iic n :=
  ⟨n, Finset.mem_Iic.mpr le_rfl⟩

/-- A homogeneous Markov kernel viewed as a history kernel: only the last
coordinate of the history is read. -/
noncomputable def homHistoryKernel
    (P : Kernel X X) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → X) X :=
  Kernel.comap P
    (fun x => x (lastHistoryIndex n))
    (measurable_pi_apply (lastHistoryIndex n))

theorem isMarkovKernel_homHistoryKernel
    (P : Kernel X X) [IsMarkovKernel P] (n : ℕ) :
    IsMarkovKernel (homHistoryKernel P n) := by
  unfold homHistoryKernel
  infer_instance

theorem homHistoryKernel_intertwines
    (P : Kernel X X) (Pbar : Kernel M M)
    (f : X → M) (hf : Measurable f)
    (h : StrongLumpability P Pbar f hf) :
    Kernel.map (homHistoryKernel P n) f =
      Kernel.comap (homHistoryKernel Pbar n)
        (mapHistory f n) (measurable_mapHistory f hf n) := by
  ext x B hB
  rw [Kernel.map_apply' _ hf _ hB, Kernel.comap_apply']
  unfold homHistoryKernel
  rw [Kernel.comap_apply', Kernel.comap_apply']
  exact
    (strongLumpability_iff_preimage P Pbar f hf).1 h
      (x (lastHistoryIndex n)) B hB


/-- Append one sampled state to a finite history. -/
def appendHistory (n : ℕ)
    (p : ((i : Finset.Iic n) → X) × X) :
    (i : Finset.Iic (n + 1)) → X :=
  IicProdIoc (X := fun _ : ℕ => X) n (n + 1)
    (p.1, MeasurableEquiv.piSingleton (X := fun _ : ℕ => X) n p.2)

theorem measurable_appendHistory (n : ℕ) :
    Measurable (appendHistory (X := X) n) := by
  unfold appendHistory
  exact measurable_IicProdIoc.comp
    (measurable_fst.prodMk
      ((MeasurableEquiv.piSingleton (X := fun _ : ℕ => X) n).measurable.comp
        measurable_snd))

theorem mapHistory_appendHistory
    (f : X → M) (n : ℕ)
    (x : (i : Finset.Iic n) → X) (y : X) :
    mapHistory f (n + 1) (appendHistory n (x, y)) =
      appendHistory n (mapHistory f n x, f y) := by
  ext i
  by_cases hi : (i : ℕ) ≤ n
  · simp [mapHistory, appendHistory, IicProdIoc_def, hi]
  · have hin : (i : ℕ) = n + 1 := by
      have hle : (i : ℕ) ≤ n + 1 := Finset.mem_Iic.mp i.2
      omega
    have hieq : i = ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ := Subtype.ext hin
    subst i
    simp [mapHistory, appendHistory, IicProdIoc_def,
      MeasurableEquiv.piSingleton]



theorem mapHistory_comp_appendHistory
    (f : X → M) (n : ℕ) :
    mapHistory f (n + 1) ∘ appendHistory n =
      appendHistory n ∘ Prod.map (mapHistory f n) f := by
  funext p
  exact mapHistory_appendHistory f n p.1 p.2

theorem appendHistory_prefix_next
    (n : ℕ) (x : ℕ → X) :
    appendHistory n (Preorder.frestrictLe n x, x (n + 1)) =
      Preorder.frestrictLe (n + 1) x := by
  ext i
  by_cases hi : (i : ℕ) ≤ n
  · simp [appendHistory, IicProdIoc_def, Preorder.frestrictLe_apply, hi]
  · have hin : (i : ℕ) = n + 1 := by
      have hle : (i : ℕ) ≤ n + 1 := Finset.mem_Iic.mp i.2
      omega
    have hieq :
        i = (⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic (n + 1)) :=
      Subtype.ext hin
    rw [hieq]
    simp [appendHistory, IicProdIoc_def, Preorder.frestrictLe_apply,
      MeasurableEquiv.piSingleton]

noncomputable def homTrajMeasure
    (μ : Measure X) (P : Kernel X X) [IsMarkovKernel P] :
    Measure (ℕ → X) :=
  letI : ∀ n, IsMarkovKernel (homHistoryKernel P n) :=
    fun n => isMarkovKernel_homHistoryKernel P n
  ProbabilityTheory.Kernel.trajMeasure (X := fun _ : ℕ => X) μ (homHistoryKernel P)

instance isProbabilityMeasure_homTrajMeasure
    (μ : Measure X) [IsProbabilityMeasure μ]
    (P : Kernel X X) [IsMarkovKernel P] :
    IsProbabilityMeasure (homTrajMeasure μ P) := by
  unfold homTrajMeasure
  infer_instance


theorem homTrajMeasure_prefix_zero
    (μ : Measure X) [IsProbabilityMeasure μ]
    (P : Kernel X X) [IsMarkovKernel P] :
    (homTrajMeasure μ P).map (Preorder.frestrictLe 0) =
      μ.map
        (MeasurableEquiv.piUnique
          (fun _ : Finset.Iic 0 => X)).symm := by
  letI : ∀ k, IsMarkovKernel (homHistoryKernel P k) :=
    fun k => isMarkovKernel_homHistoryKernel P k
  rw [homTrajMeasure, ProbabilityTheory.Kernel.trajMeasure,
    Measure.map_comp _ _ (by fun_prop),
    ProbabilityTheory.Kernel.traj_map_frestrictLe,
    ProbabilityTheory.Kernel.partialTraj_self,
    Measure.id_comp]

theorem homTrajMeasure_prefix_succ
    (μ : Measure X) [IsProbabilityMeasure μ]
    (P : Kernel X X) [IsMarkovKernel P]
    (n : ℕ) :
    (((homTrajMeasure μ P).map (Preorder.frestrictLe n)) ⊗ₘ homHistoryKernel P n).map
        (appendHistory n) =
      (homTrajMeasure μ P).map (Preorder.frestrictLe (n + 1)) := by
  letI : ∀ k, IsMarkovKernel (homHistoryKernel P k) :=
    fun k => isMarkovKernel_homHistoryKernel P k
  have hstep :=
    ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (X := fun _ : ℕ => X) (μ₀ := μ) (κ := homHistoryKernel P) (a := n)
  have hstep' :
      ((homTrajMeasure μ P).map (Preorder.frestrictLe n)) ⊗ₘ homHistoryKernel P n =
        (homTrajMeasure μ P).map
          (fun x => (Preorder.frestrictLe n x, x (n + 1))) := by
    simpa [homTrajMeasure] using hstep
  rw [hstep']
  rw [Measure.map_map (measurable_appendHistory n) (by fun_prop)]
  have hcomp :
      appendHistory n ∘
          (fun x : ℕ → X => (Preorder.frestrictLe n x, x (n + 1))) =
        Preorder.frestrictLe (n + 1) := by
    funext x
    exact appendHistory_prefix_next n x
  rw [hcomp]


theorem homHistory_compProd_naturality
    (μh : Measure ((i : Finset.Iic n) → X)) [SFinite μh]
    (P : Kernel X X) (Pbar : Kernel M M)
    [IsMarkovKernel P] [IsMarkovKernel Pbar]
    (f : X → M) (hf : Measurable f)
    (h : StrongLumpability P Pbar f hf) :
    (μh ⊗ₘ homHistoryKernel P n).map
        (Prod.map (mapHistory f n) f) =
      (μh.map (mapHistory f n)) ⊗ₘ homHistoryKernel Pbar n := by
  letI : IsMarkovKernel (homHistoryKernel P n) :=
    isMarkovKernel_homHistoryKernel P n
  letI : IsMarkovKernel (homHistoryKernel Pbar n) :=
    isMarkovKernel_homHistoryKernel Pbar n
  have hF : Measurable (mapHistory f n) :=
    measurable_mapHistory f hf n
  have hk :
      Kernel.map (homHistoryKernel P n) f =
        Kernel.comap (homHistoryKernel Pbar n)
          (mapHistory f n) hF :=
    homHistoryKernel_intertwines P Pbar f hf h
  calc
    (μh ⊗ₘ homHistoryKernel P n).map
        (Prod.map (mapHistory f n) f)
        =
      ((μh ⊗ₘ homHistoryKernel P n).map (Prod.map id f)).map
        (Prod.map (mapHistory f n) id) := by
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
          rfl
    _ =
      (μh ⊗ₘ (homHistoryKernel P n).map f).map
        (Prod.map (mapHistory f n) id) := by
          rw [← Measure.compProd_map hf]
    _ =
      (μh ⊗ₘ Kernel.comap (homHistoryKernel Pbar n)
          (mapHistory f n) hF).map
        (Prod.map (mapHistory f n) id) := by
          rw [hk]
    _ = (μh.map (mapHistory f n)) ⊗ₘ homHistoryKernel Pbar n := by
      ext s hs
      rw [Measure.map_apply (by fun_prop) hs,
        Measure.compProd_apply (by measurability),
        Measure.compProd_apply hs,
        lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hF]
      rfl


theorem mapHistory_piUnique_zero
    (f : X → M) :
    mapHistory f 0 ∘
        (MeasurableEquiv.piUnique
          (fun _ : Finset.Iic 0 => X)).symm =
      (MeasurableEquiv.piUnique
        (fun _ : Finset.Iic 0 => M)).symm ∘ f := by
  funext x
  ext i
  rfl

theorem homTrajMeasure_prefix_naturality
    (μ : Measure X) [IsProbabilityMeasure μ]
    (P : Kernel X X) (Pbar : Kernel M M)
    [IsMarkovKernel P] [IsMarkovKernel Pbar]
    (f : X → M) (hf : Measurable f)
    (h : StrongLumpability P Pbar f hf)
    (n : ℕ) :
    ((homTrajMeasure μ P).map (Preorder.frestrictLe n)).map
        (mapHistory f n) =
      (homTrajMeasure (μ.map f) Pbar).map
        (Preorder.frestrictLe n) := by
  letI : IsProbabilityMeasure (μ.map f) :=
    (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).2 inferInstance
  induction n with
  | zero =>
      rw [homTrajMeasure_prefix_zero μ P,
        homTrajMeasure_prefix_zero (μ.map f) Pbar,
        Measure.map_map (measurable_mapHistory f hf 0) (by fun_prop),
        Measure.map_map (by fun_prop) hf,
        mapHistory_piUnique_zero f]
  | succ n ih =>
      rw [← homTrajMeasure_prefix_succ μ P n]
      rw [Measure.map_map
        (measurable_mapHistory f hf (n + 1))
        (measurable_appendHistory n)]
      rw [mapHistory_comp_appendHistory f n]
      rw [← Measure.map_map
        (measurable_appendHistory (X := M) n)
        ((measurable_mapHistory f hf n).prodMap hf)]
      rw [homHistory_compProd_naturality
        (μh := (homTrajMeasure μ P).map (Preorder.frestrictLe n))
        P Pbar f hf h]
      rw [ih]
      exact homTrajMeasure_prefix_succ (μ.map f) Pbar n


def mapPath (f : X → M) (x : ℕ → X) : ℕ → M :=
  fun k => f (x k)

theorem measurable_mapPath
    (f : X → M) (hf : Measurable f) :
    Measurable (mapPath f) := by
  apply measurable_pi_iff.mpr
  intro k
  exact hf.comp (measurable_pi_apply k)

theorem frestrictLe_mapPath
    (f : X → M) (n : ℕ) :
    Preorder.frestrictLe n ∘ mapPath f =
      mapHistory f n ∘ Preorder.frestrictLe n := by
  rfl

theorem pathMeasure_eq_of_prefix_eq
    (μpath νpath : Measure (ℕ → M))
    [IsProbabilityMeasure μpath] [IsProbabilityMeasure νpath]
    (hprefix : ∀ n,
      μpath.map (Preorder.frestrictLe n) =
        νpath.map (Preorder.frestrictLe n)) :
    μpath = νpath := by
  let Pfin : (I : Finset ℕ) → Measure ((i : I) → M) :=
    fun I => μpath.map I.restrict
  letI : ∀ I, IsProbabilityMeasure (Pfin I) := fun I => by
    dsimp [Pfin]
    exact Measure.isProbabilityMeasure_map
      (Finset.measurable_restrict I).aemeasurable
  have hνfin :
      ∀ I : Finset ℕ, νpath.map I.restrict = Pfin I := by
    intro I
    dsimp [Pfin]
    have hsub : I ⊆ Finset.Iic (I.sup id) := I.subset_Iic_sup_id
    calc
      νpath.map I.restrict =
          (νpath.map (Preorder.frestrictLe (I.sup id))).map
            (Finset.restrict₂ hsub) := by
        rw [Measure.map_map
          (Finset.measurable_restrict₂ hsub)
          (Preorder.measurable_frestrictLe
            (X := fun _ : ℕ => M) (I.sup id))]
        rw [Finset.restrict₂_comp_restrict hsub]
      _ =
          (μpath.map (Preorder.frestrictLe (I.sup id))).map
            (Finset.restrict₂ hsub) := by
        rw [hprefix (I.sup id)]
      _ = μpath.map I.restrict := by
        rw [Measure.map_map
          (Finset.measurable_restrict₂ hsub)
          (Preorder.measurable_frestrictLe
            (X := fun _ : ℕ => M) (I.sup id))]
        rw [Finset.restrict₂_comp_restrict hsub]
  have hμ :
      MeasureTheory.IsProjectiveLimit μpath Pfin := by
    intro I
    rfl
  have hν :
      MeasureTheory.IsProjectiveLimit νpath Pfin :=
    hνfin
  exact hμ.unique hν

theorem homTrajMeasure_path_naturality
    (μ : Measure X) [IsProbabilityMeasure μ]
    (P : Kernel X X) (Pbar : Kernel M M)
    [IsMarkovKernel P] [IsMarkovKernel Pbar]
    (f : X → M) (hf : Measurable f)
    (h : StrongLumpability P Pbar f hf) :
    (homTrajMeasure μ P).map (mapPath f) =
      homTrajMeasure (μ.map f) Pbar := by
  letI : IsProbabilityMeasure (μ.map f) :=
    (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).2 inferInstance
  letI : IsProbabilityMeasure ((homTrajMeasure μ P).map (mapPath f)) :=
    Measure.isProbabilityMeasure_map (measurable_mapPath f hf).aemeasurable
  apply pathMeasure_eq_of_prefix_eq
  intro n
  rw [Measure.map_map
    (Preorder.measurable_frestrictLe n)
    (measurable_mapPath f hf)]
  rw [frestrictLe_mapPath f n]
  rw [← Measure.map_map
    (measurable_mapHistory f hf n)
    (Preorder.measurable_frestrictLe n)]
  exact homTrajMeasure_prefix_naturality μ P Pbar f hf h n

/-- Source clause (1) of P-DYN-01 expressed at the level of complete path laws:
for every microscopic probability initial law, the coordinatewise macro
pushforward of the microscopic Markov trajectory is exactly the trajectory of
one common macro kernel started from the pushed-forward initial law. -/
def PathLawLumpability
    (P : Kernel X X) (Pbar : Kernel M M)
    [IsMarkovKernel P] [IsMarkovKernel Pbar]
    (f : X → M) (hf : Measurable f) : Prop :=
  ∀ (μ : Measure X), IsProbabilityMeasure μ →
    (homTrajMeasure μ P).map (mapPath f) =
      homTrajMeasure (μ.map f) Pbar

theorem strongLumpability_implies_pathLaw
    (P : Kernel X X) (Pbar : Kernel M M)
    [IsMarkovKernel P] [IsMarkovKernel Pbar]
    (f : X → M) (hf : Measurable f)
    (h : StrongLumpability P Pbar f hf) :
    PathLawLumpability P Pbar f hf := by
  unfold PathLawLumpability
  intro μ hμ
  letI : IsProbabilityMeasure μ := hμ
  exact homTrajMeasure_path_naturality μ P Pbar f hf h

theorem homHistoryKernel_apply_pushforward
    (P : Kernel X X) (Pbar : Kernel M M)
    (f : X → M) (hf : Measurable f)
    (h : StrongLumpability P Pbar f hf)
    (n : ℕ) (x : (i : Finset.Iic n) → X) :
    (homHistoryKernel P n x).map f =
      homHistoryKernel Pbar n (mapHistory f n x) := by
  have hk := congrArg
    (fun K : Kernel ((i : Finset.Iic n) → X) M => K x)
    (homHistoryKernel_intertwines P Pbar f hf h)
  rw [Kernel.map_apply _ hf, Kernel.comap_apply] at hk
  exact hk

end UEOT.V3.DynamicsKernel
