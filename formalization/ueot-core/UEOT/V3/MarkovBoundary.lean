import Mathlib.Data.Set.Lattice
import Mathlib.Tactic

/-!
# P-INT-03 foundation — uniqueness of a minimal Markov boundary

Fix a target Y and write `CI A C` for the conditional-independence statement
Y ⟂ A | C.  The source assumes the semigraphoid laws together with
intersection.  This module isolates exactly the subset-decomposition,
weak-union, contraction and intersection operations used by the written proof
and derives uniqueness of a minimal blanket.
-/

namespace UEOT.V3.MarkovBoundary

open Set

universe uW

variable {W : Type uW}

/-- The conditional-independence laws used in the P-INT-03 proof, with the
target variable Y suppressed from notation. -/
structure CIAxioms (CI : Set W → Set W → Prop) : Prop where
  decomposition :
    ∀ {A B C : Set W}, CI A C → B ⊆ A → CI B C
  weakUnion :
    ∀ {A B C : Set W}, CI (A ∪ B) C → CI A (B ∪ C)
  contraction :
    ∀ {A B C : Set W}, CI A C → CI B (A ∪ C) → CI (A ∪ B) C
  intersection :
    ∀ {A B C : Set W}, CI A (B ∪ C) → CI B (A ∪ C) → CI (A ∪ B) C

def IsBlanket (CI : Set W → Set W → Prop) (B : Set W) : Prop :=
  CI Bᶜ B

def IsBoundary (CI : Set W → Set W → Prop) (B : Set W) : Prop :=
  IsBlanket CI B ∧
    ∀ C, C ⊆ B → IsBlanket CI C → C = B

/-- P-INT-03 core: under semigraphoid decomposition/weak-union/contraction
and intersection, two inclusion-minimal blankets coincide. -/
theorem boundary_unique
    (CI : Set W → Set W → Prop) (hCI : CIAxioms CI)
    {B C : Set W}
    (hB : IsBoundary CI B) (hC : IsBoundary CI C) :
    B = C := by
  let A : Set W := B \ C
  let D : Set W := C \ B
  let F : Set W := B ∩ C
  let R : Set W := (B ∪ C)ᶜ

  have hB_AF : A ∪ F = B := by
    ext x
    simp only [A, F, Set.mem_union, Set.mem_diff, Set.mem_inter_iff]
    tauto
  have hC_DF : D ∪ F = C := by
    ext x
    simp only [D, F, Set.mem_union, Set.mem_diff, Set.mem_inter_iff]
    tauto
  have hBc_RD : R ∪ D = Bᶜ := by
    ext x
    simp only [R, D, Set.mem_union, Set.mem_diff, Set.mem_compl_iff]
    tauto
  have hFc_ADR : (A ∪ D) ∪ R = Fᶜ := by
    ext x
    simp only [A, D, F, R, Set.mem_union, Set.mem_diff,
      Set.mem_inter_iff, Set.mem_compl_iff]
    tauto

  have hDsub : D ⊆ Bᶜ := by
    intro x hx
    exact hx.2
  have hAsub : A ⊆ Cᶜ := by
    intro x hx
    exact hx.2
  have hRsub : R ⊆ Bᶜ := by
    intro x hx
    exact fun hxB => hx (Or.inl hxB)

  have hD_B : CI D B :=
    hCI.decomposition hB.1 hDsub
  have hA_C : CI A C :=
    hCI.decomposition hC.1 hAsub
  have hD_AF : CI D (A ∪ F) := by
    rw [hB_AF]
    exact hD_B
  have hA_DF : CI A (D ∪ F) := by
    rw [hC_DF]
    exact hA_C

  have hDA_F : CI (D ∪ A) F :=
    hCI.intersection hD_AF hA_DF
  have hAD_F : CI (A ∪ D) F := by
    simpa [union_comm] using hDA_F

  have hRD_B : CI (R ∪ D) B := by
    rw [hBc_RD]
    exact hB.1
  have hR_DB : CI R (D ∪ B) :=
    hCI.weakUnion hRD_B
  have hR_ADF : CI R ((A ∪ D) ∪ F) := by
    have hcond : D ∪ B = (A ∪ D) ∪ F := by
      rw [← hB_AF]
      ext x
      simp only [Set.mem_union]
      tauto
    rw [← hcond]
    exact hR_DB

  have hADR_F : CI ((A ∪ D) ∪ R) F :=
    hCI.contraction hAD_F hR_ADF
  have hFblanket : IsBlanket CI F := by
    unfold IsBlanket
    rw [← hFc_ADR]
    exact hADR_F

  have hFB : F ⊆ B := inter_subset_left
  have hFC : F ⊆ C := inter_subset_right
  have hEqB : F = B := hB.2 F hFB hFblanket
  have hEqC : F = C := hC.2 F hFC hFblanket
  exact hEqB.symm.trans hEqC


/-- Source-facing P-INT-03 wrapper.  The manuscript phrases the result for a
finite variable universe `W`; the proof above is stronger and does not use
finiteness once the conditional-independence laws are supplied. -/
theorem p_int_03_boundary_unique
    [Fintype W]
    (CI : Set W → Set W → Prop) (hCI : CIAxioms CI)
    {B C : Set W}
    (hB : IsBoundary CI B) (hC : IsBoundary CI C) :
    B = C :=
  boundary_unique CI hCI hB hC

end UEOT.V3.MarkovBoundary
