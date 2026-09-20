import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# P-DDH-05 — singular-value effective-dimension stability

This module formalizes frozen UEOT Core v3 §23.5.  The source theorem uses the
genuine Euclidean operator 2-norm: if an estimated finite sensitivity matrix is
within `eta` of the reference matrix, every corresponding singular value moves
by at most `eta`.  Consequently, the source window
`sigma_3(S) + eta < tau < sigma_2(S) - eta` certifies exactly two estimated
singular values above `tau`.

Mathlib singular values are zero-indexed, so source `sigma_2` and `sigma_3` are
indices `1` and `2`.  The proof derives the indexed Lipschitz bound from the
finite-dimensional variational/min-max argument itself: top and tail right
singular subspaces have a forced nonzero intersection, and the genuine operator
norm controls the perturbation on that vector.  No Frobenius-norm replacement,
rank-two premise, singular-vector closeness assumption, or assumed Weyl theorem
is introduced.
-/

namespace UEOT.V3.SingularValueEffectiveDimension
noncomputable section
open Module InnerProductSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

def rightSingularBasis (T : E →ₗ[ℝ] F) :
    OrthonormalBasis (Fin (finrank ℝ E)) ℝ E :=
  T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl

lemma adjoint_comp_self_apply_rightSingularBasis
    (T : E →ₗ[ℝ] F) (i : Fin (finrank ℝ E)) :
    (T.adjoint ∘ₗ T) (rightSingularBasis T i) =
      (T.singularValues i ^ 2) • rightSingularBasis T i := by
  rw [rightSingularBasis]
  rw [T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis]
  rw [← T.sq_singularValues_fin rfl i]
  rfl

lemma norm_apply_rightSingularBasis
    (T : E →ₗ[ℝ] F) (i : Fin (finrank ℝ E)) :
    ‖T (rightSingularBasis T i)‖ = T.singularValues i := by
  have heig := adjoint_comp_self_apply_rightSingularBasis T i
  have hsq : ‖T (rightSingularBasis T i)‖ ^ 2 = T.singularValues i ^ 2 := by
    calc
      ‖T (rightSingularBasis T i)‖ ^ 2
          = inner ℝ (T (rightSingularBasis T i)) (T (rightSingularBasis T i)) := by
              rw [real_inner_self_eq_norm_sq]
      _ = inner ℝ ((T.adjoint ∘ₗ T) (rightSingularBasis T i))
          (rightSingularBasis T i) := by
              rw [LinearMap.comp_apply]
              exact (LinearMap.adjoint_inner_left T (rightSingularBasis T i)
                (T (rightSingularBasis T i))).symm
      _ = inner ℝ ((T.singularValues i ^ 2) • rightSingularBasis T i)
          (rightSingularBasis T i) := by rw [heig]
      _ = T.singularValues i ^ 2 := by
          rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
          simp [rightSingularBasis]
  exact (sq_eq_sq₀ (norm_nonneg _) (T.singularValues_nonneg i)).mp hsq

end
end UEOT.V3.SingularValueEffectiveDimension

namespace UEOT.V3.SingularValueEffectiveDimension
noncomputable section
open Module InnerProductSpace
open scoped RealInnerProductSpace BigOperators

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

lemma norm_apply_sq_eq_sum_singular
    (T : E →ₗ[ℝ] F) (x : E) :
    ‖T x‖ ^ 2 = ∑ j : Fin (finrank ℝ E),
      (T.singularValues j ^ 2) * (inner ℝ (rightSingularBasis T j) x) ^ 2 := by
  let b := rightSingularBasis T
  have hadj : inner ℝ ((T.adjoint ∘ₗ T) x) x = ‖T x‖ ^ 2 := by
    rw [LinearMap.comp_apply]
    rw [LinearMap.adjoint_inner_left]
    rw [real_inner_self_eq_norm_sq]
  calc
    ‖T x‖ ^ 2 = inner ℝ ((T.adjoint ∘ₗ T) x) x := hadj.symm
    _ = ∑ j : Fin (finrank ℝ E),
        inner ℝ ((T.adjoint ∘ₗ T) x) (b j) * inner ℝ (b j) x := by
          rw [← b.sum_inner_mul_inner]
    _ = ∑ j : Fin (finrank ℝ E),
        (T.singularValues j ^ 2) * (inner ℝ (b j) x) ^ 2 := by
          apply Finset.sum_congr rfl
          intro j hj
          have hsym := T.isSymmetric_adjoint_comp_self
          have hself : (T.adjoint ∘ₗ T) (b j) =
              (T.singularValues j ^ 2) • b j := by
            simpa [b, rightSingularBasis] using adjoint_comp_self_apply_rightSingularBasis T j
          calc
            inner ℝ ((T.adjoint ∘ₗ T) x) (b j) * inner ℝ (b j) x
                = inner ℝ x ((T.adjoint ∘ₗ T) (b j)) * inner ℝ (b j) x := by
                    rw [hsym x (b j)]
            _ = inner ℝ x ((T.singularValues j ^ 2) • b j) * inner ℝ (b j) x := by rw [hself]
            _ = (T.singularValues j ^ 2) * (inner ℝ (b j) x) ^ 2 := by
                    rw [real_inner_smul_right, real_inner_comm x (b j)]
                    ring
    _ = _ := rfl

end
end UEOT.V3.SingularValueEffectiveDimension

namespace UEOT.V3.SingularValueEffectiveDimension
noncomputable section
open Module InnerProductSpace
open scoped RealInnerProductSpace BigOperators

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]


def topSingularSubspace (T : E →ₗ[ℝ] F) (i : Fin (finrank ℝ E)) : Submodule ℝ E :=
  Submodule.span ℝ (rightSingularBasis T '' Set.Iic i)

def tailSingularSubspace (T : E →ₗ[ℝ] F) (i : Fin (finrank ℝ E)) : Submodule ℝ E :=
  Submodule.span ℝ (rightSingularBasis T '' Set.Ici i)

lemma inner_eq_zero_of_mem_top_of_not_le
    (T : E →ₗ[ℝ] F) (i j : Fin (finrank ℝ E)) (x : E)
    (hx : x ∈ topSingularSubspace T i) (hji : ¬ j ≤ i) :
    inner ℝ (rightSingularBasis T j) x = 0 := by
  let b := rightSingularBasis T
  have hsupp : ↑(b.toBasis.repr x).support ⊆ Set.Iic i := by
    exact (b.toBasis.mem_span_image).mp hx
  have hjnot : j ∉ (b.toBasis.repr x).support := by
    intro hj
    exact hji (hsupp hj)
  rw [← b.repr_apply_apply]
  exact Finsupp.notMem_support_iff.mp hjnot

lemma inner_eq_zero_of_mem_tail_of_not_le
    (T : E →ₗ[ℝ] F) (i j : Fin (finrank ℝ E)) (x : E)
    (hx : x ∈ tailSingularSubspace T i) (hij : ¬ i ≤ j) :
    inner ℝ (rightSingularBasis T j) x = 0 := by
  let b := rightSingularBasis T
  have hsupp : ↑(b.toBasis.repr x).support ⊆ Set.Ici i := by
    exact (b.toBasis.mem_span_image).mp hx
  have hjnot : j ∉ (b.toBasis.repr x).support := by
    intro hj
    exact hij (hsupp hj)
  rw [← b.repr_apply_apply]
  exact Finsupp.notMem_support_iff.mp hjnot

end
end UEOT.V3.SingularValueEffectiveDimension

namespace UEOT.V3.SingularValueEffectiveDimension
noncomputable section
open Module InnerProductSpace
open scoped RealInnerProductSpace BigOperators

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

lemma singular_sq_mul_norm_sq_le_of_mem_top
    (T : E →ₗ[ℝ] F) (i : Fin (finrank ℝ E)) (x : E)
    (hx : x ∈ topSingularSubspace T i) :
    (T.singularValues i ^ 2) * ‖x‖ ^ 2 ≤ ‖T x‖ ^ 2 := by
  let b := rightSingularBasis T
  rw [norm_apply_sq_eq_sum_singular T x, ← b.sum_sq_inner_right x, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hji : j ≤ i
  · have hs : T.singularValues i ≤ T.singularValues j :=
      T.singularValues_antitone hji
    have hs2 : T.singularValues i ^ 2 ≤ T.singularValues j ^ 2 := by
      nlinarith [T.singularValues_nonneg i, T.singularValues_nonneg j]
    exact mul_le_mul_of_nonneg_right hs2 (sq_nonneg _)
  · have hz : inner ℝ (b j) x = 0 := by
      simpa [b] using inner_eq_zero_of_mem_top_of_not_le T i j x hx hji
    simp [hz, b]

lemma norm_apply_sq_le_singular_sq_mul_norm_sq_of_mem_tail
    (T : E →ₗ[ℝ] F) (i : Fin (finrank ℝ E)) (x : E)
    (hx : x ∈ tailSingularSubspace T i) :
    ‖T x‖ ^ 2 ≤ (T.singularValues i ^ 2) * ‖x‖ ^ 2 := by
  let b := rightSingularBasis T
  rw [norm_apply_sq_eq_sum_singular T x, ← b.sum_sq_inner_right x, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hij : i ≤ j
  · have hs : T.singularValues j ≤ T.singularValues i :=
      T.singularValues_antitone hij
    have hs2 : T.singularValues j ^ 2 ≤ T.singularValues i ^ 2 := by
      nlinarith [T.singularValues_nonneg i, T.singularValues_nonneg j]
    exact mul_le_mul_of_nonneg_right hs2 (sq_nonneg _)
  · have hz : inner ℝ (b j) x = 0 := by
      simpa [b] using inner_eq_zero_of_mem_tail_of_not_le T i j x hx hij
    simp [hz, b]

lemma singular_mul_norm_le_norm_apply_of_mem_top
    (T : E →ₗ[ℝ] F) (i : Fin (finrank ℝ E)) (x : E)
    (hx : x ∈ topSingularSubspace T i) :
    T.singularValues i * ‖x‖ ≤ ‖T x‖ := by
  have hsq := singular_sq_mul_norm_sq_le_of_mem_top T i x hx
  apply (sq_le_sq₀ (mul_nonneg (T.singularValues_nonneg i) (norm_nonneg x))
    (norm_nonneg (T x))).mp
  calc
    (T.singularValues i * ‖x‖) ^ 2 = (T.singularValues i ^ 2) * ‖x‖ ^ 2 := by ring
    _ ≤ ‖T x‖ ^ 2 := hsq

lemma norm_apply_le_singular_mul_norm_of_mem_tail
    (T : E →ₗ[ℝ] F) (i : Fin (finrank ℝ E)) (x : E)
    (hx : x ∈ tailSingularSubspace T i) :
    ‖T x‖ ≤ T.singularValues i * ‖x‖ := by
  have hsq := norm_apply_sq_le_singular_sq_mul_norm_sq_of_mem_tail T i x hx
  apply (sq_le_sq₀ (norm_nonneg (T x))
    (mul_nonneg (T.singularValues_nonneg i) (norm_nonneg x))).mp
  calc
    ‖T x‖ ^ 2 ≤ (T.singularValues i ^ 2) * ‖x‖ ^ 2 := hsq
    _ = (T.singularValues i * ‖x‖) ^ 2 := by ring

end
end UEOT.V3.SingularValueEffectiveDimension

namespace UEOT.V3.SingularValueEffectiveDimension
noncomputable section
open Module InnerProductSpace
open scoped RealInnerProductSpace BigOperators

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

lemma finrank_topSingularSubspace
    (T : E →ₗ[ℝ] F) (i : Fin (finrank ℝ E)) :
    finrank ℝ (topSingularSubspace T i) = i + 1 := by
  let b := rightSingularBasis T
  let v : Set.Iic i → E := fun j => b j
  have hli : LinearIndependent ℝ v :=
    b.orthonormal.linearIndependent.comp ((↑) : Set.Iic i → Fin (finrank ℝ E)) Subtype.val_injective
  have h := finrank_span_eq_card hli
  have hrange : Set.range v = b '' Set.Iic i := by
    ext x
    simp [v]
  rw [hrange] at h
  change finrank ℝ (Submodule.span ℝ (rightSingularBasis T '' Set.Iic i)) = i + 1
  simpa [b] using h

lemma finrank_tailSingularSubspace
    (T : E →ₗ[ℝ] F) (i : Fin (finrank ℝ E)) :
    finrank ℝ (tailSingularSubspace T i) = finrank ℝ E - i := by
  let b := rightSingularBasis T
  let v : Set.Ici i → E := fun j => b j
  have hli : LinearIndependent ℝ v :=
    b.orthonormal.linearIndependent.comp ((↑) : Set.Ici i → Fin (finrank ℝ E)) Subtype.val_injective
  have h := finrank_span_eq_card hli
  have hrange : Set.range v = b '' Set.Ici i := by
    ext x
    simp [v]
  rw [hrange] at h
  change finrank ℝ (Submodule.span ℝ (rightSingularBasis T '' Set.Ici i)) = finrank ℝ E - i
  simpa [b] using h

end
end UEOT.V3.SingularValueEffectiveDimension

namespace UEOT.V3.SingularValueEffectiveDimension
noncomputable section
open Module InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma inf_ne_bot_of_finrank_lt_add (U V : Submodule ℝ E)
    (h : finrank ℝ E < finrank ℝ U + finrank ℝ V) :
    U ⊓ V ≠ ⊥ := by
  intro hinf
  have hd := Submodule.finrank_sup_add_finrank_inf_eq U V
  rw [hinf, finrank_bot, add_zero] at hd
  have hle : finrank ℝ (U ⊔ V : Submodule ℝ E) ≤ finrank ℝ E := Submodule.finrank_le _
  omega

end
end UEOT.V3.SingularValueEffectiveDimension

namespace UEOT.V3.SingularValueEffectiveDimension
noncomputable section
open Module InnerProductSpace
open scoped RealInnerProductSpace BigOperators

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

lemma singularValue_le_add_opNorm_sub
    (T S : E →ₗ[ℝ] F) (i : Fin (finrank ℝ E)) :
    T.singularValues i ≤ S.singularValues i + ‖(T - S).toContinuousLinearMap‖ := by
  let U := topSingularSubspace T i
  let V := tailSingularSubspace S i
  have hdim : finrank ℝ E < finrank ℝ U + finrank ℝ V := by
    rw [show finrank ℝ U = i + 1 by simpa [U] using finrank_topSingularSubspace T i,
      show finrank ℝ V = finrank ℝ E - i by
        simpa [V] using finrank_tailSingularSubspace S i]
    omega
  have hinf : U ⊓ V ≠ ⊥ := inf_ne_bot_of_finrank_lt_add U V hdim
  obtain ⟨x, hx0⟩ := Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr hinf)
  have hxU : (x : E) ∈ U := x.property.1
  have hxV : (x : E) ∈ V := x.property.2
  have hlower : T.singularValues i * ‖(x : E)‖ ≤ ‖T (x : E)‖ := by
    exact singular_mul_norm_le_norm_apply_of_mem_top T i x (by simpa [U] using hxU)
  have hupper : ‖S (x : E)‖ ≤ S.singularValues i * ‖(x : E)‖ := by
    exact norm_apply_le_singular_mul_norm_of_mem_tail S i x (by simpa [V] using hxV)
  have hpert : ‖T (x : E)‖ ≤ ‖S (x : E)‖ + ‖(T - S).toContinuousLinearMap‖ * ‖(x : E)‖ := by
    calc
      ‖T (x : E)‖ = ‖S (x : E) + (T - S) (x : E)‖ := by
        congr 1
        simp
      _ ≤ ‖S (x : E)‖ + ‖(T - S) (x : E)‖ := norm_add_le _ _
      _ ≤ ‖S (x : E)‖ + ‖(T - S).toContinuousLinearMap‖ * ‖(x : E)‖ := by
        gcongr
        exact (T - S).toContinuousLinearMap.le_opNorm (x : E)
  have hmul : T.singularValues i * ‖(x : E)‖ ≤
      (S.singularValues i + ‖(T - S).toContinuousLinearMap‖) * ‖(x : E)‖ := by
    calc
      T.singularValues i * ‖(x : E)‖ ≤ ‖T (x : E)‖ := hlower
      _ ≤ ‖S (x : E)‖ + ‖(T - S).toContinuousLinearMap‖ * ‖(x : E)‖ := hpert
      _ ≤ S.singularValues i * ‖(x : E)‖ + ‖(T - S).toContinuousLinearMap‖ * ‖(x : E)‖ := by
        gcongr
      _ = (S.singularValues i + ‖(T - S).toContinuousLinearMap‖) * ‖(x : E)‖ := by ring
  have hxE : (x : E) ≠ 0 := by
    intro h
    apply hx0
    exact Subtype.ext h
  have hxnorm : 0 < ‖(x : E)‖ := norm_pos_iff.mpr hxE
  exact le_of_mul_le_mul_right hmul hxnorm

end
end UEOT.V3.SingularValueEffectiveDimension

namespace UEOT.V3.SingularValueEffectiveDimension
noncomputable section
open Module InnerProductSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
lemma opNorm_sub_comm (T S : E →ₗ[ℝ] F) :
    ‖(T - S).toContinuousLinearMap‖ = ‖(S - T).toContinuousLinearMap‖ := by
  change ‖T.toContinuousLinearMap - S.toContinuousLinearMap‖ =
    ‖S.toContinuousLinearMap - T.toContinuousLinearMap‖
  exact norm_sub_rev _ _

lemma singularValues_lipschitz
    (T S : E →ₗ[ℝ] F) (i : ℕ) :
    |T.singularValues i - S.singularValues i| ≤ ‖(T - S).toContinuousLinearMap‖ := by
  by_cases hi : i < finrank ℝ E
  · let fi : Fin (finrank ℝ E) := ⟨i, hi⟩
    have hTS := singularValue_le_add_opNorm_sub T S fi
    have hST := singularValue_le_add_opNorm_sub S T fi
    have hnorm := opNorm_sub_comm T S
    rw [← hnorm] at hST
    exact abs_le.2 ⟨by linarith, by linarith⟩
  · have hle : finrank ℝ E ≤ i := Nat.le_of_not_gt hi
    rw [T.singularValues_of_finrank_le hle, S.singularValues_of_finrank_le hle, sub_zero, abs_zero]
    exact norm_nonneg _

end
end UEOT.V3.SingularValueEffectiveDimension

namespace UEOT.V3.SingularValueEffectiveDimension
noncomputable section
open Module InnerProductSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

lemma singularValues_lipschitz_of_opNorm_le
    (T S : E →ₗ[ℝ] F) (eta : ℝ)
    (hpert : ‖(T - S).toContinuousLinearMap‖ ≤ eta) (i : ℕ) :
    |T.singularValues i - S.singularValues i| ≤ eta :=
  (singularValues_lipschitz T S i).trans hpert

lemma exactly_two_singularValues_above_threshold
    (S Shat : E →ₗ[ℝ] F) (eta tau : ℝ)
    (hlip : ∀ i, |Shat.singularValues i - S.singularValues i| ≤ eta)
    (h3 : S.singularValues 2 + eta < tau)
    (h2 : tau < S.singularValues 1 - eta) :
    ∀ i, tau < Shat.singularValues i ↔ i < 2 := by
  intro i
  constructor
  · intro hhat
    by_contra hi
    have hi2 : 2 ≤ i := Nat.le_of_not_gt hi
    have hSmono : S.singularValues i ≤ S.singularValues 2 :=
      S.singularValues_antitone hi2
    have hup := (abs_le.mp (hlip i)).2
    linarith
  · intro hi
    have hi1 : i ≤ 1 := by omega
    have hSmono : S.singularValues 1 ≤ S.singularValues i :=
      S.singularValues_antitone hi1
    have hlo := (abs_le.mp (hlip i)).1
    linarith

lemma p_ddh_05_linear
    (S Shat : E →ₗ[ℝ] F) (eta tau : ℝ)
    (hpert : ‖(Shat - S).toContinuousLinearMap‖ ≤ eta)
    (h3 : S.singularValues 2 + eta < tau)
    (h2 : tau < S.singularValues 1 - eta) :
    (∀ i, |Shat.singularValues i - S.singularValues i| ≤ eta) ∧
      (∀ i, tau < Shat.singularValues i ↔ i < 2) := by
  have hlip : ∀ i, |Shat.singularValues i - S.singularValues i| ≤ eta :=
    fun i => singularValues_lipschitz_of_opNorm_le Shat S eta hpert i
  exact ⟨hlip, exactly_two_singularValues_above_threshold S Shat eta tau hlip h3 h2⟩

end
end UEOT.V3.SingularValueEffectiveDimension

namespace UEOT.V3.SingularValueEffectiveDimension
noncomputable section
open scoped Matrix.Norms.L2Operator

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

noncomputable def rectangularLin (A : Matrix m n ℝ) :
    EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ m :=
  Matrix.toEuclideanLin (𝕜 := ℝ) A

noncomputable def rectangularCLM (A : Matrix m n ℝ) :
    EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m :=
  (rectangularLin A).toContinuousLinearMap

lemma rectangularCLM_norm_eq (A : Matrix m n ℝ) : ‖rectangularCLM A‖ = ‖A‖ := by
  rfl

omit [Fintype m] in
lemma rectangularLin_sub (A B : Matrix m n ℝ) :
    rectangularLin (A - B) = rectangularLin A - rectangularLin B := by
  simp [rectangularLin]

lemma rectangularCLM_sub (A B : Matrix m n ℝ) :
    rectangularCLM (A - B) = rectangularCLM A - rectangularCLM B := by
  simp [rectangularCLM, rectangularLin]

lemma matrixPerturb_to_clmBound (A B : Matrix m n ℝ) (eta : ℝ)
    (h : ‖A - B‖ ≤ eta) : ‖rectangularCLM A - rectangularCLM B‖ ≤ eta := by
  rw [← rectangularCLM_sub, rectangularCLM_norm_eq]
  exact h

/-- Singular values of a finite real matrix, via its Euclidean linear map.
The sequence is zero-padded exactly as `LinearMap.singularValues` is. -/
noncomputable def matrixSingularValue (A : Matrix m n ℝ) (i : ℕ) : ℝ :=
  (rectangularLin A).singularValues i

/-- Frozen Core v3 P-DDH-05.

Under a genuine Euclidean operator-2-norm perturbation of a finite sensitivity
matrix, every indexed singular value moves by at most `eta`.  If the threshold
lies strictly between the perturbed source third/second singular-value bounds,
then exactly the first two estimated singular values exceed that threshold.
The source uses one-based `sigma_2`, `sigma_3`; Mathlib uses zero-based indices
`1`, `2`. -/
theorem p_ddh_05
    (S Shat : Matrix m n ℝ) (eta tau : ℝ)
    (hpert : ‖Shat - S‖ ≤ eta)
    (hwindow : matrixSingularValue S 2 + eta < tau ∧
      tau < matrixSingularValue S 1 - eta) :
    (∀ i, |matrixSingularValue Shat i - matrixSingularValue S i| ≤ eta) ∧
      (∀ i, tau < matrixSingularValue Shat i ↔ i < 2) := by
  let SL := rectangularLin S
  let ShatL := rectangularLin Shat
  have hlin : ‖(ShatL - SL).toContinuousLinearMap‖ ≤ eta := by
    have h := matrixPerturb_to_clmBound Shat S eta hpert
    simpa [ShatL, SL, rectangularCLM] using h
  have hcore := p_ddh_05_linear SL ShatL eta tau hlin hwindow.1 hwindow.2
  simpa [matrixSingularValue, SL, ShatL] using hcore

end
end UEOT.V3.SingularValueEffectiveDimension
