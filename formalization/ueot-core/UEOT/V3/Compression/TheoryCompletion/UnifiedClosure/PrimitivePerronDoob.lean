import UEOT.V3.Compression.PositiveEigenstructure
import UEOT.V3.FiniteDobrushin
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs

/-! Actual Doob power transport for the general finite primitive Perron source.
The positive right eigenstructure is the existing interface; its construction
from primitivity is a separate upstream obligation, not assumed to be solved here.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PrimitivePerronDoob

noncomputable section
open scoped BigOperators
open UEOT.V3.Compression.PositiveEigenstructure

variable {I : Type*} [Fintype I] [DecidableEq I] {M : Matrix I I ℝ}

/-- Every power is the original power with the same diagonal reweighting. -/
theorem transform_power (D : RightEigenData M) (n : ℕ) (i j : I) :
    (hTransform D ^ n) i j =
      (M ^ n) i j * D.vector j / (D.scale ^ n * D.vector i) := by
  have hR : D.scale ≠ 0 := D.scale_pos.ne'
  have hv : ∀ k, D.vector k ≠ 0 := fun k => (D.vector_pos k).ne'
  induction n generalizing i j with
  | zero =>
      by_cases h : i = j
      · subst j
        simp [hv]
      · simp [h]
  | succ n ih =>
      simp only [pow_succ, Matrix.mul_apply]
      calc
        (∑ k, (hTransform D ^ n) i k * hTransform D k j) =
            ∑ k, ((M ^ n) i k * M k j) * D.vector j /
              (D.scale ^ n * D.scale * D.vector i) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [ih i k]
          unfold hTransform
          field_simp [hR, hv]
        _ = (∑ k, (M ^ n) i k * M k j) * D.vector j /
            (D.scale ^ n * D.scale * D.vector i) := by
          rw [← Finset.sum_div, ← Finset.sum_mul]

/-- Normalization comes from the original eigenrelation, not a supplied row. -/
theorem transform_stochastic (D : RightEigenData M) (hM : ∀ i j, 0 ≤ M i j) :
    hTransform D ∈ Matrix.rowStochastic ℝ I := by
  refine ⟨hTransform_nonneg D hM, ?_⟩
  funext i
  simpa [Matrix.mulVec, dotProduct] using hTransform_row_sum D i

/-- Positive original powers remain positive under this same Doob transform. -/
theorem transform_primitive (D : RightEigenData M) (hM : Matrix.IsPrimitive M) :
    Matrix.IsPrimitive (hTransform D) := by
  refine ⟨hTransform_nonneg D hM.nonneg, ?_⟩
  rcases hM.exists_pos_pow with ⟨k, hk, hp⟩
  refine ⟨k, hk, ?_⟩
  intro i j
  rw [transform_power]
  exact div_pos (mul_pos (hp i j) (D.vector_pos j))
    (mul_pos (pow_pos D.scale_pos _) (D.vector_pos i))

/-- Actual invariant row evolution, at every original integer power. -/
theorem invariant_power (P : Matrix I I ℝ) (p : I → ℝ)
    (hp : Matrix.vecMul p P = p) (n : ℕ) : Matrix.vecMul p (P ^ n) = p := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hp]

/-- A primitive source forces every invariant probability coordinate positive. -/
theorem invariant_positive (P : Matrix I I ℝ) (hP : Matrix.IsPrimitive P)
    (p : stdSimplex ℝ I) (hp : Matrix.vecMul p.val P = p.val) (j : I) :
    0 < p.val j := by
  have hm : 0 < ∑ i, p.val i := lt_of_lt_of_eq zero_lt_one (stdSimplex.sum_eq_one p).symm
  obtain ⟨i, hi, hip⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun i (_ : i ∈ (Finset.univ : Finset I)) => stdSimplex.zero_le p i)).mp hm
  rcases hP.exists_pos_pow with ⟨k, hk, hkpos⟩
  have he := congrFun (invariant_power P p.val hp k) j
  rw [Matrix.vecMul, dotProduct] at he
  rw [← he]
  exact Finset.sum_pos'
    (fun a _ => mul_nonneg (stdSimplex.zero_le p a) (hkpos a j).le)
    ⟨i, hi, mul_pos hip (hkpos i j)⟩

/-- The actual normalized Doob chain has a strictly positive invariant law;
    existence is derived from the original finite Cesaro theorem. -/
theorem exists_positive_transform_invariant [Nonempty I]
    (D : RightEigenData M) (hM : Matrix.IsPrimitive M) :
    ∃ p : stdSimplex ℝ I, (∀ i, 0 < p.val i) ∧
      Matrix.vecMul p.val (hTransform D) = p.val := by
  obtain ⟨p, hp⟩ := UEOT.V3.FiniteDobrushin.exists_invariant
    (hTransform D) (transform_stochastic D hM.nonneg)
  have he : Matrix.vecMul p.val (hTransform D) = p.val := congrArg Subtype.val hp
  exact ⟨p, invariant_positive _ (transform_primitive D hM) p he, he⟩

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PrimitivePerronDoob
