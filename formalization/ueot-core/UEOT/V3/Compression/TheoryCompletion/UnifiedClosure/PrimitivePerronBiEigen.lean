import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PrimitivePerronSource
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PrimitivePerronDoob

/-! The left Perron data are derived from the actual Doob invariant law.
Both normalizations are constructed, rather than assumed as certificate fields.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PrimitivePerronBiEigen
noncomputable section
open scoped BigOperators
open UEOT.V3.Compression.PositiveEigenstructure
open PrimitivePerronSource PrimitivePerronDoob
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] {M : Matrix I I ℝ}

omit [DecidableEq I] [Nonempty I] in
/-- A genuine invariant law of the actual Doob transform supplies the left
    eigenrelation of the same original matrix. -/
theorem raw_left_eigen (D : RightEigenData M) (p : I → ℝ)
    (hp : Matrix.vecMul p (hTransform D) = p) (j : I) :
    (∑ i, (p i / D.vector i) * M i j) = D.scale * (p j / D.vector j) := by
  have hR := D.scale_pos.ne'
  have hv : ∀ i, D.vector i ≠ 0 := fun i => (D.vector_pos i).ne'
  have he : (∑ i, (p i / D.vector i) * M i j) * D.vector j / D.scale = p j := by
    calc
      _ = ∑ i, p i * hTransform D i j := by
        rw [Finset.sum_mul, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i hi
        unfold hTransform
        field_simp [hR, hv]
      _ = p j := congrFun hp j
  calc
    _ = ((∑ i, (p i / D.vector i) * M i j) * D.vector j / D.scale) *
          (D.scale / D.vector j) := by field_simp [hR, hv]
    _ = p j * (D.scale / D.vector j) := by rw [he]
    _ = _ := by ring

/-- Full normalized positive left/right data from primitivity. -/
theorem exists_positive_bieigen (D : RightEigenData M) (hM : Matrix.IsPrimitive M) :
    ∃ B : BiEigenData M, ∀ i, 0 < B.left i := by
  obtain ⟨p, hpos, hp⟩ := exists_positive_transform_invariant D hM
  let raw : I → ℝ := fun i => p.val i / D.vector i
  let c : ℝ := ∑ i, raw i
  have hraw : ∀ i, 0 < raw i := fun i => div_pos (hpos i) (D.vector_pos i)
  have hc : 0 < c := Finset.sum_pos (fun i _ => hraw i) Finset.univ_nonempty
  have hc0 : c ≠ 0 := hc.ne'
  have hv : ∀ i, D.vector i ≠ 0 := fun i => (D.vector_pos i).ne'
  let Dr : RightEigenData M :=
    { scale := D.scale
      vector := fun i => D.vector i * c
      scale_pos := D.scale_pos
      vector_pos := fun i => mul_pos (D.vector_pos i) hc
      eigen := by
        intro i
        change (∑ j, M i j * (D.vector j * c)) = D.scale * (D.vector i * c)
        calc
          _ = (∑ j, M i j * D.vector j) * c := by simp_rw [← mul_assoc]; rw [Finset.sum_mul]
          _ = _ := by rw [show (∑ j, M i j * D.vector j) = D.scale * D.vector i from D.eigen i]; ring }
  let B : BiEigenData M :=
    { right := Dr
      left := fun i => raw i / c
      matrix_nonneg := hM.nonneg
      left_nonneg := fun i => (div_pos (hraw i) hc).le
      left_sum_one := by rw [← Finset.sum_div]; exact div_self hc0
      pairing_sum_one := by
        change (∑ i, (raw i / c) * (D.vector i * c)) = 1
        calc
          _ = ∑ i, p.val i := by
            apply Finset.sum_congr rfl
            intro i hi
            dsimp [raw]
            field_simp [hc0, hv]
          _ = 1 := stdSimplex.sum_eq_one p
      left_eigen := by
        intro j
        change (∑ i, (raw i / c) * M i j) = D.scale * (raw j / c)
        calc
          _ = (∑ i, raw i * M i j) / c := by simp_rw [div_mul_eq_mul_div]; rw [Finset.sum_div]
          _ = D.scale * (raw j / c) := by rw [raw_left_eigen D p.val hp j]; ring }
  exact ⟨B, fun i => div_pos (hraw i) hc⟩

/-- This choice consumes the proved original primitive-source construction. -/
noncomputable def biEigenDataOfPrimitive (M : Matrix I I ℝ) (hM : Matrix.IsPrimitive M) :
    BiEigenData M := (exists_positive_bieigen (rightEigenDataOfPrimitive M hM) hM).choose

theorem actual_left_pos (M : Matrix I I ℝ) (hM : Matrix.IsPrimitive M) (i : I) :
    0 < (biEigenDataOfPrimitive M hM).left i :=
  (exists_positive_bieigen (rightEigenDataOfPrimitive M hM) hM).choose_spec i

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PrimitivePerronBiEigen
