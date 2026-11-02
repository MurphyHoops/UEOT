import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PrimitivePerronBiEigen
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
Promise: the positive Perron root of any finite primitive matrix is algebraically simple.
Existing data: actual primitive positive right/left eigenstructure, not an assumed multiplicity field.
Reduced premise: generalized eigenspace equals the one-dimensional Perron ray; charpoly root multiplicity is one.
Family: arbitrary finite nonempty primitive real matrices, including non-symmetric and non-diagonalizable other spectral blocks.
Consumer: source K-PF-01's "simple root" claim, separate from positive-ray uniqueness and strict spectral dominance.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PrimitivePerronSimplicity
open Matrix
open scoped BigOperators
open UEOT.V3.Compression.PositiveEigenstructure
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
omit [Nonempty I] in
private theorem eigen_power (M : Matrix I I ℝ) (a : ℝ) (v : I→ℝ)
    (hv : M*ᵥv=a • v) (k : ℕ) : (M^k)*ᵥv=a^k • v :=by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ',←Matrix.mulVec_mulVec,ih,Matrix.mulVec_smul,hv]
    simp [pow_succ',smul_smul,mul_comm]

/-- Positivity of the CANDIDATE is not required for the Perron eigenspace:
the primitive positive power excludes every other signed direction. -/
theorem signed_eigenvector_ray (M : Matrix I I ℝ) (hM : M.IsPrimitive)
    (D : RightEigenData M) (v : I→ℝ) (he : M*ᵥv=D.scale • v) :
    ∃c : ℝ,v=c • D.vector :=by
  obtain ⟨j,_,hmax⟩:=Finset.exists_max_image Finset.univ
    (fun i=>v i/D.vector i) Finset.univ_nonempty
  let c : ℝ:=v j/D.vector j
  let d : I→ℝ:=c • D.vector-v
  have hd : ∀i,0≤d i :=by
    intro i
    exact sub_nonneg.mpr ((div_le_iff₀ (D.vector_pos i)).mp (hmax i (Finset.mem_univ i)))
  have hdj : d j=0 :=by
    change v j/D.vector j*D.vector j-v j=0
    rw [div_mul_cancel₀ _ (D.vector_pos j).ne',sub_self]
  have hde : M*ᵥd=D.scale • d :=by
    rw [show d=c • D.vector-v from rfl,Matrix.mulVec_sub,Matrix.mulVec_smul]
    have hD : M*ᵥD.vector=D.scale • D.vector:=funext D.eigen
    rw [hD,he]
    funext i
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    ring
  have hdz : d=0 :=by
    by_contra hn
    have hp : ∃i,0<d i :=by
      by_contra hh
      push Not at hh
      exact hn (funext (fun i=>le_antisymm (hh i) (hd i)))
    obtain ⟨i,hi⟩:=hp
    obtain ⟨k,hk,hB⟩:=hM.exists_pos_pow
    have hpos : 0<((M^k)*ᵥd) j:=Finset.sum_pos'
      (fun l _=>mul_nonneg (hB j l).le (hd l))
      ⟨i,Finset.mem_univ i,mul_pos (hB j i) hi⟩
    rw [eigen_power M D.scale d hde k] at hpos
    change 0<D.scale^k*d j at hpos
    rw [hdj,mul_zero] at hpos
    exact (lt_irrefl 0) hpos
  refine ⟨c,?_⟩
  funext i
  have hh:=congrFun hdz i
  change c*D.vector i-v i=0 at hh
  change v i=c*D.vector i
  linarith

private def perronShift (M : Matrix I I ℝ) (B : BiEigenData M) : Module.End ℝ (I→ℝ):=
  M.toLin'-B.right.scale • 1
omit [Nonempty I] in
private theorem shift_apply (M : Matrix I I ℝ) (B : BiEigenData M) (v : I→ℝ) :
    perronShift M B v=M*ᵥv-B.right.scale • v:=by
  simp [perronShift,Matrix.toLin'_apply]
omit [Nonempty I] in
private theorem pair_shift_zero (M : Matrix I I ℝ) (B : BiEigenData M) (v : I→ℝ) :
    B.left ⬝ᵥ perronShift M B v=0:=by
  rw [shift_apply,dotProduct_sub,Matrix.dotProduct_mulVec,dotProduct_smul]
  have hl : Matrix.vecMul B.left M=B.right.scale • B.left:=funext B.left_eigen
  rw [hl,smul_dotProduct,sub_self]
omit [Nonempty I] in
private theorem shift_eq_zero_iff (M : Matrix I I ℝ) (B : BiEigenData M) (v : I→ℝ) :
    perronShift M B v=0 ↔ M*ᵥv=B.right.scale • v:=by
  rw [shift_apply,sub_eq_zero]

private theorem shift_kernel_two (M : Matrix I I ℝ) (hM : M.IsPrimitive)
    (B : BiEigenData M) (v : I→ℝ) (hv : perronShift M B (perronShift M B v)=0) :
    perronShift M B v=0 :=by
  obtain ⟨c,hc⟩:=signed_eigenvector_ray M hM B.right (perronShift M B v)
    ((shift_eq_zero_iff M B _).mp hv)
  have hpair:=pair_shift_zero M B v
  rw [hc,dotProduct_smul] at hpair
  have hp : B.left ⬝ᵥ B.right.vector=1:=B.pairing_sum_one
  rw [hp,smul_eq_mul,mul_one] at hpair
  rw [hc,hpair,zero_smul]

private theorem shift_power_kernel (M : Matrix I I ℝ) (hM : M.IsPrimitive)
    (B : BiEigenData M) (n : ℕ) (v : I→ℝ) (hv : ((perronShift M B)^n) v=0) :
    perronShift M B v=0 :=by
  induction n generalizing v with
  | zero =>
    simp only [pow_zero,Module.End.one_apply] at hv
    rw [hv,map_zero]
  | succ n ih =>
    have hpow : ((perronShift M B)^n) (perronShift M B v)=0:=by
      rw [←Module.End.mul_apply,←pow_succ]
      exact hv
    exact shift_kernel_two M hM B v (ih _ hpow)

/-- All generalized Perron eigenvectors are already eigenvectors: the left
pairing excludes a Jordan predecessor, rather than merely counting eigenvectors. -/
theorem maximal_generalized_eq_eigenspace (M : Matrix I I ℝ) (hM : M.IsPrimitive)
    (B : BiEigenData M) : Module.End.maxGenEigenspace M.toLin' B.right.scale=
      Module.End.eigenspace M.toLin' B.right.scale :=by
  apply le_antisymm
  · intro v hv
    obtain ⟨n,hn⟩:=(Module.End.mem_maxGenEigenspace _ _ _).mp hv
    apply Module.End.mem_eigenspace_iff.mpr
    exact (shift_eq_zero_iff M B v).mp (shift_power_kernel M hM B n v hn)
  · exact Module.End.eigenspace_le_maxGenEigenspace

/-- The full signed eigenspace is exactly the literal one-vector span. -/
theorem eigenspace_eq_span (M : Matrix I I ℝ) (hM : M.IsPrimitive)
    (D : RightEigenData M) : Module.End.eigenspace M.toLin' D.scale=ℝ ∙ D.vector :=by
  ext v
  constructor
  · intro hv
    obtain ⟨c,hc⟩:=signed_eigenvector_ray M hM D v
      (by simpa only [Matrix.toLin'_apply] using Module.End.mem_eigenspace_iff.mp hv)
    exact Submodule.mem_span_singleton.mpr ⟨c,hc.symm⟩
  · intro hv
    obtain ⟨c,rfl⟩:=Submodule.mem_span_singleton.mp hv
    apply Module.End.mem_eigenspace_iff.mpr
    rw [map_smul]
    have he : M.toLin' D.vector=D.scale • D.vector:=funext D.eigen
    rw [he]
    simp [smul_smul,mul_comm]

/-- Algebraic multiplicity in the ORIGINAL real matrix characteristic
polynomial is one; this conclusion is stronger than geometric ray uniqueness. -/
theorem perron_root_algebraically_simple (M : Matrix I I ℝ) (hM : M.IsPrimitive)
    (B : BiEigenData M) : M.charpoly.rootMultiplicity B.right.scale=1 :=by
  have hr : B.right.vector≠0 :=by
    intro hz
    let i : I:=Classical.choice (inferInstance : Nonempty I)
    have hh:=B.right.vector_pos i
    rw [hz] at hh
    simp at hh
  rw [←Matrix.charpoly_toLin',←LinearMap.finrank_maxGenEigenspace_eq,
    maximal_generalized_eq_eigenspace M hM B,eigenspace_eq_span M hM B.right]
  exact finrank_span_singleton hr

/-- The SAME real root has algebraic multiplicity one after the literal
complex scalar extension of the SAME matrix. -/
theorem perron_complex_root_algebraically_simple (M : Matrix I I ℝ) (hM : M.IsPrimitive)
    (B : BiEigenData M) :
    (M.map Complex.ofRealHom).charpoly.rootMultiplicity (B.right.scale : ℂ)=1 :=by
  rw [Matrix.charpoly_map]
  have hh:=Polynomial.eq_rootMultiplicity_map (p:=M.charpoly) (f:=Complex.ofRealHom)
    Complex.ofReal_injective B.right.scale
  exact hh.symm.trans (perron_root_algebraically_simple M hM B)


/-- Primitive-only source theorem: the right and left data are actually
constructed from this matrix, and algebraic simplicity is proved. -/
theorem actual_perron_root_algebraically_simple (M : Matrix I I ℝ) (hM : M.IsPrimitive) :
    M.charpoly.rootMultiplicity
      (PrimitivePerronBiEigen.biEigenDataOfPrimitive M hM).right.scale=1 :=
  perron_root_algebraically_simple M hM (PrimitivePerronBiEigen.biEigenDataOfPrimitive M hM)

/-- Primitive-only source theorem for the SAME matrix after complex extension. -/
theorem actual_complex_perron_root_algebraically_simple (M : Matrix I I ℝ) (hM : M.IsPrimitive) :
    (M.map Complex.ofRealHom).charpoly.rootMultiplicity
      ((PrimitivePerronBiEigen.biEigenDataOfPrimitive M hM).right.scale : ℂ)=1 :=
  perron_complex_root_algebraically_simple M hM (PrimitivePerronBiEigen.biEigenDataOfPrimitive M hM)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PrimitivePerronSimplicity
