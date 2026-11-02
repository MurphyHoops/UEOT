import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PrimitivePerronSource

/-!
Promise: a finite primitive matrix has a unique positive eigenvalue and positive ray.
Existing data: actual RightEigenData is now constructed from the primitive source.
Reduced premise: positive-right uniqueness is proved, rather than input as a certificate field.
Class: every finite nonempty real primitive matrix, without symmetry or rank restrictions.
Consumer: original KPF01Certificate.positive_right_eigen_unique, with scale/ray ambiguity explicit.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PrimitivePerronUniqueness
open Matrix
open scoped BigOperators
open UEOT.V3.Compression.PositiveEigenstructure
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PrimitivePerronSource
noncomputable section
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] [Nonempty I]

omit [DecidableEq I] [Nonempty I] in
private theorem mv_mono (M : Matrix I I ℝ) (hM : ∀i j,0≤M i j)
    {x y : I→ℝ} (hxy : x≤y) : M*ᵥx≤M*ᵥy :=by
  intro i
  exact Finset.sum_le_sum (fun j _=>mul_le_mul_of_nonneg_left (hxy j) (hM i j))

omit [Nonempty I] in
private theorem eigen_power (M : Matrix I I ℝ) (a : ℝ) (v : I→ℝ)
    (hv : M*ᵥv=a • v) (k : ℕ) : (M^k)*ᵥv=a^k • v :=by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ',←Matrix.mulVec_mulVec,ih,Matrix.mulVec_smul,hv]
    simp [pow_succ',smul_smul,mul_comm]

omit [DecidableEq I] in
/-- Even nonnegative M fixes the eigenvalue once two eigenvectors are strictly positive. -/
theorem positive_eigenvalue_eq (M : Matrix I I ℝ) (hM : ∀i j,0≤M i j)
    (D : RightEigenData M) (a : ℝ) (v : I→ℝ) (hv : ∀i,0<v i)
    (he : ∀i,(M*ᵥv) i=a*v i) : a=D.scale :=by
  obtain ⟨imin,_,hmin⟩:=Finset.exists_min_image Finset.univ
    (fun i=>v i/D.vector i) Finset.univ_nonempty
  obtain ⟨imax,_,hmax⟩:=Finset.exists_max_image Finset.univ
    (fun i=>v i/D.vector i) Finset.univ_nonempty
  have hlo : (v imin/D.vector imin) • D.vector≤v :=by
    intro i
    exact (le_div_iff₀ (D.vector_pos i)).mp (hmin i (Finset.mem_univ i))
  have hhi : v≤(v imax/D.vector imax) • D.vector :=by
    intro i
    exact (div_le_iff₀ (D.vector_pos i)).mp (hmax i (Finset.mem_univ i))
  have l:=mv_mono M hM hlo imin
  have h:=mv_mono M hM hhi imax
  rw [Matrix.mulVec_smul] at l h
  change (v imin/D.vector imin)*(M*ᵥD.vector) imin≤(M*ᵥv) imin at l
  change (M*ᵥv) imax≤(v imax/D.vector imax)*(M*ᵥD.vector) imax at h
  rw [he,show (M*ᵥD.vector) imin=D.scale*D.vector imin from D.eigen imin] at l
  rw [he,show (M*ᵥD.vector) imax=D.scale*D.vector imax from D.eigen imax] at h
  have el : v imin/D.vector imin*D.vector imin=v imin:=div_mul_cancel₀ _ (D.vector_pos imin).ne'
  have eh : v imax/D.vector imax*D.vector imax=v imax:=div_mul_cancel₀ _ (D.vector_pos imax).ne'
  have l' : D.scale*v imin≤a*v imin :=by
    calc
      _=v imin/D.vector imin*(D.scale*D.vector imin) :=by calc
        _=D.scale*(v imin/D.vector imin*D.vector imin):=by rw [el]
        _=_:=by ring
      _≤_:=l
  have h' : a*v imax≤D.scale*v imax :=by
    calc
      _≤v imax/D.vector imax*(D.scale*D.vector imax):=h
      _=D.scale*v imax :=by calc
        _=D.scale*(v imax/D.vector imax*D.vector imax):=by ring
        _=D.scale*v imax:=by rw [eh]
  exact le_antisymm (le_of_mul_le_mul_right h' (hv imax)) (le_of_mul_le_mul_right l' (hv imin))

/-- Primitive positivity forces any positive eigenvector onto the actual Perron ray. -/
theorem positive_eigenvector_ray (M : Matrix I I ℝ) (hM : M.IsPrimitive)
    (D : RightEigenData M) (a : ℝ) (v : I→ℝ) (hv : ∀i,0<v i)
    (he : ∀i,(M*ᵥv) i=a*v i) :
    a=D.scale ∧ ∃c : ℝ,0<c ∧ v=c • D.vector :=by
  have ha:=positive_eigenvalue_eq M hM.nonneg D a v hv he
  obtain ⟨j,_,hmax⟩:=Finset.exists_max_image Finset.univ
    (fun i=>v i/D.vector i) Finset.univ_nonempty
  let c : ℝ:=v j/D.vector j
  have hc : 0<c:=div_pos (hv j) (D.vector_pos j)
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
    have hv' : M*ᵥv=D.scale • v:=funext (fun i=>by simpa [ha] using he i)
    rw [hD,hv']
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
  refine ⟨ha,c,hc,?_⟩
  funext i
  have hh:=congrFun hdz i
  change c*D.vector i-v i=0 at hh
  change v i=c*D.vector i
  linarith

/-- Uniqueness for the data actually derived from ANY primitive matrix. -/
theorem primitive_positive_right_unique (M : Matrix I I ℝ) (hM : M.IsPrimitive)
    (a : ℝ) (v : I→ℝ) (hv : ∀i,0<v i) (he : ∀i,(M*ᵥv) i=a*v i) :
    a=(rightEigenDataOfPrimitive M hM).scale ∧
    ∃c : ℝ,0<c ∧ v=c • (rightEigenDataOfPrimitive M hM).vector :=
  positive_eigenvector_ray M hM (rightEigenDataOfPrimitive M hM) a v hv he

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PrimitivePerronUniqueness
