import UEOT.V3.Compression.PositiveEigenstructure
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
Original promise: K-PF-01 starts from ANY finite primitive nonnegative matrix.
Existing interface: PositiveEigenstructure.RightEigenData records a positive root/vector, but does not supply their existence.
Reduced premise: construct that existing data from Matrix.IsPrimitive, using compact maximal feasible growth and a strictly positive power.
Family: arbitrary finite nonempty index type and real primitive matrix; no symmetry, rank or stochastic-row assumption.
Consumer: the actual same-matrix Doob transform and the remaining general KPF01Certificate construction.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PrimitivePerronSource

open Set Matrix
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] [Nonempty I]

private def feasible (M : Matrix I I ℝ) (a : ℝ) (x : I→ℝ) : Prop :=
  x∈stdSimplex ℝ I ∧ ∀ i,a*x i≤(M*ᵥx) i

omit [DecidableEq I] [Nonempty I] in
private theorem mv_nonneg (M : Matrix I I ℝ) (hM : ∀i j,0≤M i j)
    (x : I→ℝ) (hx : ∀i,0≤x i) : ∀i,0≤(M*ᵥx) i :=by
  intro i
  exact Finset.sum_nonneg (fun j _=>mul_nonneg (hM i j) (hx j))

omit [DecidableEq I] [Nonempty I] in
private theorem mv_mono (M : Matrix I I ℝ) (hM : ∀i j,0≤M i j)
    {x y : I→ℝ} (hxy : x≤y) : M*ᵥx≤M*ᵥy :=by
  intro i
  exact Finset.sum_le_sum (fun j _=>mul_le_mul_of_nonneg_left (hxy j) (hM i j))

omit [DecidableEq I] [Nonempty I] in
private theorem positive_mv (B : Matrix I I ℝ) (hB : ∀i j,0<B i j)
    (x : I→ℝ) (hx : ∀i,0≤x i) (hpos : ∃j,0<x j) : ∀i,0<(B*ᵥx) i :=by
  obtain ⟨j,hj⟩:=hpos
  intro i
  exact Finset.sum_pos' (fun k _=>mul_nonneg (hB i k).le (hx k))
    ⟨j,Finset.mem_univ j,mul_pos (hB i j) hj⟩

omit [DecidableEq I] [Nonempty I] in
private theorem simplex_positive_coordinate (x : I→ℝ) (hx : x∈stdSimplex ℝ I) :
    ∃j,0<x j :=by
  by_contra hh
  push Not at hh
  have hz : x=0:=funext (fun j=>le_antisymm (hh j) (hx.1 j))
  have hs:=hx.2
  rw [hz] at hs
  simp at hs

private def normalize (x : I→ℝ) : I→ℝ:=fun i=>x i/(∑j,x j)

omit [DecidableEq I] [Nonempty I] in
private theorem normalize_mem (x : I→ℝ) (hx : ∀i,0≤x i) (hs : 0<∑j,x j) :
    normalize x∈stdSimplex ℝ I :=by
  refine ⟨fun i=>div_nonneg (hx i) hs.le,?_⟩
  unfold normalize
  rw [←Finset.sum_div,div_self hs.ne']

omit [DecidableEq I] [Nonempty I] in
private theorem normalize_subsolution (M : Matrix I I ℝ) (a : ℝ) (x : I→ℝ)
    (hs : 0<∑j,x j) (hx : ∀i,a*x i≤(M*ᵥx) i) :
    ∀i,a*normalize x i≤(M*ᵥnormalize x) i :=by
  have he : normalize x=((∑j,x j)⁻¹) • x :=by
    funext i
    simp [normalize,div_eq_mul_inv,mul_comm]
  rw [he,Matrix.mulVec_smul]
  intro i
  change a*((∑j,x j)⁻¹*x i)≤(∑j,x j)⁻¹*(M*ᵥx) i
  calc
    _=(∑j,x j)⁻¹*(a*x i) :=by ring
    _≤_:=mul_le_mul_of_nonneg_left (hx i) (inv_nonneg.mpr hs.le)

private def total (M : Matrix I I ℝ) : ℝ:=∑i,∑j,M i j

omit [DecidableEq I] [Nonempty I] in
private theorem feasible_bound (M : Matrix I I ℝ) (hM : ∀i j,0≤M i j)
    (a : ℝ) (x : I→ℝ) (hx : feasible M a x) : a≤total M :=by
  calc
    a=∑i,a*x i :=by rw [←Finset.mul_sum,hx.1.2,mul_one]
    _≤∑i,(M*ᵥx) i :=Finset.sum_le_sum (fun i _=>hx.2 i)
    _≤total M :=by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_of_le_one_right (hM i j) (mem_Icc_of_mem_stdSimplex hx.1 j).2

/-- Compactness produces maximal feasible growth; no eigen equation is assumed. -/
private theorem maximal_feasible (M : Matrix I I ℝ) (hM : ∀i j,0≤M i j) :
    ∃a : ℝ,∃x : I→ℝ,0≤a ∧ feasible M a x ∧
      ∀b : ℝ,∀y : I→ℝ,0≤b→feasible M b y→b≤a :=by
  let S : Set (ℝ×(I→ℝ)) :=
    (Icc 0 (total M) ×ˢ stdSimplex ℝ I) ∩
      ⋂i,{p : ℝ×(I→ℝ) | p.1*p.2 i≤(M*ᵥp.2) i}
  have hclosed : IsClosed (⋂i,{p : ℝ×(I→ℝ) | p.1*p.2 i≤(M*ᵥp.2) i}) :=by
    apply isClosed_iInter
    intro i
    apply isClosed_le
    · fun_prop
    · change Continuous (fun p : ℝ×(I→ℝ)=>∑j,M i j*p.2 j)
      fun_prop
  have hcompact : IsCompact S :=
    (isCompact_Icc.prod (isCompact_stdSimplex ℝ I)).inter_right hclosed
  have htotal : 0≤total M:=Finset.sum_nonneg (fun i _=>Finset.sum_nonneg (fun j _=>hM i j))
  let j : I:=Classical.choice (inferInstance : Nonempty I)
  let x0 : I→ℝ:=Pi.single j 1
  have hx0 : x0∈stdSimplex ℝ I:=single_mem_stdSimplex ℝ j
  have hne : S.Nonempty :=by
    refine ⟨(0,x0),⟨⟨⟨le_rfl,htotal⟩,hx0⟩,?_⟩⟩
    simp only [mem_iInter,mem_ofPred_eq,zero_mul]
    exact mv_nonneg M hM x0 hx0.1
  obtain ⟨p,hp,hm⟩:=hcompact.exists_isMaxOn hne continuous_fst.continuousOn
  have hsub : ∀i,p.1*p.2 i≤(M*ᵥp.2) i :=by
    simpa only [mem_iInter,mem_ofPred_eq] using hp.2
  refine ⟨p.1,p.2,hp.1.1.1,⟨hp.1.2,hsub⟩,?_⟩
  intro b y hb hy
  apply (isMaxOn_iff.mp hm) (b,y)
  exact ⟨⟨⟨hb,feasible_bound M hM b y hy⟩,hy.1⟩,by simpa only [mem_iInter,mem_ofPred_eq] using hy.2⟩

omit [Nonempty I] in
private theorem power_mv_commute (M : Matrix I I ℝ) (k : ℕ) (x : I→ℝ) :
    (M^k)*ᵥ(M*ᵥx)=M*ᵥ((M^k)*ᵥx) :=by
  rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,←pow_succ,←pow_succ']

omit [Nonempty I] in
private theorem smooth_subsolution (M : Matrix I I ℝ) (hM : ∀i j,0≤M i j)
    (a : ℝ) (x : I→ℝ) (hx : ∀i,a*x i≤(M*ᵥx) i) (k : ℕ) :
    ∀i,a*((M^k)*ᵥx) i≤(M*ᵥ((M^k)*ᵥx)) i :=by
  have hh:=mv_mono (M^k) (Matrix.pow_apply_nonneg hM k) hx
  change (M^k)*ᵥ(a • x)≤(M^k)*ᵥ(M*ᵥx) at hh
  have he : (M^k)*ᵥ(a • x)=a • ((M^k)*ᵥx):=Matrix.mulVec_smul _ _ _
  rw [he,power_mv_commute] at hh
  exact hh

private theorem primitive_row_positive (M : Matrix I I ℝ) (hM : M.IsPrimitive) (i : I) :
    ∃j,0<M i j :=by
  obtain ⟨k,hk,hpos⟩:=hM.exists_pos_pow
  cases k with
  | zero => omega
  | succ k =>
    let z : I:=Classical.choice (inferInstance : Nonempty I)
    have hh:=hpos i z
    rw [pow_succ',Matrix.mul_apply] at hh
    obtain ⟨j,_,hj⟩:=(Finset.sum_pos_iff_of_nonneg
      (fun j _=>mul_nonneg (hM.nonneg i j) (Matrix.pow_apply_nonneg hM.nonneg k j z))).mp hh
    refine ⟨j,?_⟩
    by_contra hn
    have hz : M i j=0:=le_antisymm (le_of_not_gt hn) (hM.nonneg i j)
    rw [hz,zero_mul] at hj
    linarith

private theorem positive_feasible (M : Matrix I I ℝ) (hM : M.IsPrimitive) :
    ∃a : ℝ,0<a ∧ ∃x : I→ℝ,feasible M a x :=by
  have hrow (i : I) : 0<∑j,M i j :=by
    obtain ⟨j,hj⟩:=primitive_row_positive M hM i
    exact Finset.sum_pos' (fun j _=>hM.nonneg i j) ⟨j,Finset.mem_univ j,hj⟩
  obtain ⟨i,_,hmin⟩:=Finset.exists_min_image Finset.univ (fun i=>∑j,M i j) Finset.univ_nonempty
  let a : ℝ:=∑j,M i j
  have ha : 0<a:=hrow i
  let v : I→ℝ:=fun _=>1
  have hv : 0<∑j,v j :=by
    change 0<∑j : I,(1 : ℝ)
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
    exact_mod_cast (Fintype.card_pos : 0<Fintype.card I)
  refine ⟨a,ha,normalize v,normalize_mem v (fun _=>by norm_num [v]) hv,?_⟩
  apply normalize_subsolution M a v hv
  intro j
  change a*1≤∑k,M j k*1
  simp only [mul_one]
  exact hmin j (Finset.mem_univ j)

omit [DecidableEq I] in
private theorem sum_pos_of_positive (x : I→ℝ) (hx : ∀i,0<x i) : 0<∑i,x i :=by
  let i : I:=Classical.choice (inferInstance : Nonempty I)
  exact Finset.sum_pos' (fun j _=>(hx j).le) ⟨i,Finset.mem_univ i,hx i⟩

omit [DecidableEq I] [Nonempty I] in
private theorem positive_from_nonzero (x : I→ℝ) (hx : ∀i,0≤x i) (hne : x≠0) : ∃i,0<x i :=by
  by_contra hh
  push Not at hh
  exact hne (funext (fun i=>le_antisymm (hh i) (hx i)))

/-- The compact maximizer cannot have a nonzero nonnegative residual:
a primitive power makes that residual strictly positive in EVERY coordinate. -/
private theorem maximal_growth_eigen (M : Matrix I I ℝ) (hM : M.IsPrimitive) :
    ∃a : ℝ,∃r : I→ℝ,0<a ∧ (∀i,0<r i) ∧ ∀i,(M*ᵥr) i=a*r i :=by
  obtain ⟨a,x,ha,hx,hmax⟩:=maximal_feasible M hM.nonneg
  obtain ⟨b,hb,y,hy⟩:=positive_feasible M hM
  have hap : 0<a:=hb.trans_le (hmax b y hb.le hy)
  obtain ⟨k,hk,hB⟩:=hM.exists_pos_pow
  let r0 : I→ℝ:=(M^k)*ᵥx
  have hr0 : ∀i,0<r0 i:=positive_mv (M^k) hB x hx.1.1 (simplex_positive_coordinate x hx.1)
  have hs0 : 0<∑i,r0 i:=sum_pos_of_positive r0 hr0
  let r : I→ℝ:=normalize r0
  have hr : ∀i,0<r i:=fun i=>div_pos (hr0 i) hs0
  have hfr : feasible M a r:=⟨normalize_mem r0 (fun i=>(hr0 i).le) hs0,
    normalize_subsolution M a r0 hs0 (smooth_subsolution M hM.nonneg a x hx.2 k)⟩
  refine ⟨a,r,hap,hr,?_⟩
  let d : I→ℝ:=M*ᵥr-a • r
  have hd : ∀i,0≤d i:=fun i=>sub_nonneg.mpr (hfr.2 i)
  have hdz : d=0 :=by
    by_contra hn
    have hBd : ∀i,0<((M^k)*ᵥd) i:=positive_mv (M^k) hB d hd (positive_from_nonzero d hd hn)
    let z : I→ℝ:=(M^k)*ᵥr
    have hz : ∀i,0<z i:=positive_mv (M^k) hB r (fun i=>(hr i).le)
      ⟨Classical.choice (inferInstance : Nonempty I),hr _⟩
    have hres : (M^k)*ᵥd=M*ᵥz-a • z :=by
      change (M^k)*ᵥ(M*ᵥr-a • r)=M*ᵥ((M^k)*ᵥr)-a • ((M^k)*ᵥr)
      rw [Matrix.mulVec_sub,Matrix.mulVec_smul,power_mv_commute]
    obtain ⟨i,_,hmin⟩:=Finset.exists_min_image Finset.univ
      (fun j=>((M^k)*ᵥd) j/z j) Finset.univ_nonempty
    let e : ℝ:=((M^k)*ᵥd) i/z i
    have he : 0<e:=div_pos (hBd i) (hz i)
    have hraw : ∀j,(a+e)*z j≤(M*ᵥz) j :=by
      intro j
      have hez : e*z j≤((M^k)*ᵥd) j:=
        (le_div_iff₀ (hz j)).mp (hmin j (Finset.mem_univ j))
      have heq:=congrFun hres j
      change ((M^k)*ᵥd) j=(M*ᵥz) j-a*z j at heq
      nlinarith
    have hsz : 0<∑j,z j:=sum_pos_of_positive z hz
    have hnew : feasible M (a+e) (normalize z):=⟨normalize_mem z (fun j=>(hz j).le) hsz,
      normalize_subsolution M (a+e) z hsz hraw⟩
    have hcontra:=hmax (a+e) (normalize z) (by linarith) hnew
    linarith
  intro i
  have hh:=congrFun hdz i
  change (M*ᵥr) i-a*r i=0 at hh
  linarith

/-- General finite primitive Perron existence, directly in the already
existing positive-eigenstructure interface; no certificate fields are input. -/
theorem exists_positive_right_eigen_of_primitive (M : Matrix I I ℝ) (hM : M.IsPrimitive) :
    Nonempty (UEOT.V3.Compression.PositiveEigenstructure.RightEigenData M) :=by
  obtain ⟨a,r,ha,hr,he⟩:=maximal_growth_eigen M hM
  refine ⟨⟨a,r,ha,hr,?_⟩⟩
  intro i
  exact he i

def rightEigenDataOfPrimitive (M : Matrix I I ℝ) (hM : M.IsPrimitive) :
    UEOT.V3.Compression.PositiveEigenstructure.RightEigenData M :=
  Classical.choice (exists_positive_right_eigen_of_primitive M hM)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PrimitivePerronSource
