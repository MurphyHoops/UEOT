import UEOT.V3.FiniteRecurrentDecompositionStability
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Topology.Order.MonotoneConvergence

/-!
Promise: every finite primitive stochastic kernel has strictly positive attracting stationary law.
Existing theorems: actual Cesaro invariant existence and canonical event-TV Dobrushin contraction.
Reduced premise: no mixing or positivity of an invariant law is assumed.
Family: any finite nonempty state space and actual primitive row-stochastic real matrix, including kernels with zero one-step entries.
Consumer: same-matrix primitive Doob powers and the general K-PF-01 normalized-power limit.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PrimitiveMarkovMixing
open Matrix Filter Topology
open scoped BigOperators
open UEOT.V3.FiniteDobrushin
open UEOT.V3.FiniteCesaroInvariant
open UEOT.V3.FiniteRecurrentDecompositionStability
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

private def rowLaw (P : Matrix I I ℝ) (hP : P∈Matrix.rowStochastic ℝ I) (i : I) :
    stdSimplex ℝ I :=⟨P i,fun _=>Matrix.nonneg_of_mem_rowStochastic hP,
      Matrix.sum_row_of_mem_rowStochastic hP i⟩
omit [Nonempty I] in
private theorem rowTV_law (P : Matrix I I ℝ) (hP : P∈Matrix.rowStochastic ℝ I) (i j : I) :
    rowTV P hP i j=lawTV (rowLaw P hP i) (rowLaw P hP j) :=rfl

omit [DecidableEq I] [Nonempty I] in
private theorem lawTV_le_one (x y : stdSimplex ℝ I) : lawTV x y≤1 :=by
  rw [lawTV_eq_half_sum_abs]
  have hs : (∑i,|x.1 i-y.1 i|)≤2 :=by
    calc
      _≤∑i,(x.1 i+y.1 i):=Finset.sum_le_sum (fun i _=>by
        rw [abs_le]; constructor <;> linarith [x.2.1 i,y.2.1 i])
      _=2:=by rw [Finset.sum_add_distrib,x.2.2,y.2.2]; norm_num
  linarith

private theorem rowTV_lt_one (P : Matrix I I ℝ) (hP : P∈Matrix.rowStochastic ℝ I)
    (hpos : ∀i j,0<P i j) (i j : I) : rowTV P hP i j<1 :=by
  rw [rowTV_law,lawTV_eq_half_sum_abs]
  have hs : (∑l,|P i l-P j l|)<∑l,(P i l+P j l) :=by
    apply Finset.sum_lt_sum
    · intro l _
      exact (abs_lt.mpr ⟨by linarith [hpos i l,hpos j l],by linarith [hpos i l,hpos j l]⟩).le
    · let l : I:=Classical.choice (inferInstance : Nonempty I)
      exact ⟨l,Finset.mem_univ l,abs_lt.mpr ⟨by linarith [hpos i l,hpos j l],by linarith [hpos i l,hpos j l]⟩⟩
  have hr : (∑l,(P i l+P j l))=2:=by
    rw [Finset.sum_add_distrib,Matrix.sum_row_of_mem_rowStochastic hP i,
      Matrix.sum_row_of_mem_rowStochastic hP j]; norm_num
  change (1/2 : ℝ)*(∑l,|P i l-P j l|)<1
  linarith

private theorem alpha_bounds (P : Matrix I I ℝ) (hP : P∈Matrix.rowStochastic ℝ I) :
    0≤dobrushinAlpha P hP ∧ dobrushinAlpha P hP≤1 :=by
  constructor
  · let i : I:=Classical.choice (inferInstance : Nonempty I)
    exact (lawTV_nonneg (rowLaw P hP i) (rowLaw P hP i)).trans
      (rowTV_le_dobrushinAlpha P hP i i)
  · apply Finset.sup'_le
    intro z _
    rw [rowTV_law]
    exact lawTV_le_one _ _

private theorem alpha_lt_one_of_positive (P : Matrix I I ℝ) (hP : P∈Matrix.rowStochastic ℝ I)
    (hpos : ∀i j,0<P i j) : dobrushinAlpha P hP<1 :=by
  apply (Finset.sup'_lt_iff _).mpr
  intro z _
  exact rowTV_lt_one P hP hpos z.1 z.2

omit [Nonempty I] in
private theorem invariant_power (P : Matrix I I ℝ) (x : I→ℝ) (hx : Matrix.vecMul x P=x)
    (k : ℕ) : Matrix.vecMul x (P^k)=x :=by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ,←Matrix.vecMul_vecMul,ih,hx]

omit [Nonempty I] in
private theorem orbit_step (P : Matrix I I ℝ) (hP : P∈Matrix.rowStochastic ℝ I)
    (x : stdSimplex ℝ I) (n : ℕ) : orbit P hP x (n+1)=step P hP (orbit P hP x n) :=by
  apply Subtype.ext
  exact orbit_succ P hP x n

private theorem orbit_tv_antitone (P : Matrix I I ℝ) (hP : P∈Matrix.rowStochastic ℝ I)
    (x mu : stdSimplex ℝ I) (hmu : step P hP mu=mu) :
    Antitone (fun n=>lawTV (orbit P hP x n) mu) :=by
  apply antitone_nat_of_succ_le
  intro n
  rw [orbit_step]
  calc
    _=lawTV (step P hP (orbit P hP x n)) (step P hP mu):=by rw [hmu]
    _≤dobrushinAlpha P hP*lawTV (orbit P hP x n) mu:=tv_step_le_dobrushin P hP _ _
    _≤_:=mul_le_of_le_one_left (lawTV_nonneg _ _) (alpha_bounds P hP).2

private theorem orbit_geometric (P : Matrix I I ℝ) (hP : P∈Matrix.rowStochastic ℝ I)
    (x mu : stdSimplex ℝ I) (hmu : step P hP mu=mu) (n : ℕ) :
    lawTV (orbit P hP x n) mu≤(dobrushinAlpha P hP)^n*lawTV x mu :=by
  induction n with
  | zero =>
    have hz : orbit P hP x 0=x:=Subtype.ext (orbit_zero P hP x)
    simp [hz]
  | succ n ih =>
    rw [orbit_step]
    calc
      _=lawTV (step P hP (orbit P hP x n)) (step P hP mu):=by rw [hmu]
      _≤dobrushinAlpha P hP*lawTV (orbit P hP x n) mu:=
        tv_step_le_dobrushin P hP _ _
      _≤dobrushinAlpha P hP*((dobrushinAlpha P hP)^n*lawTV x mu):=
        mul_le_mul_of_nonneg_left ih (alpha_bounds P hP).1
      _=_:=by rw [pow_succ]; ring

omit [Nonempty I] in
/-- Primitive powers force every coordinate of any actual invariant row to be positive. -/
theorem invariant_positive (P : Matrix I I ℝ) (hprim : P.IsPrimitive)
    (mu : stdSimplex ℝ I) (hmu : Matrix.vecMul mu.1 P=mu.1) : ∀j,0<mu.1 j :=by
  have hex : ∃i,0<mu.1 i :=by
    by_contra hh
    push Not at hh
    have hz : mu.1=0:=funext (fun i=>le_antisymm (hh i) (mu.2.1 i))
    have hs:=stdSimplex.sum_eq_one mu
    change (∑i,mu.1 i)=1 at hs
    rw [hz] at hs
    simp at hs
  obtain ⟨i,hi⟩:=hex
  obtain ⟨k,hk,hpos⟩:=hprim.exists_pos_pow
  intro j
  have hh : 0<Matrix.vecMul mu.1 (P^k) j :=Finset.sum_pos'
    (fun l _=>mul_nonneg (mu.2.1 l) (hpos l j).le)
    ⟨i,Finset.mem_univ i,mul_pos hi (hpos i j)⟩
  rw [invariant_power P mu.1 hmu k] at hh
  exact hh

/-- ANY primitive finite stochastic kernel has an actual positive stationary
row, and ALL original matrix-power coordinates converge to that same row. -/
theorem primitive_power_convergence (P : Matrix I I ℝ)
    (hP : P∈Matrix.rowStochastic ℝ I) (hprim : P.IsPrimitive) :
    ∃mu : stdSimplex ℝ I,(∀j,0<mu.1 j) ∧ Matrix.vecMul mu.1 P=mu.1 ∧
      ∀i j,Tendsto (fun n : ℕ=>(P^n) i j) atTop (𝓝 (mu.1 j)) :=by
  obtain ⟨mu,hmu⟩:=exists_invariant P hP
  have hmuval : Matrix.vecMul mu.1 P=mu.1:=congrArg Subtype.val hmu
  refine ⟨mu,invariant_positive P hprim mu hmuval,hmuval,?_⟩
  obtain ⟨k,hk,hpos⟩:=hprim.exists_pos_pow
  let Q : Matrix I I ℝ:=P^k
  have hQ : Q∈Matrix.rowStochastic ℝ I:=(Matrix.rowStochastic ℝ I).pow_mem hP k
  have hmuQ : step Q hQ mu=mu:=Subtype.ext (invariant_power P mu.1 hmuval k)
  have hα0 : 0≤dobrushinAlpha Q hQ:=(alpha_bounds Q hQ).1
  have hα1 : dobrushinAlpha Q hQ<1:=alpha_lt_one_of_positive Q hQ hpos
  intro i j
  let x : stdSimplex ℝ I:=pureSimplex i
  have hsub : Tendsto (fun n : ℕ=>lawTV (orbit P hP x (n*k)) mu) atTop (𝓝 0) :=by
    have heq (n : ℕ) : orbit P hP x (n*k)=orbit Q hQ x n :=by
      apply Subtype.ext
      change Matrix.vecMul x.1 (P^(n*k))=Matrix.vecMul x.1 ((P^k)^n)
      rw [←pow_mul,Nat.mul_comm]
    simp_rw [heq]
    apply squeeze_zero (fun _=>lawTV_nonneg _ _) (orbit_geometric Q hQ x mu hmuQ)
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hα0 hα1).mul_const (lawTV x mu)
  have hkn : Tendsto (fun n : ℕ=>n*k) atTop atTop :=by
    apply tendsto_atTop_mono _ tendsto_id
    intro n
    calc
      n=n*1:=by omega
      _≤n*k:=Nat.mul_le_mul_left n hk
  have hfull : Tendsto (fun n : ℕ=>lawTV (orbit P hP x n) mu) atTop (𝓝 0) :=
    (tendsto_iff_tendsto_subseq_of_antitone (orbit_tv_antitone P hP x mu hmu) hkn).mpr hsub
  have hbound (n : ℕ) : |(orbit P hP x n).1 j-mu.1 j|≤2*lawTV (orbit P hP x n) mu :=by
    rw [lawTV_eq_half_sum_abs]
    have hh:=Finset.single_le_sum (fun l (_ : l∈Finset.univ)=>abs_nonneg ((orbit P hP x n).1 l-mu.1 l))
      (Finset.mem_univ j)
    linarith
  have hcoord : Tendsto (fun n : ℕ=>|(orbit P hP x n).1 j-mu.1 j|) atTop (𝓝 0):=
    squeeze_zero (fun _=>abs_nonneg _) hbound (by simpa using hfull.const_mul 2)
  have hr (n : ℕ) : (orbit P hP x n).1 j=(P^n) i j :=by
    dsimp [orbit,x,pureSimplex]
    simp [Matrix.single_vecMul]
  simp_rw [hr] at hcoord
  exact (tendsto_iff_norm_sub_tendsto_zero).mpr (by simpa only [Real.norm_eq_abs] using hcoord)

/-- A primitive kernel's actual invariant row is unique, even when its
one-step Dobrushin coefficient equals one. -/
theorem primitive_invariant_unique (P : Matrix I I ℝ)
    (hP : P∈Matrix.rowStochastic ℝ I) (hprim : P.IsPrimitive)
    (mu nu : stdSimplex ℝ I) (hmu : Matrix.vecMul mu.1 P=mu.1)
    (hnu : Matrix.vecMul nu.1 P=nu.1) : mu=nu :=by
  obtain ⟨k,hk,hpos⟩:=hprim.exists_pos_pow
  have hPk : P^k∈Matrix.rowStochastic ℝ I:=(Matrix.rowStochastic ℝ I).pow_mem hP k
  apply invariant_eq_of_dobrushin_lt_one (P^k) hPk
    (alpha_lt_one_of_positive (P^k) hPk hpos) mu nu
  · exact Subtype.ext (invariant_power P mu.1 hmu k)
  · exact Subtype.ext (invariant_power P nu.1 hnu k)

/-- The full power limit is bound to ANY given actual invariant row, so an
independently constructed Cesaro/Doob invariant is not silently replaced. -/
theorem primitive_power_tendsto_invariant (P : Matrix I I ℝ)
    (hP : P∈Matrix.rowStochastic ℝ I) (hprim : P.IsPrimitive)
    (mu : stdSimplex ℝ I) (hmu : Matrix.vecMul mu.1 P=mu.1) :
    ∀i j,Tendsto (fun n : ℕ=>(P^n) i j) atTop (𝓝 (mu.1 j)) :=by
  obtain ⟨nu,hpos,hnu,hlim⟩:=primitive_power_convergence P hP hprim
  have he:=primitive_invariant_unique P hP hprim nu mu hnu hmu
  subst nu
  exact hlim

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PrimitiveMarkovMixing
