import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PrimitivePerronSource
import Mathlib.Analysis.SpecificLimits.Normed
/-!
Original promise: strict complex spectral dominance for the actual primitive Perron source.
Existing dependency: actual normalized matrix power convergence is a separate required source theorem.
This intermediate lemma removes spectral dominance as an independent premise once that limit is supplied.
Class: any finite real matrix, any positive scaling with convergent normalized powers; no symmetry or rank restriction.
Consumer: the final primitive KPF01Certificate assembly MUST derive its power limit, rather than input this dependency as a new field.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PrimitivePerronSpectral
open Matrix Filter Topology
open scoped BigOperators
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
private theorem cast_pow (M : Matrix I I ℝ) (n : ℕ) :
    (M.map Complex.ofRealHom)^n=(M^n).map Complex.ofRealHom :=by
  induction n with
  | zero => simp [Matrix.map_one]
  | succ n ih => rw [pow_succ,ih,←Matrix.map_mul,←pow_succ]
private theorem eigen_power (C : Matrix I I ℂ) (a : ℂ) (v : I→ℂ)
    (hv : C*ᵥv=a • v) (n : ℕ) : (C^n)*ᵥv=a^n • v :=by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',←Matrix.mulVec_mulVec,ih,Matrix.mulVec_smul,hv]
    simp [pow_succ',smul_smul,mul_comm]
theorem strict_of_power_limit (M : Matrix I I ℝ) (R : ℝ) (hR : 0<R)
    (L : Matrix I I ℝ)
    (hlim : ∀i j,Tendsto (fun n : ℕ=>(R^n)⁻¹*(M^n) i j) atTop (𝓝 (L i j)))
    (a : ℂ) (v : I→ℂ) (hv : v≠0)
    (he : ∀i,∑j,(M i j : ℂ)*v j=a*v i) (ha : a≠(R : ℂ)) : ‖a‖<R :=by
  have hex : ∃i,v i≠0 :=by
    by_contra hh
    push Not at hh
    exact hv (funext hh)
  obtain ⟨i,hi⟩:=hex
  let q : ℂ:=a/(R : ℂ)
  let z : ℂ:=(∑j,(L i j : ℂ)*v j)/v i
  have hRc : (R : ℂ)≠0:=Complex.ofReal_ne_zero.mpr hR.ne'
  have hq : q≠1:=by
    intro h
    exact ha ((div_eq_one_iff_eq hRc).mp h)
  have hep : ∀n,∑j,((M^n) i j : ℂ)*v j=a^n*v i :=by
    intro n
    have hh:=congrFun (eigen_power (M.map Complex.ofRealHom) a v (funext he) n) i
    rw [cast_pow] at hh
    exact hh
  have heq (n : ℕ) :
      (∑j,(((R^n)⁻¹*(M^n) i j : ℝ) : ℂ)*v j)/v i=q^n :=by
    simp_rw [Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_pow]
    have hs : (∑j,((R : ℂ)^n)⁻¹*((M^n) i j : ℂ)*v j)=
        ((R : ℂ)^n)⁻¹*(∑j,((M^n) i j : ℂ)*v j) :=by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hs,hep]
    simp [q,div_eq_mul_inv,mul_pow,inv_pow,hi,mul_assoc,mul_comm]
  have hf : Tendsto (fun n : ℕ=>∑j,(((R^n)⁻¹*(M^n) i j : ℝ) : ℂ)*v j)
      atTop (𝓝 (∑j,(L i j : ℂ)*v j)) :=by
    apply tendsto_finsetSum
    intro j _
    exact (Complex.continuous_ofReal.continuousAt.tendsto.comp (hlim i j)).mul_const (v j)
  have hz : Tendsto (fun n : ℕ=>q^n) atTop (𝓝 z) :=by
    simpa only [heq] using hf.div_const (v i)
  have hs := hz.comp (tendsto_add_atTop_nat 1)
  have hm := hz.mul_const q
  have hzm : z=z*q :=by
    apply tendsto_nhds_unique _ hm
    simpa only [Function.comp_def,pow_succ] using hs
  have hz0 : z=0 :=by
    have h : (q-1)*z=0 :=by
      calc
        _=z*q-z:=by ring
        _=0:=sub_eq_zero.mpr hzm.symm
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hq)
  have hnorm := tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mp (hz0 ▸ hz)
  have hh : ‖a‖/R<1 :=by
    simpa only [q,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR] using hnorm
  exact (div_lt_one hR).mp hh
end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PrimitivePerronSpectral
