import UEOT.V3.Compression.TopologyChangingGoaDobrushinL1Bridge
import Mathlib.GroupTheory.Perm.Cycle.Basic

/-!
# Permutation-kernel classification for residual isolation

This Track-S module classifies the residual geometry of finite deterministic
bijective kernels. For a permutation σ, its kernel sends each state
deterministically to σ(i).

On every nontrivial finite carrier the Dobrushin coefficient is exactly one,
because distinct source states have disjoint point-mass rows. The zero-mass
residual is finer: its restriction is injective exactly when σ is one cycle
on the full carrier. Equivalently, on a nontrivial carrier, the canonical
direct-L1 residual conorm is positive exactly in the single-cycle case.

For the converse, the proof constructs an explicit nonzero zero-mass
residual-kernel vector whenever there are multiple permutation orbits.

This is uncounted post-FINAL Track-S research. It does not change the frozen
Core-v3 ledger or the counted four-generator core.
-/

namespace UEOT.V3.Compression.TopologyChangingGoaPermutationClassification

open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.TopologyChangingGoaSpectralIsolation
open UEOT.V3.Compression.TopologyChangingGoaRestrictedResidualAdapter
open UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm

universe u
noncomputable section
variable {S : Type u} [Fintype S] [Nonempty S]
noncomputable local instance : DecidableEq S := Classical.decEq S
local instance : MeasurableSpace S := ⊤

/-- Deterministic row-stochastic matrix induced by a finite permutation. -/
def permKernel (σ : Equiv.Perm S) : Matrix S S ℝ :=
  fun i j => if j = σ i then 1 else 0

/-- Every permutation kernel is row stochastic. -/
theorem permKernel_stochastic (σ : Equiv.Perm S) :
    permKernel σ ∈ Matrix.rowStochastic ℝ S := by
  rw [Matrix.mem_rowStochastic_iff_sum]
  constructor
  · intro i j
    by_cases h : j = σ i <;> simp [permKernel, h]
  · intro i
    simp [permKernel]

/-- Signed-law transport by a permutation is pullback by its inverse. -/
theorem vecMul_permKernel (σ : Equiv.Perm S) (v : S → ℝ) (y : S) :
    Matrix.vecMul v (permKernel σ) y = v (σ.symm y) := by
  rw [Matrix.vecMul_apply_eq_sum]
  classical
  simp only [permKernel, mul_ite, mul_one, mul_zero]
  have hcond : ∀ j : S, (y = σ j) ↔ (j = σ.symm y) := by
    intro j
    constructor
    · intro h
      apply σ.injective
      simpa using h.symm
    · intro h
      rw [h]
      simp
  simp_rw [hcond]
  simp

private theorem residual_zero_implies_step_invariant
    (σ : Equiv.Perm S) (v : S → ℝ)
    (hres : signedResidual (permKernel σ) v = 0) :
    ∀ x, v (σ x) = v x := by
  intro x
  have hx := congrFun hres (σ x)
  unfold signedResidual at hx
  change Matrix.vecMul v (permKernel σ) (σ x) - v (σ x) = 0 at hx
  rw [vecMul_permKernel] at hx
  have hx' : v x - v (σ x) = 0 := by simpa using hx
  linarith

private theorem residual_zero_implies_pow_invariant
    (σ : Equiv.Perm S) (v : S → ℝ)
    (hres : signedResidual (permKernel σ) v = 0) :
    ∀ n x, v ((σ ^ n) x) = v x := by
  intro n
  induction n with
  | zero =>
      intro x
      simp
  | succ n ih =>
      intro x
      rw [pow_succ, Equiv.Perm.coe_mul, Function.comp_apply]
      rw [ih (σ x)]
      exact residual_zero_implies_step_invariant σ v hres x

private theorem residual_zero_implies_const_of_cycle
    (σ : Equiv.Perm S) (hcycle : σ.IsCycleOn Set.univ)
    (v : S → ℝ) (hres : signedResidual (permKernel σ) v = 0) :
    ∀ x y, v x = v y := by
  intro x y
  obtain ⟨n, hn⟩ := hcycle.exists_pow_eq' Set.finite_univ (by simp) (by simp)
  have hpow := residual_zero_implies_pow_invariant σ v hres n x
  calc
    v x = v ((σ ^ n) x) := hpow.symm
    _ = v y := congrArg v hn

private theorem zero_sum_residual_kernel_trivial_of_cycle
    (σ : Equiv.Perm S) (hcycle : σ.IsCycleOn Set.univ)
    (v : S → ℝ) (hv : (∑ s, v s) = 0)
    (hres : signedResidual (permKernel σ) v = 0) :
    v = 0 := by
  let x0 : S := Classical.choice (inferInstance : Nonempty S)
  have hconst : ∀ s, v s = v x0 := by
    intro s
    exact residual_zero_implies_const_of_cycle σ hcycle v hres s x0
  have hvx0 : v x0 = 0 := by
    have hcardpos : (0 : ℝ) < Fintype.card S := by
      exact_mod_cast Fintype.card_pos
    have hsum : (Fintype.card S : ℝ) * v x0 = 0 := by
      simpa only [hconst, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hv
    exact (mul_eq_zero.mp hsum).resolve_left (ne_of_gt hcardpos)
  funext s
  rw [hconst s, hvx0]
  rfl

private theorem permKernel_restricted_injective_of_cycle
    (σ : Equiv.Perm S) (hcycle : σ.IsCycleOn Set.univ) :
    Function.Injective (zeroSumResidualLinear (permKernel σ)) := by
  intro x y hxy
  have hmapzero : zeroSumResidualLinear (permKernel σ) (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  let v : S → ℝ :=
    ((x - y : zeroSumEuclidean (S := S)) : EuclideanSpace ℝ S).ofLp
  have hvsum : (∑ s, v s) = 0 := by
    exact (zeroSum_mem_iff v).1 (by simpa [v] using (x - y).property)
  have hlinzero :
      residualEuclideanLinear (permKernel σ) (WithLp.toLp 2 v) = 0 := by
    simpa [zeroSumResidualLinear, v] using hmapzero
  have hresCoord : signedResidual (permKernel σ) v = 0 := by
    rw [← residualEuclideanLinear_ofLp]
    funext s
    have hs := congrArg (fun z : EuclideanSpace ℝ S => z.ofLp s) hlinzero
    simpa using hs
  have hvzero := zero_sum_residual_kernel_trivial_of_cycle σ hcycle v hvsum hresCoord
  have hsub : x - y = 0 := by
    apply Subtype.ext
    rw [WithLp.ext_iff]
    simpa [v] using hvzero
  exact sub_eq_zero.mp hsub

private theorem permKernel_l1ResidualConorm_pos_of_cycle
    (σ : Equiv.Perm S) (hcycle : σ.IsCycleOn Set.univ)
    (hcard : 1 < Fintype.card S) :
    0 < l1ResidualConorm (permKernel σ) := by
  exact l1ResidualConorm_pos_of_restricted_injective
    (permKernel σ) hcard (permKernel_restricted_injective_of_cycle σ hcycle)

private theorem permKernel_rowTV_eq_one_of_ne
    (σ : Equiv.Perm S) {x y : S} (hxy : x ≠ y) :
    rowTV (permKernel σ) (permKernel_stochastic σ) x y = 1 := by
  unfold rowTV UEOT.V3.FiniteDiscountedControl.FiniteProbabilityRow.tvDist
  rw [UEOT.V3.FiniteRecurrentDecompositionStability.pmf_tv_eq_half_sum_abs]
  simp_rw [rowPMF_toReal]
  have hσxy : σ x ≠ σ y := σ.injective.ne hxy
  have habs : ∀ z : S,
      |permKernel σ x z - permKernel σ y z| =
        (if z = σ x then 1 else 0) + (if z = σ y then 1 else 0) := by
    intro z
    by_cases hxz : z = σ x
    · subst z
      simp [permKernel, hxy]
    · by_cases hyz : z = σ y
      · subst z
        simp [permKernel, hxz]
      · simp [permKernel, hxz, hyz]
  simp_rw [habs, Finset.sum_add_distrib]
  norm_num

/-- Every nontrivial finite permutation kernel has Dobrushin coefficient one. -/
theorem permKernel_dobrushinAlpha_eq_one
    (σ : Equiv.Perm S) (hcard : 1 < Fintype.card S) :
    dobrushinAlpha (permKernel σ) (permKernel_stochastic σ) = 1 := by
  have hle :
      dobrushinAlpha (permKernel σ) (permKernel_stochastic σ) ≤ 1 := by
    unfold dobrushinAlpha
    apply Finset.sup'_le
    intro z hz
    unfold rowTV UEOT.V3.FiniteDiscountedControl.FiniteProbabilityRow.tvDist
    exact UEOT.V3.TotalVariation.tvDist_le_one _ _
  let x : S := Classical.choice (inferInstance : Nonempty S)
  obtain ⟨y, hxy⟩ := Fintype.exists_ne_of_one_lt_card hcard x
  apply le_antisymm hle
  have h := rowTV_le_dobrushinAlpha
    (permKernel σ) (permKernel_stochastic σ) x y
  rw [permKernel_rowTV_eq_one_of_ne σ hxy.symm] at h
  exact h

private theorem not_cycleOn_univ_exists_not_sameCycle
    (σ : Equiv.Perm S) (hnot : ¬ σ.IsCycleOn Set.univ) :
    ∃ x y : S, ¬ σ.SameCycle x y := by
  by_contra h
  apply hnot
  refine ⟨σ.bijOn (by intro a; simp), ?_⟩
  intro x hx y hy
  by_contra hxy
  exact h ⟨x, y, hxy⟩

/-- Multiple orbits produce an explicit nonzero zero-mass residual-kernel vector. -/
theorem exists_zero_sum_residual_kernel_of_not_cycle
    (σ : Equiv.Perm S) (hnot : ¬ σ.IsCycleOn Set.univ) :
    ∃ v : S → ℝ,
      v ≠ 0 ∧
      (∑ s, v s) = 0 ∧
      signedResidual (permKernel σ) v = 0 := by
  obtain ⟨x, y, hxy⟩ := not_cycleOn_univ_exists_not_sameCycle σ hnot
  let p : S → Prop := fun z => σ.SameCycle x z
  let A : Finset S := Finset.univ.filter p
  let B : Finset S := Finset.univ.filter (fun z => ¬ p z)
  have hxA : x ∈ A := by
    simp [A, p, Equiv.Perm.SameCycle.rfl]
  have hyB : y ∈ B := by
    simp [B, p, hxy]
  have hApos : 0 < A.card := Finset.card_pos.mpr ⟨x, hxA⟩
  have hBpos : 0 < B.card := Finset.card_pos.mpr ⟨y, hyB⟩
  let v : S → ℝ := fun z =>
    if p z then (B.card : ℝ) else -(A.card : ℝ)
  have hvsum : (∑ s, v s) = 0 := by
    have hpart := Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset S) p v
    have hA :
        (∑ z ∈ A, v z) =
          (A.card : ℝ) * B.card := by
      calc
        (∑ z ∈ A, v z) = ∑ _z ∈ A, (B.card : ℝ) := by
          apply Finset.sum_congr rfl
          intro z hz
          have hpz : p z := by simpa [A] using hz
          simp [v, hpz]
        _ = (A.card : ℝ) * B.card := by
          simp [nsmul_eq_mul]
    have hB :
        (∑ z ∈ B, v z) =
          (B.card : ℝ) * (-(A.card : ℝ)) := by
      calc
        (∑ z ∈ B, v z) = ∑ _z ∈ B, (-(A.card : ℝ)) := by
          apply Finset.sum_congr rfl
          intro z hz
          have hpz : ¬ p z := by simpa [B] using hz
          simp [v, hpz]
        _ = (B.card : ℝ) * (-(A.card : ℝ)) := by
          simp [nsmul_eq_mul]
    have hpart' :
        (∑ z ∈ A, v z) + (∑ z ∈ B, v z) = ∑ z, v z := by
      simpa [A, B] using hpart
    rw [hA, hB] at hpart'
    nlinarith
  have hres : signedResidual (permKernel σ) v = 0 := by
    funext z
    unfold signedResidual
    change Matrix.vecMul v (permKernel σ) z - v z = 0
    rw [vecMul_permKernel]
    have hp : p (σ.symm z) ↔ p z := by
      exact Equiv.Perm.sameCycle_symm_apply_right
    simp [v, hp]
  have hvne : v ≠ 0 := by
    intro hv0
    have hx0 := congrFun hv0 x
    have hpx : p x := Equiv.Perm.SameCycle.rfl
    simp [v, hpx] at hx0
    simpa [hx0] using hBpos
  exact ⟨v, hvne, hvsum, hres⟩

/-- Multiple permutation orbits force failure of restricted residual injectivity. -/
theorem permKernel_not_restricted_injective_of_not_cycle
    (σ : Equiv.Perm S) (hnot : ¬ σ.IsCycleOn Set.univ) :
    ¬ Function.Injective (zeroSumResidualLinear (permKernel σ)) := by
  obtain ⟨v, hvne, hvsum, hres⟩ :=
    exists_zero_sum_residual_kernel_of_not_cycle σ hnot
  let w : zeroSumEuclidean (S := S) :=
    ⟨WithLp.toLp 2 v, (zeroSum_mem_iff v).2 hvsum⟩
  have hwne : w ≠ 0 := by
    intro hw0
    have hval := congrArg (fun z : zeroSumEuclidean (S := S) =>
      (z.1 : EuclideanSpace ℝ S).ofLp) hw0
    apply hvne
    simpa [w] using hval
  have hmapzero : zeroSumResidualLinear (permKernel σ) w = 0 := by
    rw [WithLp.ext_iff]
    simpa [zeroSumResidualLinear, w, residualEuclideanLinear_ofLp] using hres
  intro hinj
  apply hwne
  apply hinj
  simpa using hmapzero

/-- Restricted residual injectivity is equivalent to one full-carrier cycle. -/
theorem permKernel_restricted_injective_iff_cycle
    (σ : Equiv.Perm S) :
    Function.Injective (zeroSumResidualLinear (permKernel σ)) ↔
      σ.IsCycleOn Set.univ := by
  constructor
  · intro hinj
    by_contra hnot
    exact (permKernel_not_restricted_injective_of_not_cycle σ hnot) hinj
  · intro hcycle
    exact permKernel_restricted_injective_of_cycle σ hcycle

/-- Positive canonical direct-L1 conorm is equivalent to single-cycle topology. -/
theorem permKernel_l1ResidualConorm_pos_iff_cycle
    (σ : Equiv.Perm S) (hcard : 1 < Fintype.card S) :
    0 < l1ResidualConorm (permKernel σ) ↔ σ.IsCycleOn Set.univ := by
  rw [l1ResidualConorm_pos_iff_restricted_injective
    (permKernel σ) hcard]
  exact permKernel_restricted_injective_iff_cycle σ

/-- Complete permutation-family separation between Dobrushin and residual geometry. -/
theorem permutation_kernel_complete_classification
    (σ : Equiv.Perm S) (hcard : 1 < Fintype.card S) :
    dobrushinAlpha (permKernel σ) (permKernel_stochastic σ) = 1 ∧
      (0 < l1ResidualConorm (permKernel σ) ↔ σ.IsCycleOn Set.univ) := by
  exact ⟨permKernel_dobrushinAlpha_eq_one σ hcard,
    permKernel_l1ResidualConorm_pos_iff_cycle σ hcard⟩

end
end UEOT.V3.Compression.TopologyChangingGoaPermutationClassification
