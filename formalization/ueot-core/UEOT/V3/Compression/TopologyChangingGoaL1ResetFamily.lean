import UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm

/-!
# Constant-row reset family for canonical direct-L1 GOA certificates

The completely mixing benchmark is one member of a larger algebraic family.
For any matrix whose rows are all the same vector `q`, every zero-total-mass
signed vector is annihilated by one matrix step.  Hence the residual operator
on the zero-mass subspace is exactly `-I`.

This module proves that every such constant-row matrix has canonical direct-L1
residual conorm exactly `1` on nontrivial finite state spaces, and that its
canonical direct-L1 certificate radius is strictly smaller than the generic
Euclidean singular-value-to-TV certificate for every positive perturbation
envelope.

The algebraic statements do not require `q` to be a probability row.  When
`q` is normalized and nonnegative, the same matrix is the usual one-step reset
stochastic kernel.
-/

namespace UEOT.V3.Compression.TopologyChangingGoaL1ResetFamily

open UEOT.V3
open UEOT.V3.Compression.TopologyChangingGoaSpectralIsolation
open UEOT.V3.Compression.TopologyChangingGoaRestrictedResidualAdapter
open UEOT.V3.Compression.TopologyChangingGoaL1ResidualAdapter
open UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm
open UEOT.V3.Compression.TopologyChangingGoaSharpSingularValue
open UEOT.V3.Compression.TopologyChangingGoaZeroMassDimension

universe uS
noncomputable section
variable {S : Type uS} [Fintype S] [Nonempty S]
noncomputable local instance : DecidableEq S := Classical.decEq S

/-- Constant-row reset matrix: every source state uses the same target row `q`. -/
def constantRowMatrix (q : S → ℝ) : Matrix S S ℝ :=
  fun _ j => q j

theorem vecMul_constantRowMatrix_of_sum_zero
    (q v : S → ℝ) (hv : (∑ s, v s) = 0) :
    Matrix.vecMul v (constantRowMatrix q) = 0 := by
  funext j
  rw [Matrix.vecMul_apply_eq_sum]
  change (∑ i, v i * q j) = 0
  rw [← Finset.sum_mul, hv]
  simp

theorem signedResidual_constantRowMatrix_of_sum_zero
    (q v : S → ℝ) (hv : (∑ s, v s) = 0) :
    signedResidual (constantRowMatrix q) v = -v := by
  unfold signedResidual
  rw [vecMul_constantRowMatrix_of_sum_zero q v hv]
  simp

theorem constantRowMatrix_l1Isolation_one (q : S → ℝ) :
    ZeroSumL1Isolation (constantRowMatrix q) 1 := by
  refine ⟨zero_lt_one, ?_⟩
  intro v hv
  rw [one_mul, signedResidual_constantRowMatrix_of_sum_zero q v hv]
  unfold signedL1
  simp


theorem constantRowMatrix_l1ResidualConorm_eq_one
    (q : S → ℝ) (hcard : 1 < Fintype.card S) :
    l1ResidualConorm (constantRowMatrix q) = 1 := by
  apply le_antisymm
  · rcases l1UnitGainSet_nonempty_of_card_one_lt
      (constantRowMatrix q) hcard with ⟨r, x, hxunit, rfl⟩
    have hmin := l1ResidualConorm_le_unit (constantRowMatrix q) x hxunit
    let v : S → ℝ := (x : WithLp 1 (S → ℝ)).ofLp
    have hv : (∑ s, v s) = 0 := by
      exact (zeroSumL1_mem_iff v).1 (by simpa [v] using x.property)
    have hres := signedResidual_constantRowMatrix_of_sum_zero q v hv
    have hxcoord :
        (WithLp.toLp 1 v : WithLp 1 (S → ℝ)) = (x : WithLp 1 (S → ℝ)) := by
      rw [WithLp.ext_iff]
    have hmapnorm :
        ‖zeroSumResidualL1Linear (constantRowMatrix q) x‖ =
          signedL1 (signedResidual (constantRowMatrix q) v) := by
      change ‖residualL1Linear (constantRowMatrix q)
        (x : WithLp 1 (S → ℝ))‖ = _
      rw [← hxcoord]
      have heq :
          residualL1Linear (constantRowMatrix q) (WithLp.toLp 1 v) =
            (WithLp.toLp 1 (signedResidual (constantRowMatrix q) v) :
              WithLp 1 (S → ℝ)) := by
        rw [WithLp.ext_iff]
        exact residualL1Linear_ofLp (constantRowMatrix q) v
      rw [heq]
      symm
      exact signedL1_eq_l1_norm _
    have hvnorm : signedL1 v = ‖x‖ := by
      rw [signedL1_eq_l1_norm, hxcoord]
      rfl
    rw [hmapnorm, hres] at hmin
    have hneg : signedL1 (-v) = signedL1 v := by
      unfold signedL1
      simp
    rw [hneg, hvnorm, hxunit] at hmin
    exact hmin
  · exact l1Isolation_le_l1ResidualConorm
      (constantRowMatrix q) hcard 1 (constantRowMatrix_l1Isolation_one q)

theorem constantRowMatrix_restricted_injective (q : S → ℝ) :
    Function.Injective (zeroSumResidualLinear (constantRowMatrix q)) := by
  have hinj1 : Function.Injective
      (zeroSumResidualL1Linear (constantRowMatrix q)) :=
    l1_restricted_injective_of_l1Isolation
      (constantRowMatrix q) 1 (constantRowMatrix_l1Isolation_one q)
  exact l2_restricted_injective_of_l1_restricted_injective
    (constantRowMatrix q) hinj1

theorem constantRowMatrix_minSingularValue_le_one
    (q : S → ℝ) (hcard : 1 < Fintype.card S) :
    restrictedMinSingularValue (constantRowMatrix q) ≤ 1 := by
  have hpos : 0 < Module.finrank ℝ (zeroSumEuclidean (S := S)) :=
    (zeroSum_finrank_pos_iff_card_one_lt (S := S)).2 hcard
  letI : Nontrivial (zeroSumEuclidean (S := S)) :=
    (Module.finrank_pos_iff).1 hpos
  obtain ⟨x, hx⟩ := exists_ne (0 : zeroSumEuclidean (S := S))
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let y : zeroSumEuclidean (S := S) := (‖x‖ : ℝ)⁻¹ • x
  have hynorm : ‖y‖ = 1 := by
    rw [norm_smul]
    simp only [Real.norm_eq_abs, abs_inv, abs_norm]
    exact inv_mul_cancel₀ (ne_of_gt hxnorm)
  let v : S → ℝ := ((y : zeroSumEuclidean (S := S)) : EuclideanSpace ℝ S).ofLp
  have hv : (∑ s, v s) = 0 := by
    exact (zeroSum_mem_iff v).1 (by simpa [v] using y.property)
  have hsharp := smallest_singularValue_mul_norm_le
    (zeroSumResidualLinear (constantRowMatrix q)) hpos y
  have hres := signedResidual_constantRowMatrix_of_sum_zero q v hv
  have hycoord :
      (WithLp.toLp 2 v : EuclideanSpace ℝ S) =
        (y : EuclideanSpace ℝ S) := by
    simpa [v]
  have hmapnorm :
      ‖zeroSumResidualLinear (constantRowMatrix q) y‖ =
        signedL2 (signedResidual (constantRowMatrix q) v) := by
    change ‖residualEuclideanLinear (constantRowMatrix q)
      (y : EuclideanSpace ℝ S)‖ = _
    rw [← hycoord]
    have heq :
        residualEuclideanLinear (constantRowMatrix q) (WithLp.toLp 2 v) =
          (WithLp.toLp 2 (signedResidual (constantRowMatrix q) v) :
            EuclideanSpace ℝ S) := by
      rw [WithLp.ext_iff]
      exact residualEuclideanLinear_ofLp (constantRowMatrix q) v
    rw [heq]
    symm
    exact signedL2_eq_euclidean_norm _
  have hvnorm : signedL2 v = ‖y‖ := by
    rw [signedL2_eq_euclidean_norm, hycoord]
    rfl
  rw [hmapnorm, hres] at hsharp
  have hneg : signedL2 (-v) = signedL2 v := by
    rw [signedL2_eq_euclidean_norm, signedL2_eq_euclidean_norm]
    rw [show (WithLp.toLp 2 (-v) : EuclideanSpace ℝ S) =
        -(WithLp.toLp 2 v : EuclideanSpace ℝ S) by
      rw [WithLp.ext_iff]
      rfl]
    simp
  rw [hneg, hvnorm, hynorm] at hsharp
  simpa [restrictedMinSingularValue] using hsharp

theorem constantRowMatrix_canonical_radius_lt_spectral_radius
    (q : S → ℝ) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hcard : 1 < Fintype.card S) :
    epsilon / l1ResidualConorm (constantRowMatrix q) <
      Real.sqrt (Fintype.card S) * epsilon /
        restrictedMinSingularValue (constantRowMatrix q) := by
  have hconorm := constantRowMatrix_l1ResidualConorm_eq_one q hcard
  have hinj := constantRowMatrix_restricted_injective q
  have hsigma_pos :
      0 < restrictedMinSingularValue (constantRowMatrix q) :=
    restrictedMinSingularValue_pos _
      ((zeroSum_finrank_pos_iff_card_one_lt (S := S)).2 hcard) hinj
  have hsigma_le := constantRowMatrix_minSingularValue_le_one q hcard
  have hsqrt_sq :
      (Real.sqrt (Fintype.card S)) ^ 2 = (Fintype.card S : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hcard_real : 1 < (Fintype.card S : ℝ) := by exact_mod_cast hcard
  have hsqrt_nonneg : 0 ≤ Real.sqrt (Fintype.card S) := Real.sqrt_nonneg _
  have hsqrt_gt : 1 < Real.sqrt (Fintype.card S) := by
    nlinarith
  have hsigma_lt_sqrt :
      restrictedMinSingularValue (constantRowMatrix q) <
        Real.sqrt (Fintype.card S) := lt_of_le_of_lt hsigma_le hsqrt_gt
  rw [hconorm, div_one]
  apply (lt_div_iff₀ hsigma_pos).2
  nlinarith

end
end UEOT.V3.Compression.TopologyChangingGoaL1ResetFamily
