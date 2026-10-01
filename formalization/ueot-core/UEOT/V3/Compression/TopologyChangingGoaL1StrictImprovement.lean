import UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm

/-!
# Strict improvement of the canonical direct-L1 GOA certificate

The merged canonical direct-L1 conorm is never worse than the generic
Euclidean singular-value-to-TV certificate.  This module shows that the
comparison can be strict on an explicit finite kernel family.

For the completely mixing matrix with identical uniform rows, every zero-mass
signed vector is sent to zero in one step, so the residual is exactly `-v`.
The canonical direct-L1 conorm is therefore exactly `1`.  On every nontrivial
finite state space and every positive perturbation envelope, the canonical L1
radius is strictly smaller than the generic spectral-TV radius.

This is a certificate comparison.  It does not claim that either upper bound is
always attained by an actual perturbation.
-/

namespace UEOT.V3.Compression.TopologyChangingGoaL1StrictImprovement

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

/-- Completely mixing finite kernel with identical uniform rows. -/
def uniformMixingKernel : Matrix S S ℝ :=
  fun _ _ => (Fintype.card S : ℝ)⁻¹

theorem vecMul_uniformMixingKernel_of_sum_zero
    (v : S → ℝ) (hv : (∑ s, v s) = 0) :
    Matrix.vecMul v (uniformMixingKernel (S := S)) = 0 := by
  funext j
  rw [Matrix.vecMul_apply_eq_sum]
  change (∑ i, v i * (Fintype.card S : ℝ)⁻¹) = 0
  rw [← Finset.sum_mul, hv]
  simp

theorem signedResidual_uniformMixingKernel_of_sum_zero
    (v : S → ℝ) (hv : (∑ s, v s) = 0) :
    signedResidual (uniformMixingKernel (S := S)) v = -v := by
  unfold signedResidual
  rw [vecMul_uniformMixingKernel_of_sum_zero v hv]
  simp

theorem uniformMixingKernel_l1Isolation_one :
    ZeroSumL1Isolation (uniformMixingKernel (S := S)) 1 := by
  refine ⟨zero_lt_one, ?_⟩
  intro v hv
  rw [one_mul, signedResidual_uniformMixingKernel_of_sum_zero v hv]
  unfold signedL1
  simp

theorem uniformMixingKernel_l1ResidualConorm_eq_one
    (hcard : 1 < Fintype.card S) :
    l1ResidualConorm (uniformMixingKernel (S := S)) = 1 := by
  apply le_antisymm
  · rcases l1UnitGainSet_nonempty_of_card_one_lt
      (uniformMixingKernel (S := S)) hcard with ⟨r, x, hxunit, rfl⟩
    have hmin := l1ResidualConorm_le_unit
      (uniformMixingKernel (S := S)) x hxunit
    let v : S → ℝ := (x : WithLp 1 (S → ℝ)).ofLp
    have hv : (∑ s, v s) = 0 := by
      exact (zeroSumL1_mem_iff v).1 (by simpa [v] using x.property)
    have hres := signedResidual_uniformMixingKernel_of_sum_zero v hv
    have hxcoord :
        (WithLp.toLp 1 v : WithLp 1 (S → ℝ)) = (x : WithLp 1 (S → ℝ)) := by
      rw [WithLp.ext_iff]
    have hmapnorm :
        ‖zeroSumResidualL1Linear (uniformMixingKernel (S := S)) x‖ =
          signedL1 (signedResidual (uniformMixingKernel (S := S)) v) := by
      change ‖residualL1Linear (uniformMixingKernel (S := S))
        (x : WithLp 1 (S → ℝ))‖ = _
      rw [← hxcoord]
      have heq :
          residualL1Linear (uniformMixingKernel (S := S)) (WithLp.toLp 1 v) =
            (WithLp.toLp 1 (signedResidual (uniformMixingKernel (S := S)) v) :
              WithLp 1 (S → ℝ)) := by
        rw [WithLp.ext_iff]
        exact residualL1Linear_ofLp (uniformMixingKernel (S := S)) v
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
      (uniformMixingKernel (S := S)) hcard 1 uniformMixingKernel_l1Isolation_one

theorem uniformMixingKernel_restricted_injective :
    Function.Injective (zeroSumResidualLinear (uniformMixingKernel (S := S))) := by
  have hinj1 : Function.Injective
      (zeroSumResidualL1Linear (uniformMixingKernel (S := S))) :=
    l1_restricted_injective_of_l1Isolation
      (uniformMixingKernel (S := S)) 1 uniformMixingKernel_l1Isolation_one
  exact l2_restricted_injective_of_l1_restricted_injective
    (uniformMixingKernel (S := S)) hinj1

theorem uniformMixingKernel_minSingularValue_le_one
    (hcard : 1 < Fintype.card S) :
    restrictedMinSingularValue (uniformMixingKernel (S := S)) ≤ 1 := by
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
    (zeroSumResidualLinear (uniformMixingKernel (S := S))) hpos y
  have hres := signedResidual_uniformMixingKernel_of_sum_zero v hv
  have hycoord :
      (WithLp.toLp 2 v : EuclideanSpace ℝ S) =
        (y : EuclideanSpace ℝ S) := by
    simpa [v]
  have hmapnorm :
      ‖zeroSumResidualLinear (uniformMixingKernel (S := S)) y‖ =
        signedL2 (signedResidual (uniformMixingKernel (S := S)) v) := by
    change ‖residualEuclideanLinear (uniformMixingKernel (S := S))
      (y : EuclideanSpace ℝ S)‖ = _
    rw [← hycoord]
    have heq :
        residualEuclideanLinear (uniformMixingKernel (S := S))
            (WithLp.toLp 2 v) =
          (WithLp.toLp 2 (signedResidual (uniformMixingKernel (S := S)) v) :
            EuclideanSpace ℝ S) := by
      rw [WithLp.ext_iff]
      exact residualEuclideanLinear_ofLp (uniformMixingKernel (S := S)) v
    rw [heq]
    symm
    exact signedL2_eq_euclidean_norm _
  have hvnorm : signedL2 v = ‖y‖ := by
    rw [signedL2_eq_euclidean_norm, hycoord]
    rfl
  rw [hmapnorm, hres] at hsharp
  have hneg : signedL2 (-v) = signedL2 v := by
    rw [signedL2_eq_euclidean_norm, signedL2_eq_euclidean_norm]
    change ‖(WithLp.toLp 2 (-v) : EuclideanSpace ℝ S)‖ =
      ‖(WithLp.toLp 2 v : EuclideanSpace ℝ S)‖
    rw [show (WithLp.toLp 2 (-v) : EuclideanSpace ℝ S) =
        -(WithLp.toLp 2 v : EuclideanSpace ℝ S) by
      rw [WithLp.ext_iff]
      rfl]
    simp
  rw [hneg, hvnorm, hynorm] at hsharp
  simpa [restrictedMinSingularValue] using hsharp

theorem uniformMixingKernel_canonical_radius_lt_spectral_radius
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hcard : 1 < Fintype.card S) :
    epsilon / l1ResidualConorm (uniformMixingKernel (S := S)) <
      Real.sqrt (Fintype.card S) * epsilon /
        restrictedMinSingularValue (uniformMixingKernel (S := S)) := by
  have hconorm := uniformMixingKernel_l1ResidualConorm_eq_one (S := S) hcard
  have hinj := uniformMixingKernel_restricted_injective (S := S)
  have hsigma_pos :
      0 < restrictedMinSingularValue (uniformMixingKernel (S := S)) :=
    restrictedMinSingularValue_pos _
      ((zeroSum_finrank_pos_iff_card_one_lt (S := S)).2 hcard) hinj
  have hsigma_le := uniformMixingKernel_minSingularValue_le_one (S := S) hcard
  have hsqrt_sq :
      (Real.sqrt (Fintype.card S)) ^ 2 = (Fintype.card S : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hcard_real : 1 < (Fintype.card S : ℝ) := by exact_mod_cast hcard
  have hsqrt_nonneg : 0 ≤ Real.sqrt (Fintype.card S) := Real.sqrt_nonneg _
  have hsqrt_gt : 1 < Real.sqrt (Fintype.card S) := by
    nlinarith
  have hsigma_lt_sqrt :
      restrictedMinSingularValue (uniformMixingKernel (S := S)) <
        Real.sqrt (Fintype.card S) := lt_of_le_of_lt hsigma_le hsqrt_gt
  rw [hconorm, div_one]
  apply (lt_div_iff₀ hsigma_pos).2
  nlinarith

end
end UEOT.V3.Compression.TopologyChangingGoaL1StrictImprovement
