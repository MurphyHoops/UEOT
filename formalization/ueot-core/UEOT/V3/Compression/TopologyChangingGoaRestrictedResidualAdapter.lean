import UEOT.V3.Compression.TopologyChangingGoaSpectralIsolation
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Restricted residual operator adapter for GOA stability

This adapter turns a structural property of the zero-mass signed-law residual
operator into the Euclidean minimum-gain certificate used by the S1 spectral
isolation theorem.

For finite state space `S`, let

`R_P(v) = vP - v`.

The relevant perturbations of probability laws lie in the zero-total-mass
subspace.  If the restriction of `R_P` to that subspace is injective, finite
dimensionality gives an antilipschitz constant and hence some positive lower
Euclidean gain `kappa`.  This is enough to invoke the merged S1 bridge and
obtain stationary-branch robustness.

Mathlib also identifies this injectivity exactly with positivity of every
singular value below the domain finrank.  This module deliberately stops at
that exact positivity characterization; identifying the optimal lower-gain
constant with the final indexed singular value is a separate linear-algebra
checkpoint.
-/

namespace UEOT.V3.Compression.TopologyChangingGoaRestrictedResidualAdapter

open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open UEOT.V3.Compression.TopologyChangingGoaSpectralIsolation

universe uS

noncomputable section

variable {S : Type uS} [Fintype S] [Nonempty S]
noncomputable local instance stateDecidableEq : DecidableEq S := Classical.decEq S
local instance stateMeasurableSpace : MeasurableSpace S := ⊤

/-- Total-mass functional on Euclidean signed laws. -/
def euclideanSum : EuclideanSpace ℝ S →ₗ[ℝ] ℝ where
  toFun v := ∑ s, v.ofLp s
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

/-- Euclidean zero-total-mass signed-law subspace. -/
def zeroSumEuclidean : Submodule ℝ (EuclideanSpace ℝ S) :=
  LinearMap.ker euclideanSum

/-- Euclidean linear realization of the signed residual `v ↦ vP - v`. -/
def residualEuclideanLinear (P : Matrix S S ℝ) :
    EuclideanSpace ℝ S →ₗ[ℝ] EuclideanSpace ℝ S :=
  (Matrix.toLpLin 2 2) P.transpose - LinearMap.id

/-- Coordinate compatibility between the Euclidean linear residual and the S1
coordinate residual. -/
theorem residualEuclideanLinear_ofLp (P : Matrix S S ℝ) (v : S → ℝ) :
    ((residualEuclideanLinear P) (WithLp.toLp 2 v)).ofLp =
      signedResidual P v := by
  funext j
  simp [residualEuclideanLinear, signedResidual]
  rw [Matrix.mulVec_transpose]

/-- Membership in the Euclidean kernel is exactly the zero-total-mass
condition. -/
theorem zeroSum_mem_iff (v : S → ℝ) :
    (WithLp.toLp 2 v : EuclideanSpace ℝ S) ∈ zeroSumEuclidean (S := S) ↔
      (∑ s, v s) = 0 := by
  simp [zeroSumEuclidean, euclideanSum]

/-- Residual operator restricted to the zero-mass domain.  The codomain remains
ambient Euclidean space; finite-dimensional lower-gain theory only needs the
domain restriction. -/
noncomputable def zeroSumResidualLinear (P : Matrix S S ℝ) :
    zeroSumEuclidean (S := S) →ₗ[ℝ] EuclideanSpace ℝ S :=
  (residualEuclideanLinear P).domRestrict (zeroSumEuclidean (S := S))

/-- Injectivity of the zero-mass residual restriction gives some positive
Euclidean minimum gain. -/
theorem exists_l2LowerSingularBound_of_restricted_injective
    (P : Matrix S S ℝ)
    (hinj : Function.Injective (zeroSumResidualLinear P)) :
    ∃ kappa > 0, ZeroSumL2LowerSingularBound P kappa := by
  rcases (zeroSumResidualLinear P).injective_iff_antilipschitz.mp hinj with
    ⟨K, hKpos, hanti⟩
  let kappa : ℝ := ((K : ℝ))⁻¹
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast hKpos
  have hkappa : 0 < kappa := inv_pos.mpr hKreal
  refine ⟨kappa, hkappa, hkappa, ?_⟩
  intro v hv
  have hmem :
      (WithLp.toLp 2 v : EuclideanSpace ℝ S) ∈ zeroSumEuclidean (S := S) :=
    (zeroSum_mem_iff v).2 hv
  let x : zeroSumEuclidean (S := S) := ⟨WithLp.toLp 2 v, hmem⟩
  have hanti0 := hanti.le_mul_dist 0 x
  have hxnorm : ‖(x : EuclideanSpace ℝ S)‖ = signedL2 v := by
    symm
    exact signedL2_eq_euclidean_norm v
  have hmapEq :
      (residualEuclideanLinear P) (WithLp.toLp 2 v) =
        (WithLp.toLp 2 (signedResidual P v) : EuclideanSpace ℝ S) := by
    rw [WithLp.ext_iff]
    exact residualEuclideanLinear_ofLp P v
  have hmapNorm :
      ‖(residualEuclideanLinear P) (WithLp.toLp 2 v)‖ =
        signedL2 (signedResidual P v) := by
    rw [hmapEq]
    symm
    exact signedL2_eq_euclidean_norm (signedResidual P v)
  have hbase :
      signedL2 v ≤ (K : ℝ) * signedL2 (signedResidual P v) := by
    simpa [dist_eq_norm, x, zeroSumResidualLinear, hxnorm, hmapNorm] using hanti0
  dsimp [kappa]
  calc
    (K : ℝ)⁻¹ * signedL2 v
        ≤ (K : ℝ)⁻¹ * ((K : ℝ) * signedL2 (signedResidual P v)) :=
      mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr hKreal.le)
    _ = signedL2 (signedResidual P v) := by field_simp

/-- End-to-end Track-S consequence: restricted injectivity supplies a positive
quantitative isolation constant and therefore a target invariant law inside the
S1 TV robustness tube. -/
theorem exists_stationary_tracking_of_restricted_injective
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (Q : Matrix S S ℝ) (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (muStar : stdSimplex ℝ S)
    (hmuStar : step P hP muStar = muStar)
    (epsilon : ℝ)
    (hinj : Function.Injective (zeroSumResidualLinear P))
    (hrow : ∀ x, crossRowTV P hP Q hQ x ≤ epsilon) :
    ∃ kappa > 0, ∃ muhat : stdSimplex ℝ S,
      muhat ∈ invariantLawSet Q hQ ∧
      lawTV muStar muhat ≤
        Real.sqrt (Fintype.card S) * epsilon / kappa := by
  rcases exists_l2LowerSingularBound_of_restricted_injective P hinj with
    ⟨kappa, hkappa, hiso⟩
  rcases l2LowerSingularBound_stationary_tracking
      P hP Q hQ muStar hmuStar kappa epsilon hiso hrow with
    ⟨muhat, hmuhat, hbound⟩
  exact ⟨kappa, hkappa, muhat, hmuhat, hbound⟩

/-- Exact singular-value characterization of the restricted injectivity
certificate, directly from Mathlib's finite-dimensional singular-value API. -/
theorem restricted_injective_iff_all_singularValues_pos
    (P : Matrix S S ℝ) :
    Function.Injective (zeroSumResidualLinear P) ↔
      ∀ i < Module.finrank ℝ (zeroSumEuclidean (S := S)),
        0 < (zeroSumResidualLinear P).singularValues i := by
  exact (zeroSumResidualLinear P).injective_iff_forall_lt_finrank_singularValues_pos

/-- Positivity of all relevant singular values is therefore enough to obtain
some quantitative GOA branch robustness constant. -/
theorem exists_stationary_tracking_of_all_singularValues_pos
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (Q : Matrix S S ℝ) (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (muStar : stdSimplex ℝ S)
    (hmuStar : step P hP muStar = muStar)
    (epsilon : ℝ)
    (hsv : ∀ i < Module.finrank ℝ (zeroSumEuclidean (S := S)),
      0 < (zeroSumResidualLinear P).singularValues i)
    (hrow : ∀ x, crossRowTV P hP Q hQ x ≤ epsilon) :
    ∃ kappa > 0, ∃ muhat : stdSimplex ℝ S,
      muhat ∈ invariantLawSet Q hQ ∧
      lawTV muStar muhat ≤
        Real.sqrt (Fintype.card S) * epsilon / kappa := by
  have hinj : Function.Injective (zeroSumResidualLinear P) :=
    (restricted_injective_iff_all_singularValues_pos P).2 hsv
  exact exists_stationary_tracking_of_restricted_injective
    P hP Q hQ muStar hmuStar epsilon hinj hrow

end

end UEOT.V3.Compression.TopologyChangingGoaRestrictedResidualAdapter
