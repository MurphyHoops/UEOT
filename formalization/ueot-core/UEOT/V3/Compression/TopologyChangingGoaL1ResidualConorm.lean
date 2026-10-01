import UEOT.V3.Compression.TopologyChangingGoaL1ResidualAdapter
import UEOT.V3.Compression.TopologyChangingGoaSharpSingularValue
import UEOT.V3.Compression.TopologyChangingGoaZeroMassDimension
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Canonical direct-L1 residual conorm for topology-changing GOA stability

This module turns the existential direct-L1 isolation witness into a canonical
kernel-specific constant.  It defines the residual conorm as the infimum of
residual L1 norms on the zero-mass L1 unit sphere and proves that, for nontrivial
finite state spaces, restricted injectivity is equivalent to strict positivity
of this conorm.

The canonical conorm is itself a `ZeroSumL1Isolation` certificate and is the
greatest admissible certificate constant.  It also dominates the generic
Euclidean spectral-to-TV denominator `sigma_min / sqrt(card S)`, hence its TV
tracking radius is never worse than the currently merged sharp spectral radius
when the perturbation envelope is nonnegative.

No claim is made here that the unit-sphere infimum is attained by a specific
vector; optimality is expressed as greatest admissible lower-gain constant.
-/

namespace UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm

open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open UEOT.V3.Compression.TopologyChangingGoaSpectralIsolation
open UEOT.V3.Compression.TopologyChangingGoaRestrictedResidualAdapter
open UEOT.V3.Compression.TopologyChangingGoaL1ResidualAdapter
open UEOT.V3.Compression.TopologyChangingGoaSharpSingularValue
open UEOT.V3.Compression.TopologyChangingGoaZeroMassDimension

universe uS
noncomputable section
variable {S : Type uS} [Fintype S] [Nonempty S]
noncomputable local instance : DecidableEq S := Classical.decEq S

theorem l1Sum_ne_zero : l1Sum (S := S) ≠ 0 := by
  intro hzero
  let s0 : S := Classical.choice (inferInstance : Nonempty S)
  let e : S → ℝ := fun s => if s = s0 then 1 else 0
  let e1 : WithLp 1 (S → ℝ) := WithLp.toLp 1 e
  have happ := congrArg (fun f : WithLp 1 (S → ℝ) →ₗ[ℝ] ℝ => f e1) hzero
  change (∑ s, e s) = 0 at happ
  have hsum : (∑ s, e s) = 1 := by simp [e]
  rw [hsum] at happ
  norm_num at happ

theorem finrank_l1Ambient :
    Module.finrank ℝ (WithLp 1 (S → ℝ)) = Fintype.card S := by
  calc
    Module.finrank ℝ (WithLp 1 (S → ℝ)) = Module.finrank ℝ (S → ℝ) :=
      (WithLp.linearEquiv 1 ℝ (S → ℝ)).finrank_eq
    _ = Fintype.card S := Module.finrank_pi ℝ

theorem finrank_zeroSumL1Space_add_one :
    Module.finrank ℝ (zeroSumL1Space (S := S)) + 1 = Fintype.card S := by
  unfold zeroSumL1Space
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero (l1Sum_ne_zero (S := S))
  rw [finrank_l1Ambient (S := S)] at h
  exact h

theorem zeroSumL1_finrank_pos_iff_card_one_lt :
    0 < Module.finrank ℝ (zeroSumL1Space (S := S)) ↔ 1 < Fintype.card S := by
  have h := finrank_zeroSumL1Space_add_one (S := S)
  omega

/-- Residual norms attained on the L1 unit sphere of the zero-mass subspace. -/
def l1UnitGainSet (P : Matrix S S ℝ) : Set ℝ :=
  {r | ∃ x : zeroSumL1Space (S := S),
    ‖x‖ = 1 ∧ r = ‖zeroSumResidualL1Linear P x‖}

/-- Canonical direct-L1 residual conorm. -/
def l1ResidualConorm (P : Matrix S S ℝ) : ℝ :=
  sInf (l1UnitGainSet P)

theorem l1UnitGainSet_bddBelow (P : Matrix S S ℝ) :
    BddBelow (l1UnitGainSet P) := by
  refine ⟨0, ?_⟩
  rintro r ⟨x, hx, rfl⟩
  exact norm_nonneg _

theorem l1UnitGainSet_nonempty_of_card_one_lt
    (P : Matrix S S ℝ) (hcard : 1 < Fintype.card S) :
    (l1UnitGainSet P).Nonempty := by
  have hpos : 0 < Module.finrank ℝ (zeroSumL1Space (S := S)) :=
    (zeroSumL1_finrank_pos_iff_card_one_lt (S := S)).2 hcard
  letI : Nontrivial (zeroSumL1Space (S := S)) :=
    (Module.finrank_pos_iff).1 hpos
  obtain ⟨x, hx⟩ := exists_ne (0 : zeroSumL1Space (S := S))
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let y : zeroSumL1Space (S := S) := (‖x‖ : ℝ)⁻¹ • x
  have hynorm : ‖y‖ = 1 := by
    rw [norm_smul]
    simp only [Real.norm_eq_abs, abs_inv, abs_norm]
    exact inv_mul_cancel₀ (ne_of_gt hxnorm)
  exact ⟨‖zeroSumResidualL1Linear P y‖, y, hynorm, rfl⟩

theorem l1ResidualConorm_le_unit
    (P : Matrix S S ℝ) (x : zeroSumL1Space (S := S))
    (hx : ‖x‖ = 1) :
    l1ResidualConorm P ≤ ‖zeroSumResidualL1Linear P x‖ := by
  apply csInf_le (l1UnitGainSet_bddBelow P)
  exact ⟨x, hx, rfl⟩

theorem l1ResidualConorm_mul_norm_le
    (P : Matrix S S ℝ) (x : zeroSumL1Space (S := S)) :
    l1ResidualConorm P * ‖x‖ ≤ ‖zeroSumResidualL1Linear P x‖ := by
  by_cases hx0 : x = 0
  · subst x
    simp
  · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    let y : zeroSumL1Space (S := S) := (‖x‖ : ℝ)⁻¹ • x
    have hynorm : ‖y‖ = 1 := by
      rw [norm_smul]
      simp only [Real.norm_eq_abs, abs_inv, abs_norm]
      exact inv_mul_cancel₀ (ne_of_gt hxpos)
    have hmin := l1ResidualConorm_le_unit P y hynorm
    have hTy :
        ‖zeroSumResidualL1Linear P y‖ =
          (‖x‖ : ℝ)⁻¹ * ‖zeroSumResidualL1Linear P x‖ := by
      simp [y, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
    rw [hTy] at hmin
    calc
      l1ResidualConorm P * ‖x‖
          ≤ ((‖x‖ : ℝ)⁻¹ * ‖zeroSumResidualL1Linear P x‖) * ‖x‖ :=
        mul_le_mul_of_nonneg_right hmin (norm_nonneg _)
      _ = ‖zeroSumResidualL1Linear P x‖ := by
        field_simp

theorem l1ResidualConorm_nonneg (P : Matrix S S ℝ)
    (hcard : 1 < Fintype.card S) :
    0 ≤ l1ResidualConorm P := by
  apply le_csInf (l1UnitGainSet_nonempty_of_card_one_lt P hcard)
  intro r hr
  rcases hr with ⟨x, hx, rfl⟩
  exact norm_nonneg _

theorem l1ResidualConorm_pos_of_restricted_injective
    (P : Matrix S S ℝ) (hcard : 1 < Fintype.card S)
    (hinj : Function.Injective (zeroSumResidualLinear P)) :
    0 < l1ResidualConorm P := by
  rcases exists_l1Isolation_of_l2_restricted_injective P hinj with
    ⟨kappa, hkappa, hiso⟩
  have hne := l1UnitGainSet_nonempty_of_card_one_lt P hcard
  have hk_le : kappa ≤ l1ResidualConorm P := by
    apply le_csInf hne
    intro r hr
    rcases hr with ⟨x, hxunit, rfl⟩
    let v : S → ℝ := (x : WithLp 1 (S → ℝ)).ofLp
    have hv : (∑ s, v s) = 0 := by
      exact (zeroSumL1_mem_iff v).1 (by simpa [v] using x.property)
    have hlower := hiso.lower v hv
    have hxnorm : signedL1 v = ‖x‖ := by
      rw [signedL1_eq_l1_norm]
      congr 1
    have hmapnorm :
        signedL1 (signedResidual P v) =
          ‖zeroSumResidualL1Linear P x‖ := by
      rw [signedL1_eq_l1_norm]
      congr 1
      rw [WithLp.ext_iff]
      simpa [zeroSumResidualL1Linear, v] using (residualL1Linear_ofLp P v).symm
    rw [hxnorm, hxunit, hmapnorm] at hlower
    simpa using hlower
  exact lt_of_lt_of_le hkappa hk_le

theorem l1ResidualConorm_isolation
    (P : Matrix S S ℝ) (hcard : 1 < Fintype.card S)
    (hinj : Function.Injective (zeroSumResidualLinear P)) :
    ZeroSumL1Isolation P (l1ResidualConorm P) := by
  refine ⟨l1ResidualConorm_pos_of_restricted_injective P hcard hinj, ?_⟩
  intro v hv
  have hmem :
      (WithLp.toLp 1 v : WithLp 1 (S → ℝ)) ∈ zeroSumL1Space (S := S) :=
    (zeroSumL1_mem_iff v).2 hv
  let x : zeroSumL1Space (S := S) := ⟨WithLp.toLp 1 v, hmem⟩
  have h := l1ResidualConorm_mul_norm_le P x
  have hxnorm : ‖x‖ = signedL1 v := by
    symm
    exact signedL1_eq_l1_norm v
  have hmapnorm :
      ‖zeroSumResidualL1Linear P x‖ = signedL1 (signedResidual P v) := by
    change ‖residualL1Linear P (WithLp.toLp 1 v)‖ = _
    have heq :
        residualL1Linear P (WithLp.toLp 1 v) =
          (WithLp.toLp 1 (signedResidual P v) : WithLp 1 (S → ℝ)) := by
      rw [WithLp.ext_iff]
      exact residualL1Linear_ofLp P v
    rw [heq]
    symm
    exact signedL1_eq_l1_norm (signedResidual P v)
  simpa [hxnorm, hmapnorm] using h




theorem l1ResidualConorm_lower
    (P : Matrix S S ℝ) (v : S → ℝ) (hv : (∑ s, v s) = 0) :
    l1ResidualConorm P * signedL1 v ≤ signedL1 (signedResidual P v) := by
  have hmem :
      (WithLp.toLp 1 v : WithLp 1 (S → ℝ)) ∈ zeroSumL1Space (S := S) :=
    (zeroSumL1_mem_iff v).2 hv
  let x : zeroSumL1Space (S := S) := ⟨WithLp.toLp 1 v, hmem⟩
  have h := l1ResidualConorm_mul_norm_le P x
  have hxnorm : ‖x‖ = signedL1 v := by
    symm
    exact signedL1_eq_l1_norm v
  have hmapnorm :
      ‖zeroSumResidualL1Linear P x‖ = signedL1 (signedResidual P v) := by
    change ‖residualL1Linear P (WithLp.toLp 1 v)‖ = _
    have heq :
        residualL1Linear P (WithLp.toLp 1 v) =
          (WithLp.toLp 1 (signedResidual P v) : WithLp 1 (S → ℝ)) := by
      rw [WithLp.ext_iff]
      exact residualL1Linear_ofLp P v
    rw [heq]
    symm
    exact signedL1_eq_l1_norm (signedResidual P v)
  simpa [hxnorm, hmapnorm] using h

theorem l1ResidualConorm_pos_iff_restricted_injective
    (P : Matrix S S ℝ) (hcard : 1 < Fintype.card S) :
    0 < l1ResidualConorm P ↔ Function.Injective (zeroSumResidualLinear P) := by
  constructor
  · intro hpos
    have hiso : ZeroSumL1Isolation P (l1ResidualConorm P) :=
      ⟨hpos, l1ResidualConorm_lower P⟩
    have hinj1 : Function.Injective (zeroSumResidualL1Linear P) :=
      l1_restricted_injective_of_l1Isolation P (l1ResidualConorm P) hiso
    exact l2_restricted_injective_of_l1_restricted_injective P hinj1
  · exact l1ResidualConorm_pos_of_restricted_injective P hcard


theorem l1ResidualConorm_pos_iff_all_singularValues_pos
    (P : Matrix S S ℝ) (hcard : 1 < Fintype.card S) :
    0 < l1ResidualConorm P ↔
      ∀ i < Module.finrank ℝ (zeroSumEuclidean (S := S)),
        0 < (zeroSumResidualLinear P).singularValues i := by
  rw [l1ResidualConorm_pos_iff_restricted_injective P hcard]
  exact restricted_injective_iff_all_singularValues_pos P

theorem l1Isolation_le_l1ResidualConorm
    (P : Matrix S S ℝ) (hcard : 1 < Fintype.card S)
    (kappa : ℝ) (hiso : ZeroSumL1Isolation P kappa) :
    kappa ≤ l1ResidualConorm P := by
  apply le_csInf (l1UnitGainSet_nonempty_of_card_one_lt P hcard)
  intro r hr
  rcases hr with ⟨x, hxunit, rfl⟩
  let v : S → ℝ := (x : WithLp 1 (S → ℝ)).ofLp
  have hv : (∑ s, v s) = 0 := by
    exact (zeroSumL1_mem_iff v).1 (by simpa [v] using x.property)
  have hlower := hiso.lower v hv
  have hxnorm : signedL1 v = ‖x‖ := by
    rw [signedL1_eq_l1_norm]
    congr 1
  have hmapnorm :
      signedL1 (signedResidual P v) =
        ‖zeroSumResidualL1Linear P x‖ := by
    rw [signedL1_eq_l1_norm]
    congr 1
    rw [WithLp.ext_iff]
    simpa [zeroSumResidualL1Linear, v] using (residualL1Linear_ofLp P v).symm
  rw [hxnorm, hxunit, hmapnorm] at hlower
  simpa using hlower


theorem canonical_l1_radius_le_of_isolation
    (P : Matrix S S ℝ) (hcard : 1 < Fintype.card S)
    (epsilon kappa : ℝ) (hepsilon : 0 ≤ epsilon)
    (hiso : ZeroSumL1Isolation P kappa) :
    epsilon / l1ResidualConorm P ≤ epsilon / kappa := by
  exact div_le_div_of_nonneg_left hepsilon hiso.kappa_pos
    (l1Isolation_le_l1ResidualConorm P hcard kappa hiso)

theorem l1ResidualConorm_isGreatest_isolation
    (P : Matrix S S ℝ) (hcard : 1 < Fintype.card S)
    (hinj : Function.Injective (zeroSumResidualLinear P)) :
    IsGreatest {kappa : ℝ | ZeroSumL1Isolation P kappa} (l1ResidualConorm P) := by
  refine ⟨l1ResidualConorm_isolation P hcard hinj, ?_⟩
  intro kappa hkappa
  exact l1Isolation_le_l1ResidualConorm P hcard kappa hkappa


theorem canonical_l1_stationary_tracking
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (Q : Matrix S S ℝ) (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (muStar : stdSimplex ℝ S)
    (hmuStar : step P hP muStar = muStar)
    (epsilon : ℝ) (hcard : 1 < Fintype.card S)
    (hinj : Function.Injective (zeroSumResidualLinear P))
    (hrow : ∀ x, crossRowTV P hP Q hQ x ≤ epsilon) :
    ∃ muhat : stdSimplex ℝ S,
      muhat ∈ invariantLawSet Q hQ ∧
      lawTV muStar muhat ≤ epsilon / l1ResidualConorm P := by
  exact l1Isolation_stationary_tracking
    P hP Q hQ muStar hmuStar (l1ResidualConorm P) epsilon
    (l1ResidualConorm_isolation P hcard hinj) hrow

theorem spectral_over_sqrt_card_le_l1ResidualConorm
    (P : Matrix S S ℝ) (hcard : 1 < Fintype.card S)
    (hinj : Function.Injective (zeroSumResidualLinear P)) :
    restrictedMinSingularValue P / Real.sqrt (Fintype.card S) ≤
      l1ResidualConorm P := by
  have hne := l1UnitGainSet_nonempty_of_card_one_lt P hcard
  have hsqrt_pos : 0 < Real.sqrt (Fintype.card S) := by
    apply Real.sqrt_pos.2
    exact_mod_cast (lt_trans Nat.zero_lt_one hcard)
  have hiso2 := sharp_l2LowerSingularBound_of_restricted_injective P
    ((zeroSum_finrank_pos_iff_card_one_lt (S := S)).2 hcard) hinj
  apply le_csInf hne
  intro r hr
  rcases hr with ⟨x, hxunit, rfl⟩
  let v : S → ℝ := (x : WithLp 1 (S → ℝ)).ofLp
  have hv : (∑ s, v s) = 0 := by
    exact (zeroSumL1_mem_iff v).1 (by simpa [v] using x.property)
  have hl2 := hiso2.lower v hv
  have hv_l1 : signedL1 v = 1 := by
    rw [signedL1_eq_l1_norm]
    simpa [v] using hxunit
  have hv_conv := signedL1_le_sqrt_card_mul_l2 v
  have hr_conv := signedL2_le_signedL1 (signedResidual P v)
  have hsigma_nonneg : 0 ≤ restrictedMinSingularValue P :=
    le_of_lt (restrictedMinSingularValue_pos P
      ((zeroSum_finrank_pos_iff_card_one_lt (S := S)).2 hcard) hinj)
  have hsqrt_nonneg : 0 ≤ Real.sqrt (Fintype.card S) := hsqrt_pos.le
  have hscaled :
      restrictedMinSingularValue P ≤
        Real.sqrt (Fintype.card S) * signedL1 (signedResidual P v) := by
    calc
      restrictedMinSingularValue P
          = restrictedMinSingularValue P * signedL1 v := by rw [hv_l1, mul_one]
      _ ≤ restrictedMinSingularValue P *
            (Real.sqrt (Fintype.card S) * signedL2 v) :=
        mul_le_mul_of_nonneg_left hv_conv hsigma_nonneg
      _ = Real.sqrt (Fintype.card S) *
            (restrictedMinSingularValue P * signedL2 v) := by ring
      _ ≤ Real.sqrt (Fintype.card S) * signedL2 (signedResidual P v) :=
        mul_le_mul_of_nonneg_left hl2 hsqrt_nonneg
      _ ≤ Real.sqrt (Fintype.card S) * signedL1 (signedResidual P v) :=
        mul_le_mul_of_nonneg_left hr_conv hsqrt_nonneg
  have hdiv :
      restrictedMinSingularValue P / Real.sqrt (Fintype.card S) ≤
        signedL1 (signedResidual P v) :=
    (div_le_iff₀ hsqrt_pos).2 (by simpa [mul_comm] using hscaled)
  have hmapnorm :
      signedL1 (signedResidual P v) = ‖zeroSumResidualL1Linear P x‖ := by
    rw [signedL1_eq_l1_norm]
    congr 1
    rw [WithLp.ext_iff]
    simpa [zeroSumResidualL1Linear, v] using (residualL1Linear_ofLp P v).symm
  simpa [hmapnorm] using hdiv


theorem canonical_l1_radius_le_spectral_radius
    (P : Matrix S S ℝ) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hcard : 1 < Fintype.card S)
    (hinj : Function.Injective (zeroSumResidualLinear P)) :
    epsilon / l1ResidualConorm P ≤
      Real.sqrt (Fintype.card S) * epsilon / restrictedMinSingularValue P := by
  have hsigma_pos : 0 < restrictedMinSingularValue P :=
    restrictedMinSingularValue_pos P
      ((zeroSum_finrank_pos_iff_card_one_lt (S := S)).2 hcard) hinj
  have hsqrt_pos : 0 < Real.sqrt (Fintype.card S) := by
    apply Real.sqrt_pos.2
    exact_mod_cast (lt_trans Nat.zero_lt_one hcard)
  have hbase_pos :
      0 < restrictedMinSingularValue P / Real.sqrt (Fintype.card S) :=
    div_pos hsigma_pos hsqrt_pos
  have hcomp := spectral_over_sqrt_card_le_l1ResidualConorm P hcard hinj
  have hdiv :
      epsilon / l1ResidualConorm P ≤
        epsilon / (restrictedMinSingularValue P / Real.sqrt (Fintype.card S)) :=
    div_le_div_of_nonneg_left hepsilon hbase_pos hcomp
  calc
    epsilon / l1ResidualConorm P
        ≤ epsilon / (restrictedMinSingularValue P / Real.sqrt (Fintype.card S)) := hdiv
    _ = Real.sqrt (Fintype.card S) * epsilon / restrictedMinSingularValue P := by
      field_simp

end
end UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm
