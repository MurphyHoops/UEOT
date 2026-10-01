import UEOT.V3.Compression.TopologyChangingGoaRestrictedResidualAdapter
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Direct L1 residual adapter for topology-changing GOA stability

This module realizes the same zero-mass residual operator in finite-dimensional
`L1` geometry and proves that its qualitative injectivity is exactly the same
as in the existing Euclidean `L2` realization.  Finite-dimensional
antilipschitzness then yields existence of a positive direct `L1` minimum-gain
certificate, which feeds the existing exact-TV residual theorem without an
explicit `sqrt(card S)` norm-conversion factor.

The quantitative `L1` witness produced here is existential.  This module does
not identify the optimal `L1` minimum gain, does not provide a closed-form
formula for it, and does not claim its resulting numerical radius is strictly
better than the explicit Euclidean singular-value bound on every kernel.
-/

namespace UEOT.V3.Compression.TopologyChangingGoaL1ResidualAdapter

open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open UEOT.V3.Compression.TopologyChangingGoaSpectralIsolation
open UEOT.V3.Compression.TopologyChangingGoaRestrictedResidualAdapter

universe uS
noncomputable section

variable {S : Type uS} [Fintype S] [Nonempty S]
noncomputable local instance : DecidableEq S := Classical.decEq S

noncomputable def l1Sum : WithLp 1 (S → ℝ) →ₗ[ℝ] ℝ where
  toFun v := ∑ s, v.ofLp s
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

noncomputable def zeroSumL1Space : Submodule ℝ (WithLp 1 (S → ℝ)) :=
  LinearMap.ker l1Sum

noncomputable def residualL1Linear (P : Matrix S S ℝ) :
    WithLp 1 (S → ℝ) →ₗ[ℝ] WithLp 1 (S → ℝ) :=
  (Matrix.toLpLin 1 1) P.transpose - LinearMap.id

theorem residualL1Linear_ofLp (P : Matrix S S ℝ) (v : S → ℝ) :
    ((residualL1Linear P) (WithLp.toLp 1 v)).ofLp = signedResidual P v := by
  funext j
  simp [residualL1Linear, signedResidual]
  rw [Matrix.mulVec_transpose]

theorem zeroSumL1_mem_iff (v : S → ℝ) :
    (WithLp.toLp 1 v : WithLp 1 (S → ℝ)) ∈ zeroSumL1Space (S := S) ↔
      (∑ s, v s) = 0 := by
  change (∑ s, (WithLp.toLp 1 v : WithLp 1 (S → ℝ)).ofLp s) = 0 ↔ _
  simp

theorem signedL1_eq_l1_norm (v : S → ℝ) :
    signedL1 v = ‖(WithLp.toLp 1 v : WithLp 1 (S → ℝ))‖ := by
  rw [PiLp.norm_eq_of_L1]
  unfold signedL1
  simp [Real.norm_eq_abs]

noncomputable def zeroSumResidualL1Linear (P : Matrix S S ℝ) :
    zeroSumL1Space (S := S) →ₗ[ℝ] WithLp 1 (S → ℝ) :=
  (residualL1Linear P).domRestrict (zeroSumL1Space (S := S))

/-- Existing L2 restricted injectivity implies the coordinate residual has no
nonzero zero-mass kernel vector. -/
theorem coordinate_kernel_trivial_of_l2_restricted_injective
    (P : Matrix S S ℝ)
    (hinj : Function.Injective (zeroSumResidualLinear P))
    (v : S → ℝ) (hv : (∑ s, v s) = 0)
    (hres : signedResidual P v = 0) :
    v = 0 := by
  have hmem :
      (WithLp.toLp 2 v : EuclideanSpace ℝ S) ∈ zeroSumEuclidean (S := S) :=
    (zeroSum_mem_iff v).2 hv
  let x : zeroSumEuclidean (S := S) := ⟨WithLp.toLp 2 v, hmem⟩
  have hxmap : zeroSumResidualLinear P x = 0 := by
    rw [WithLp.ext_iff]
    simpa [zeroSumResidualLinear, x, residualEuclideanLinear_ofLp, hres]
  have hxzero : x = 0 := by
    apply hinj
    simpa using hxmap
  funext s
  have hs := congrArg (fun z : zeroSumEuclidean (S := S) =>
    ((z : EuclideanSpace ℝ S).ofLp s)) hxzero
  simpa [x] using hs

/-- The same algebraic residual restriction is injective in L1 geometry. -/
theorem l1_restricted_injective_of_l2_restricted_injective
    (P : Matrix S S ℝ)
    (hinj : Function.Injective (zeroSumResidualLinear P)) :
    Function.Injective (zeroSumResidualL1Linear P) := by
  intro x y hxy
  apply Subtype.ext
  let v : S → ℝ := ((x - y : zeroSumL1Space (S := S)) : WithLp 1 (S → ℝ)).ofLp
  have hv : (∑ s, v s) = 0 := by
    exact (zeroSumL1_mem_iff v).1 (by simpa [v] using (x - y).property)
  have hmapzero : zeroSumResidualL1Linear P (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hres : signedResidual P v = 0 := by
    rw [← residualL1Linear_ofLp]
    simpa [zeroSumResidualL1Linear, v] using congrArg WithLp.ofLp hmapzero
  have hvzero := coordinate_kernel_trivial_of_l2_restricted_injective P hinj v hv hres
  have hsubzero : (x : WithLp 1 (S → ℝ)) - y = 0 := by
    rw [WithLp.ext_iff]
    simpa [v] using hvzero
  exact sub_eq_zero.mp hsubzero

/-- L1 restricted injectivity yields some positive exact L1 minimum-gain
certificate by finite-dimensional antilipschitzness. -/
theorem exists_l1Isolation_of_l1_restricted_injective
    (P : Matrix S S ℝ)
    (hinj : Function.Injective (zeroSumResidualL1Linear P)) :
    ∃ kappa > 0, ZeroSumL1Isolation P kappa := by
  rcases (zeroSumResidualL1Linear P).injective_iff_antilipschitz.mp hinj with
    ⟨K, hKpos, hanti⟩
  let kappa : ℝ := ((K : ℝ))⁻¹
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast hKpos
  have hkappa : 0 < kappa := inv_pos.mpr hKreal
  refine ⟨kappa, hkappa, hkappa, ?_⟩
  intro v hv
  have hmem :
      (WithLp.toLp 1 v : WithLp 1 (S → ℝ)) ∈ zeroSumL1Space (S := S) :=
    (zeroSumL1_mem_iff v).2 hv
  let x : zeroSumL1Space (S := S) := ⟨WithLp.toLp 1 v, hmem⟩
  have hanti0 := hanti.le_mul_dist 0 x
  have hxnorm : ‖(x : WithLp 1 (S → ℝ))‖ = signedL1 v := by
    symm
    exact signedL1_eq_l1_norm v
  have hmapEq :
      residualL1Linear P (WithLp.toLp 1 v) =
        (WithLp.toLp 1 (signedResidual P v) : WithLp 1 (S → ℝ)) := by
    rw [WithLp.ext_iff]
    exact residualL1Linear_ofLp P v
  have hmapNorm :
      ‖residualL1Linear P (WithLp.toLp 1 v)‖ =
        signedL1 (signedResidual P v) := by
    rw [hmapEq]
    symm
    exact signedL1_eq_l1_norm (signedResidual P v)
  have hbase :
      signedL1 v ≤ (K : ℝ) * signedL1 (signedResidual P v) := by
    simpa [dist_eq_norm, x, zeroSumResidualL1Linear, hxnorm, hmapNorm] using hanti0
  dsimp [kappa]
  calc
    (K : ℝ)⁻¹ * signedL1 v
        ≤ (K : ℝ)⁻¹ * ((K : ℝ) * signedL1 (signedResidual P v)) :=
      mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr hKreal.le)
    _ = signedL1 (signedResidual P v) := by field_simp

/-- Existing spectral injectivity therefore guarantees existence of an exact
TV-geometry residual isolation constant. -/
theorem exists_l1Isolation_of_l2_restricted_injective
    (P : Matrix S S ℝ)
    (hinj : Function.Injective (zeroSumResidualLinear P)) :
    ∃ kappa > 0, ZeroSumL1Isolation P kappa := by
  exact exists_l1Isolation_of_l1_restricted_injective P
    (l1_restricted_injective_of_l2_restricted_injective P hinj)



/-- An exact positive L1 lower-gain certificate forces the coordinate residual
kernel on zero-mass vectors to be trivial. -/
theorem coordinate_kernel_trivial_of_l1Isolation
    (P : Matrix S S ℝ) (kappa : ℝ)
    (hiso : ZeroSumL1Isolation P kappa)
    (v : S → ℝ) (hv : (∑ s, v s) = 0)
    (hres : signedResidual P v = 0) :
    v = 0 := by
  have hlow := hiso.lower v hv
  have hresnorm : signedL1 (signedResidual P v) = 0 := by
    rw [hres]
    simp [signedL1]
  rw [hresnorm] at hlow
  have hnonneg : 0 ≤ signedL1 v := by
    unfold signedL1
    exact Finset.sum_nonneg fun i hi => abs_nonneg _
  have hl1zero : signedL1 v = 0 := by
    nlinarith [hiso.kappa_pos]
  have hnorm : ‖(WithLp.toLp 1 v : WithLp 1 (S → ℝ))‖ = 0 := by
    rw [← signedL1_eq_l1_norm v]
    exact hl1zero
  have hzero : (WithLp.toLp 1 v : WithLp 1 (S → ℝ)) = 0 := norm_eq_zero.mp hnorm
  have hof := congrArg WithLp.ofLp hzero
  simpa using hof

/-- An L1 isolation certificate implies injectivity of the L1 restricted
residual operator. -/
theorem l1_restricted_injective_of_l1Isolation
    (P : Matrix S S ℝ) (kappa : ℝ)
    (hiso : ZeroSumL1Isolation P kappa) :
    Function.Injective (zeroSumResidualL1Linear P) := by
  intro x y hxy
  apply Subtype.ext
  let v : S → ℝ := ((x - y : zeroSumL1Space (S := S)) : WithLp 1 (S → ℝ)).ofLp
  have hv : (∑ s, v s) = 0 := by
    exact (zeroSumL1_mem_iff v).1 (by simpa [v] using (x - y).property)
  have hmapzero : zeroSumResidualL1Linear P (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hres : signedResidual P v = 0 := by
    rw [← residualL1Linear_ofLp]
    simpa [zeroSumResidualL1Linear, v] using congrArg WithLp.ofLp hmapzero
  have hvzero := coordinate_kernel_trivial_of_l1Isolation P kappa hiso v hv hres
  have hsubzero : (x : WithLp 1 (S → ℝ)) - y = 0 := by
    rw [WithLp.ext_iff]
    simpa [v] using hvzero
  exact sub_eq_zero.mp hsubzero

/-- L1 restricted injectivity also implies the same algebraic injectivity in
Euclidean L2 geometry. -/
theorem l2_restricted_injective_of_l1_restricted_injective
    (P : Matrix S S ℝ)
    (hinj : Function.Injective (zeroSumResidualL1Linear P)) :
    Function.Injective (zeroSumResidualLinear P) := by
  intro x y hxy
  apply Subtype.ext
  let v : S → ℝ := ((x - y : zeroSumEuclidean (S := S)) : EuclideanSpace ℝ S).ofLp
  have hv : (∑ s, v s) = 0 := by
    exact (zeroSum_mem_iff v).1 (by simpa [v] using (x - y).property)
  have hmapzero : zeroSumResidualLinear P (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hres : signedResidual P v = 0 := by
    rw [← residualEuclideanLinear_ofLp]
    simpa [zeroSumResidualLinear, v] using congrArg WithLp.ofLp hmapzero
  have hmem1 :
      (WithLp.toLp 1 v : WithLp 1 (S → ℝ)) ∈ zeroSumL1Space (S := S) :=
    (zeroSumL1_mem_iff v).2 hv
  let z : zeroSumL1Space (S := S) := ⟨WithLp.toLp 1 v, hmem1⟩
  have hzmap : zeroSumResidualL1Linear P z = 0 := by
    rw [WithLp.ext_iff]
    simpa [zeroSumResidualL1Linear, z, residualL1Linear_ofLp, hres]
  have hzzero : z = 0 := by
    apply hinj
    simpa using hzmap
  have hvzero : v = 0 := by
    have hof := congrArg (fun w : zeroSumL1Space (S := S) =>
      ((w : WithLp 1 (S → ℝ)).ofLp)) hzzero
    simpa [z] using hof
  have hsubzero : (x : EuclideanSpace ℝ S) - y = 0 := by
    rw [WithLp.ext_iff]
    simpa [v] using hvzero
  exact sub_eq_zero.mp hsubzero

/-- Injectivity of the zero-mass residual restriction is norm-independent
between the finite L1 and Euclidean L2 realizations. -/
theorem l1_restricted_injective_iff_l2_restricted_injective
    (P : Matrix S S ℝ) :
    Function.Injective (zeroSumResidualL1Linear P) ↔
      Function.Injective (zeroSumResidualLinear P) := by
  exact ⟨l2_restricted_injective_of_l1_restricted_injective P,
    l1_restricted_injective_of_l2_restricted_injective P⟩

/-- Finite-dimensional L1 restricted injectivity is equivalent to existence of
some positive exact L1 minimum-gain certificate. -/
theorem l1_restricted_injective_iff_exists_l1Isolation
    (P : Matrix S S ℝ) :
    Function.Injective (zeroSumResidualL1Linear P) ↔
      ∃ kappa > 0, ZeroSumL1Isolation P kappa := by
  constructor
  · exact exists_l1Isolation_of_l1_restricted_injective P
  · rintro ⟨kappa, hkappa, hiso⟩
    exact l1_restricted_injective_of_l1Isolation P kappa hiso

/-- The existing zero-mass restricted residual injectivity condition is
exactly equivalent to existence of some positive direct L1/TV minimum-gain
certificate.  The qualitative isolation condition is therefore independent of
whether the finite-dimensional signed-law space is equipped with L1 or L2
geometry; only the quantitative constant changes. -/
theorem restricted_injective_iff_exists_l1Isolation
    (P : Matrix S S ℝ) :
    Function.Injective (zeroSumResidualLinear P) ↔
      ∃ kappa > 0, ZeroSumL1Isolation P kappa := by
  rw [← l1_restricted_injective_iff_l2_restricted_injective P]
  exact l1_restricted_injective_iff_exists_l1Isolation P

/-- Positive Euclidean singular spectrum is therefore equivalent to existence
of some positive exact L1/TV residual-isolation constant. -/
theorem all_singularValues_pos_iff_exists_l1Isolation
    (P : Matrix S S ℝ) :
    (∀ i < Module.finrank ℝ (zeroSumEuclidean (S := S)),
      0 < (zeroSumResidualLinear P).singularValues i) ↔
      ∃ kappa > 0, ZeroSumL1Isolation P kappa := by
  rw [← restricted_injective_iff_all_singularValues_pos P]
  rw [← l1_restricted_injective_iff_l2_restricted_injective P]
  exact l1_restricted_injective_iff_exists_l1Isolation P

/-- End-to-end direct-TV consequence: spectral injectivity guarantees existence
of some positive L1 residual gain and therefore an exact TV tracking radius
`epsilon / kappa`. -/
theorem exists_l1_stationary_tracking_of_l2_restricted_injective
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (Q : Matrix S S ℝ) (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (muStar : stdSimplex ℝ S)
    (hmuStar : step P hP muStar = muStar)
    (epsilon : ℝ)
    (hinj : Function.Injective (zeroSumResidualLinear P))
    (hrow : ∀ x, crossRowTV P hP Q hQ x ≤ epsilon) :
    ∃ kappa > 0, ∃ muhat : stdSimplex ℝ S,
      muhat ∈ invariantLawSet Q hQ ∧
      lawTV muStar muhat ≤ epsilon / kappa := by
  rcases exists_l1Isolation_of_l2_restricted_injective P hinj with
    ⟨kappa, hkappa, hiso⟩
  rcases l1Isolation_stationary_tracking
      P hP Q hQ muStar hmuStar kappa epsilon hiso hrow with
    ⟨muhat, hmuhat, hbound⟩
  exact ⟨kappa, hkappa, muhat, hmuhat, hbound⟩


/-- End-to-end direct-TV consequence stated directly from positive Euclidean
singular spectrum.  The resulting L1 minimum-gain constant is existential in
this adapter; a later canonical-conorm layer may identify the optimal value. -/
theorem exists_l1_stationary_tracking_of_all_singularValues_pos
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (Q : Matrix S S ℝ) (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (muStar : stdSimplex ℝ S)
    (hmuStar : step P hP muStar = muStar)
    (epsilon : ℝ)
    (hall : ∀ i < Module.finrank ℝ (zeroSumEuclidean (S := S)),
      0 < (zeroSumResidualLinear P).singularValues i)
    (hrow : ∀ x, crossRowTV P hP Q hQ x ≤ epsilon) :
    ∃ kappa > 0, ∃ muhat : stdSimplex ℝ S,
      muhat ∈ invariantLawSet Q hQ ∧
      lawTV muStar muhat ≤ epsilon / kappa := by
  have hinj : Function.Injective (zeroSumResidualLinear P) :=
    (restricted_injective_iff_all_singularValues_pos P).2 hall
  exact exists_l1_stationary_tracking_of_l2_restricted_injective
    P hP Q hQ muStar hmuStar epsilon hinj hrow

end
end UEOT.V3.Compression.TopologyChangingGoaL1ResidualAdapter
