import UEOT.V3.Compression.TopologyChangingGoaResidualInverseStability
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Spectral / minimum-gain isolation for topology-changing GOA stability

The residual-inverse lane showed that robust tracking of one selected
stationary branch only needs an a-posteriori fixed-point error estimate

`D_TV(muStar, nu) <= C * D_TV(P nu, nu)`.

This module derives such an estimate from operator isolation on the zero-mass
subspace of signed finite laws.

There are two distinct norm geometries and they must not be conflated:

* an `L1` / total-variation minimum-gain bound gives the exact constant
  `C = 1 / kappa`;
* a standard Euclidean `L2` lower singular bound gives the dimension-safe TV
  constant `C = sqrt(card S) / kappa` through finite-dimensional norm
  comparison.

Thus a standard Euclidean singular-value statement does **not**, in general,
justify an unqualified `1 / kappa` TV constant.  The latter is exact only when
the lower bound is formulated in `L1` / TV geometry (or when additional norm
structure yields a sharper conversion).

For row-law dynamics, `Matrix.vecMul v P - v` is the signed residual
`(T_P - I)v`.  Its norm is identical to `(I - T_P)v`, so the sign convention
does not affect any minimum-gain or singular-value statement below.
-/

namespace UEOT.V3.Compression.TopologyChangingGoaSpectralIsolation

open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open UEOT.V3.Compression.TopologyChangingGoaResidualInverseStability

universe uS

noncomputable section

variable {S : Type uS} [Fintype S] [Nonempty S]

noncomputable local instance stateDecidableEq : DecidableEq S :=
  Classical.decEq S

local instance stateMeasurableSpace : MeasurableSpace S := ⊤

/-- Coordinate `L1` norm of a finite signed law. -/
def signedL1 (v : S → ℝ) : ℝ :=
  ∑ s, |v s|

/-- Euclidean `L2` norm written in coordinates. -/
def signedL2 (v : S → ℝ) : ℝ :=
  Real.sqrt (∑ s, (v s) ^ 2)

/-- Signed one-step fixed-point residual `(T_P - I)v`. -/
def signedResidual (P : Matrix S S ℝ) (v : S → ℝ) : S → ℝ :=
  Matrix.vecMul v P - v

/-- The coordinate definition `signedL2` is exactly the Mathlib Euclidean
norm on `EuclideanSpace ℝ S`. -/
theorem signedL2_eq_euclidean_norm (v : S → ℝ) :
    signedL2 v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ S)‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold signedL2
  apply congrArg Real.sqrt
  apply Finset.sum_congr rfl
  intro i hi
  simp [sq_abs]

/-- Finite-dimensional norm comparison `‖v‖₁ <= sqrt(n) ‖v‖₂`. -/
theorem signedL1_le_sqrt_card_mul_l2 (v : S → ℝ) :
    signedL1 v ≤ Real.sqrt (Fintype.card S) * signedL2 v := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt
    (Finset.univ : Finset S) (fun i => |v i|) (fun _ => (1 : ℝ))
  unfold signedL1 signedL2
  simpa [sq_abs, mul_comm] using h

/-- Finite-dimensional norm comparison `‖v‖₂ <= ‖v‖₁`. -/
theorem signedL2_le_signedL1 (v : S → ℝ) :
    signedL2 v ≤ signedL1 v := by
  have hsquares := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := (Finset.univ : Finset S)) (f := fun i => |v i|)
    (fun i hi => abs_nonneg (v i))
  have hsqrt := Real.sqrt_le_sqrt hsquares
  have hsum : 0 ≤ ∑ i : S, |v i| :=
    Finset.sum_nonneg (fun i hi => abs_nonneg (v i))
  unfold signedL1 signedL2
  simpa [sq_abs, Real.sqrt_sq hsum] using hsqrt

/-- Exact `L1` minimum-gain isolation of the residual operator on the
zero-mass signed subspace. -/
structure ZeroSumL1Isolation (P : Matrix S S ℝ) (kappa : ℝ) : Prop where
  kappa_pos : 0 < kappa
  lower : ∀ v : S → ℝ, (∑ s, v s) = 0 →
    kappa * signedL1 v ≤ signedL1 (signedResidual P v)

/-- Standard Euclidean lower-singular/minimum-gain certificate for the
residual operator restricted to the zero-mass signed subspace.

Because `signedL2` is the Euclidean norm, this is the norm inequality delivered
by a positive lower singular value of the restricted operator.  The present
interface records the lower singular **bound** directly; extracting `kappa`
from Mathlib's ordered `LinearMap.singularValues` is a separate adapter layer. -/
structure ZeroSumL2LowerSingularBound
    (P : Matrix S S ℝ) (kappa : ℝ) : Prop where
  kappa_pos : 0 < kappa
  lower : ∀ v : S → ℝ, (∑ s, v s) = 0 →
    kappa * signedL2 v ≤ signedL2 (signedResidual P v)

private theorem signedDifference_sum_zero
    (mu nu : stdSimplex ℝ S) :
    (∑ s, (nu s - mu s)) = 0 := by
  calc
    (∑ s, (nu s - mu s)) = (∑ s, nu s) - (∑ s, mu s) := by
      simp [Finset.sum_sub_distrib]
    _ = 1 - 1 := by
      rw [stdSimplex.sum_eq_one nu, stdSimplex.sum_eq_one mu]
    _ = 0 := by norm_num

private theorem signedResidual_of_stationary_difference
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (muStar nu : stdSimplex ℝ S)
    (hmuStar : step P hP muStar = muStar) :
    signedResidual P (fun s => nu s - muStar s) =
      (step P hP nu).1 - nu.1 := by
  unfold signedResidual
  change Matrix.vecMul (nu.1 - muStar.1) P - (nu.1 - muStar.1) =
    (step P hP nu).1 - nu.1
  rw [Matrix.sub_vecMul]
  have hstarval := congrArg Subtype.val hmuStar
  change Matrix.vecMul muStar.1 P = muStar.1 at hstarval
  rw [hstarval]
  funext s
  change (step P hP nu).1 s - muStar.1 s -
    (nu.1 s - muStar.1 s) = (step P hP nu).1 s - nu.1 s
  ring

private theorem signedL1_difference_eq_two_lawTV
    (mu nu : stdSimplex ℝ S) :
    signedL1 (fun s => nu s - mu s) = 2 * lawTV mu nu := by
  rw [UEOT.V3.FiniteRecurrentDecompositionStability.lawTV_eq_half_sum_abs]
  unfold signedL1
  have habs :
      (∑ s, |nu s - mu s|) = ∑ s, |mu.1 s - nu.1 s| := by
    apply Finset.sum_congr rfl
    intro s hs
    exact abs_sub_comm _ _
  rw [habs]
  ring

private theorem signedL1_residual_eq_two_lawTV
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (muStar nu : stdSimplex ℝ S)
    (hmuStar : step P hP muStar = muStar) :
    signedL1 (signedResidual P (fun s => nu s - muStar s)) =
      2 * lawTV (step P hP nu) nu := by
  rw [signedResidual_of_stationary_difference P hP muStar nu hmuStar]
  rw [UEOT.V3.FiniteRecurrentDecompositionStability.lawTV_eq_half_sum_abs]
  unfold signedL1
  simp only [Pi.sub_apply]
  ring

/-- **Exact TV-geometry isolation theorem.**

An `L1` minimum gain `kappa` of `P - I` on zero-mass signed laws gives a branch
residual inverse with exact constant `1 / kappa`. -/
theorem residualInverse_of_l1Isolation
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (muStar : stdSimplex ℝ S)
    (hmuStar : step P hP muStar = muStar)
    (kappa : ℝ)
    (hiso : ZeroSumL1Isolation P kappa) :
    BranchResidualInverse P hP muStar (1 / kappa) := by
  refine ⟨hmuStar,
    div_nonneg zero_le_one (le_of_lt hiso.kappa_pos), ?_⟩
  intro nu
  let v : S → ℝ := fun s => nu s - muStar s
  have hsum : (∑ s, v s) = 0 := by
    simpa [v] using signedDifference_sum_zero muStar nu
  have hlower := hiso.lower v hsum
  have hvnorm : signedL1 v = 2 * lawTV muStar nu := by
    simpa [v] using signedL1_difference_eq_two_lawTV muStar nu
  have hrnorm : signedL1 (signedResidual P v) =
      2 * lawTV (step P hP nu) nu := by
    simpa [v] using
      signedL1_residual_eq_two_lawTV P hP muStar nu hmuStar
  rw [hvnorm, hrnorm] at hlower
  have hscaled :
      kappa * lawTV muStar nu ≤ lawTV (step P hP nu) nu := by
    nlinarith
  have hform :
      (1 / kappa) * lawTV (step P hP nu) nu =
        lawTV (step P hP nu) nu / kappa := by
    field_simp
  rw [hform]
  apply (le_div_iff₀ hiso.kappa_pos).2
  simpa [mul_comm] using hscaled

/-- **Euclidean lower-singular-bound isolation theorem.**

If the residual operator has Euclidean lower minimum gain `kappa` on the
zero-mass subspace, then it yields a TV residual inverse with the safe finite-
dimensional constant `sqrt(card S) / kappa`. -/
theorem residualInverse_of_l2LowerSingularBound
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (muStar : stdSimplex ℝ S)
    (hmuStar : step P hP muStar = muStar)
    (kappa : ℝ)
    (hiso : ZeroSumL2LowerSingularBound P kappa) :
    BranchResidualInverse P hP muStar
      (Real.sqrt (Fintype.card S) / kappa) := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt (Fintype.card S) :=
    Real.sqrt_nonneg _
  refine ⟨hmuStar,
    div_nonneg hsqrt_nonneg (le_of_lt hiso.kappa_pos), ?_⟩
  intro nu
  let v : S → ℝ := fun s => nu s - muStar s
  let r : S → ℝ := signedResidual P v
  have hsum : (∑ s, v s) = 0 := by
    simpa [v] using signedDifference_sum_zero muStar nu
  have hisol := hiso.lower v hsum
  have hv_l1 : signedL1 v = 2 * lawTV muStar nu := by
    simpa [v] using signedL1_difference_eq_two_lawTV muStar nu
  have hr_l1 : signedL1 r = 2 * lawTV (step P hP nu) nu := by
    simpa [r, v] using
      signedL1_residual_eq_two_lawTV P hP muStar nu hmuStar
  have hvl1_l2 := signedL1_le_sqrt_card_mul_l2 v
  have hrl2_l1 := signedL2_le_signedL1 r
  have hk_nonneg : 0 ≤ kappa := le_of_lt hiso.kappa_pos
  have hchain :
      kappa * signedL1 v ≤
        Real.sqrt (Fintype.card S) * signedL1 r := by
    calc
      kappa * signedL1 v
          ≤ kappa * (Real.sqrt (Fintype.card S) * signedL2 v) :=
        mul_le_mul_of_nonneg_left hvl1_l2 hk_nonneg
      _ = Real.sqrt (Fintype.card S) * (kappa * signedL2 v) := by
        ring
      _ ≤ Real.sqrt (Fintype.card S) * signedL2 r :=
        mul_le_mul_of_nonneg_left hisol hsqrt_nonneg
      _ ≤ Real.sqrt (Fintype.card S) * signedL1 r :=
        mul_le_mul_of_nonneg_left hrl2_l1 hsqrt_nonneg
  rw [hv_l1, hr_l1] at hchain
  have hscaled :
      kappa * lawTV muStar nu ≤
        Real.sqrt (Fintype.card S) * lawTV (step P hP nu) nu := by
    nlinarith
  have hform :
      (Real.sqrt (Fintype.card S) / kappa) *
          lawTV (step P hP nu) nu =
        (Real.sqrt (Fintype.card S) *
          lawTV (step P hP nu) nu) / kappa := by
    field_simp
  rw [hform]
  apply (le_div_iff₀ hiso.kappa_pos).2
  simpa [mul_comm] using hscaled

/-- `L1` isolation implies the requested topology-changing stationary-branch
tracking estimate with exact factor `epsilon / kappa`. -/
theorem l1Isolation_stationary_tracking
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (Q : Matrix S S ℝ) (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (muStar : stdSimplex ℝ S)
    (hmuStar : step P hP muStar = muStar)
    (kappa epsilon : ℝ)
    (hiso : ZeroSumL1Isolation P kappa)
    (hrow : ∀ x, crossRowTV P hP Q hQ x ≤ epsilon) :
    ∃ muhat : stdSimplex ℝ S,
      muhat ∈ invariantLawSet Q hQ ∧
      lawTV muStar muhat ≤ epsilon / kappa := by
  rcases residual_stationary_tracking P hP Q hQ muStar
      (1 / kappa) epsilon
      (residualInverse_of_l1Isolation P hP muStar hmuStar kappa hiso)
      hrow with ⟨muhat, hmuhat, hbound⟩
  refine ⟨muhat, hmuhat, ?_⟩
  calc
    lawTV muStar muhat ≤ (1 / kappa) * epsilon := hbound
    _ = epsilon / kappa := by field_simp

/-- Standard Euclidean lower singular isolation implies topology-changing
stationary-branch tracking with the dimension-safe TV bound
`sqrt(card S) * epsilon / kappa`. -/
theorem l2LowerSingularBound_stationary_tracking
    (P : Matrix S S ℝ) (hP : P ∈ Matrix.rowStochastic ℝ S)
    (Q : Matrix S S ℝ) (hQ : Q ∈ Matrix.rowStochastic ℝ S)
    (muStar : stdSimplex ℝ S)
    (hmuStar : step P hP muStar = muStar)
    (kappa epsilon : ℝ)
    (hiso : ZeroSumL2LowerSingularBound P kappa)
    (hrow : ∀ x, crossRowTV P hP Q hQ x ≤ epsilon) :
    ∃ muhat : stdSimplex ℝ S,
      muhat ∈ invariantLawSet Q hQ ∧
      lawTV muStar muhat ≤
        Real.sqrt (Fintype.card S) * epsilon / kappa := by
  rcases residual_stationary_tracking P hP Q hQ muStar
      (Real.sqrt (Fintype.card S) / kappa) epsilon
      (residualInverse_of_l2LowerSingularBound
        P hP muStar hmuStar kappa hiso)
      hrow with ⟨muhat, hmuhat, hbound⟩
  refine ⟨muhat, hmuhat, ?_⟩
  calc
    lawTV muStar muhat
        ≤ (Real.sqrt (Fintype.card S) / kappa) * epsilon := hbound
    _ = Real.sqrt (Fintype.card S) * epsilon / kappa := by
      field_simp

end


end UEOT.V3.Compression.TopologyChangingGoaSpectralIsolation
