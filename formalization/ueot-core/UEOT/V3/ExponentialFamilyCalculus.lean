import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Tactic.Ring

/-!
# P-DDH-02 — finite exponential-family log-partition calculus

The frozen UEOT Core v3 §23.3 statement is the standard finite exponential
family identity. For a finite state space Γ, a strictly positive baseline
law p0, an arbitrary finite feature dimension k, a prescribed feature map
F : Γ → ℝ^k, and an arbitrary finite natural parameter theta, define

ψ(theta) = log (sum γ, p0(γ) * exp (inner(F(γ), theta))).

The gradient of ψ is the tilted feature mean and its Hessian is the tilted
feature covariance. No rank, feature-independence, strict-convexity,
positive-definite-covariance, or parameter-identifiability hypothesis is used.
In particular k = 0, constant/redundant features, and singular covariance
remain valid.

This module is deliberately standalone from P-DDH-03.
-/

namespace UEOT.V3.ExponentialFamilyCalculus

noncomputable section

open Real
open scoped BigOperators Gradient

universe uΓ

variable {Γ : Type uΓ} [Fintype Γ]

/-- Euclidean natural-parameter / feature space of arbitrary finite
dimension, including dimension zero. -/
abbrev Param (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- Real baseline mass associated with a PMF atom. -/
def baselineWeight (p0 : PMF Γ) (γ : Γ) : ℝ :=
  (p0 γ).toReal

/-- Finite exponential-family score. -/
def score {k : ℕ} (F : Γ → Param k) (theta : Param k) (γ : Γ) : ℝ :=
  inner ℝ (F γ) theta

/-- Exponential-family partition function. -/
def partition {k : ℕ} (p0 : PMF Γ) (F : Γ → Param k) (theta : Param k) : ℝ :=
  ∑ γ, baselineWeight p0 γ * exp (score F theta γ)

/-- Log-partition function ψ. -/
def logPartition {k : ℕ} (p0 : PMF Γ) (F : Γ → Param k) (theta : Param k) : ℝ :=
  log (partition p0 F theta)

/-- Normalized tilted atom weight. -/
def tiltWeight {k : ℕ} (p0 : PMF Γ) (F : Γ → Param k)
    (theta : Param k) (γ : Γ) : ℝ :=
  baselineWeight p0 γ * exp (score F theta γ) / partition p0 F theta

/-- Tilted feature mean. -/
def meanVec {k : ℕ} (p0 : PMF Γ) (F : Γ → Param k)
    (theta : Param k) : Param k :=
  ∑ γ, tiltWeight p0 F theta γ • F γ

/-- Unnormalized derivative of the partition function. -/
def partitionDeriv {k : ℕ} (p0 : PMF Γ) (F : Γ → Param k)
    (theta : Param k) : StrongDual ℝ (Param k) :=
  ∑ γ, baselineWeight p0 γ •
    (exp (score F theta γ) • innerSL ℝ (F γ))

/-- Unnormalized second derivative of the partition function. -/
def partitionSecond {k : ℕ} (p0 : PMF Γ) (F : Γ → Param k)
    (theta : Param k) : Param k →L[ℝ] StrongDual ℝ (Param k) :=
  ∑ γ, baselineWeight p0 γ •
    ((exp (score F theta γ) • innerSL ℝ (F γ)).smulRight
      (innerSL ℝ (F γ)))

/-- Riesz-dual representation of the tilted mean, i.e. the Fréchet derivative
of the log-partition function. -/
def gradientDual {k : ℕ} (p0 : PMF Γ) (F : Γ → Param k)
    (theta : Param k) : StrongDual ℝ (Param k) :=
  (partition p0 F theta)⁻¹ • partitionDeriv p0 F theta

/-- Derivative of the reciprocal partition factor. -/
def invPartitionDeriv {k : ℕ} (p0 : PMF Γ) (F : Γ → Param k)
    (theta : Param k) : StrongDual ℝ (Param k) :=
  (ContinuousLinearMap.toSpanSingleton ℝ (-(partition p0 F theta ^ 2)⁻¹)).comp
    (partitionDeriv p0 F theta)

/-- Raw quotient-rule Hessian before covariance normalization. -/
def hessianRaw {k : ℕ} (p0 : PMF Γ) (F : Γ → Param k)
    (theta : Param k) : Param k →L[ℝ] StrongDual ℝ (Param k) :=
  (partition p0 F theta)⁻¹ • partitionSecond p0 F theta +
    (invPartitionDeriv p0 F theta).smulRight (partitionDeriv p0 F theta)

/-- Tilted covariance as a symmetric bilinear operator. Evaluating this
operator at v and then w gives the covariance bilinear form in directions
v,w. -/
def covarianceDual {k : ℕ} (p0 : PMF Γ) (F : Γ → Param k)
    (theta : Param k) : Param k →L[ℝ] StrongDual ℝ (Param k) :=
  (∑ γ, tiltWeight p0 F theta γ •
      ((innerSL ℝ (F γ)).smulRight (innerSL ℝ (F γ)))) -
    (innerSL ℝ (meanVec p0 F theta)).smulRight
      (innerSL ℝ (meanVec p0 F theta))

lemma baselineWeight_pos
    (p0 : PMF Γ) (hp0 : ∀ γ, 0 < p0 γ) (γ : Γ) :
    0 < baselineWeight p0 γ := by
  exact ENNReal.toReal_pos (ne_of_gt (hp0 γ)) (p0.apply_ne_top γ)

lemma partition_pos {k : ℕ}
    (p0 : PMF Γ) (hp0 : ∀ γ, 0 < p0 γ)
    (F : Γ → Param k) (theta : Param k) :
    0 < partition p0 F theta := by
  letI : Nonempty Γ := ⟨p0.support_nonempty.some⟩
  unfold partition
  exact Finset.sum_pos
    (fun γ _ => mul_pos (baselineWeight_pos p0 hp0 γ) (exp_pos _))
    Finset.univ_nonempty

lemma hasFDerivAt_score {k : ℕ}
    (F : Γ → Param k) (theta : Param k) (γ : Γ) :
    HasFDerivAt (fun x : Param k => score F x γ) (innerSL ℝ (F γ)) theta := by
  simpa [score] using (innerSL ℝ (F γ)).hasFDerivAt

lemma hasFDerivAt_partition {k : ℕ}
    (p0 : PMF Γ) (F : Γ → Param k) (theta : Param k) :
    HasFDerivAt (partition p0 F) (partitionDeriv p0 F theta) theta := by
  change HasFDerivAt
    (fun x : Param k =>
      ∑ γ, baselineWeight p0 γ * exp (score F x γ))
    (∑ γ, baselineWeight p0 γ •
      (exp (score F theta γ) • innerSL ℝ (F γ))) theta
  rw [show
      (fun x : Param k =>
        ∑ γ, baselineWeight p0 γ * exp (score F x γ)) =
        ∑ γ, (fun x : Param k =>
          baselineWeight p0 γ * exp (score F x γ)) by
      funext x
      simp]
  exact HasFDerivAt.sum (u := Finset.univ) (x := theta) (fun γ _ =>
    ((hasFDerivAt_score F theta γ).exp.const_mul (baselineWeight p0 γ)))

lemma hasFDerivAt_logPartition_raw {k : ℕ}
    (p0 : PMF Γ) (hp0 : ∀ γ, 0 < p0 γ)
    (F : Γ → Param k) (theta : Param k) :
    HasFDerivAt (logPartition p0 F)
      ((partition p0 F theta)⁻¹ • partitionDeriv p0 F theta) theta := by
  exact (hasFDerivAt_partition p0 F theta).log
    (ne_of_gt (partition_pos p0 hp0 F theta))

lemma partitionDeriv_eq_partition_smul_meanDual {k : ℕ}
    (p0 : PMF Γ) (F : Γ → Param k) (theta : Param k)
    (hZ : partition p0 F theta ≠ 0) :
    partitionDeriv p0 F theta =
      partition p0 F theta • innerSL ℝ (meanVec p0 F theta) := by
  ext v
  simp only [partitionDeriv, meanVec, tiltWeight, div_eq_mul_inv,
    innerSL_apply_apply, _root_.sum_apply, smul_apply, sum_inner,
    real_inner_smul_left, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro γ hγ
  field_simp [hZ]

lemma gradientDual_eq_meanDual {k : ℕ}
    (p0 : PMF Γ) (F : Γ → Param k) (theta : Param k)
    (hZ : partition p0 F theta ≠ 0) :
    gradientDual p0 F theta = innerSL ℝ (meanVec p0 F theta) := by
  rw [gradientDual, partitionDeriv_eq_partition_smul_meanDual p0 F theta hZ]
  ext v
  simp [hZ]

lemma toDual_symm_innerSL {k : ℕ} (x : Param k) :
    (InnerProductSpace.toDual ℝ (Param k)).symm (innerSL ℝ x) = x := by
  apply (InnerProductSpace.toDual ℝ (Param k)).injective
  simp only [LinearIsometryEquiv.apply_symm_apply]
  rw [InnerProductSpace.toDual_apply_eq_toDualMap_apply]
  rfl

/-- Exact first source identity: the gradient of the finite log-partition is
the tilted feature mean. -/
lemma hasGradientAt_logPartition {k : ℕ}
    (p0 : PMF Γ) (hp0 : ∀ γ, 0 < p0 γ)
    (F : Γ → Param k) (theta : Param k) :
    HasGradientAt (logPartition p0 F) (meanVec p0 F theta) theta := by
  have hZ : partition p0 F theta ≠ 0 :=
    ne_of_gt (partition_pos p0 hp0 F theta)
  have hlog := hasFDerivAt_logPartition_raw p0 hp0 F theta
  rw [partitionDeriv_eq_partition_smul_meanDual p0 F theta hZ] at hlog
  simpa [hZ, toDual_symm_innerSL] using hlog.hasGradientAt

lemma hasFDerivAt_partitionDeriv {k : ℕ}
    (p0 : PMF Γ) (F : Γ → Param k) (theta : Param k) :
    HasFDerivAt (partitionDeriv p0 F) (partitionSecond p0 F theta) theta := by
  change HasFDerivAt
    (fun x : Param k =>
      ∑ γ, baselineWeight p0 γ •
        (exp (score F x γ) • innerSL ℝ (F γ)))
    (∑ γ, baselineWeight p0 γ •
      ((exp (score F theta γ) • innerSL ℝ (F γ)).smulRight
        (innerSL ℝ (F γ)))) theta
  rw [show
      (fun x : Param k =>
        ∑ γ, baselineWeight p0 γ •
          (exp (score F x γ) • innerSL ℝ (F γ))) =
        ∑ γ, (fun x : Param k =>
          baselineWeight p0 γ •
            (exp (score F x γ) • innerSL ℝ (F γ))) by
      funext x
      simp]
  exact HasFDerivAt.sum (u := Finset.univ) (x := theta) (fun γ _ =>
    ((hasFDerivAt_score F theta γ).exp.smul_const
      (innerSL ℝ (F γ))).const_smul (baselineWeight p0 γ))

lemma hasFDerivAt_gradientDual_raw {k : ℕ}
    (p0 : PMF Γ) (F : Γ → Param k) (theta : Param k)
    (hZ : partition p0 F theta ≠ 0) :
    HasFDerivAt (gradientDual p0 F) (hessianRaw p0 F theta) theta := by
  have hInv : HasFDerivAt
      (fun x : Param k => (partition p0 F x)⁻¹)
      (invPartitionDeriv p0 F theta) theta := by
    change HasFDerivAt ((fun y : ℝ => y⁻¹) ∘ partition p0 F) _ theta
    exact (hasFDerivAt_inv hZ).comp theta
      (hasFDerivAt_partition p0 F theta)
  change HasFDerivAt
    ((fun x : Param k => (partition p0 F x)⁻¹) • partitionDeriv p0 F)
    (hessianRaw p0 F theta) theta
  exact hInv.smul (hasFDerivAt_partitionDeriv p0 F theta)

lemma hessianRaw_eq_covarianceDual {k : ℕ}
    (p0 : PMF Γ) (F : Γ → Param k) (theta : Param k)
    (hZ : partition p0 F theta ≠ 0) :
    hessianRaw p0 F theta = covarianceDual p0 F theta := by
  ext v w
  simp only [hessianRaw, covarianceDual, partitionSecond, invPartitionDeriv,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.toSpanSingleton_apply, innerSL_apply_apply]
  rw [partitionDeriv_eq_partition_smul_meanDual p0 F theta hZ]
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply]
  simp [meanVec, tiltWeight, div_eq_mul_inv, hZ, Finset.mul_sum]
  field_simp [hZ]
  ring

/-- Exact second source identity: differentiating the Riesz-dual gradient gives
the tilted covariance bilinear operator, i.e. the Hessian of the log-partition. -/
lemma hasFDerivAt_gradientDual_covariance {k : ℕ}
    (p0 : PMF Γ) (hp0 : ∀ γ, 0 < p0 γ)
    (F : Γ → Param k) (theta : Param k) :
    HasFDerivAt (gradientDual p0 F) (covarianceDual p0 F theta) theta := by
  have hZ : partition p0 F theta ≠ 0 :=
    ne_of_gt (partition_pos p0 hp0 F theta)
  rw [← hessianRaw_eq_covarianceDual p0 F theta hZ]
  exact hasFDerivAt_gradientDual_raw p0 F theta hZ

/-- Source-facing P-DDH-02.

For arbitrary finite Γ, strictly positive baseline PMF p0, arbitrary finite
dimension k (including k = 0), prescribed F, and arbitrary finite parameter
theta, the log-partition gradient is exactly the tilted mean and its Hessian
is exactly the tilted covariance operator E[F Fᵀ] - E[F]E[F]ᵀ.
-/
theorem p_ddh_02 {k : ℕ}
    (p0 : PMF Γ) (hp0 : ∀ γ, 0 < p0 γ)
    (F : Γ → Param k) (theta : Param k) :
    HasGradientAt (logPartition p0 F) (meanVec p0 F theta) theta ∧
      HasFDerivAt (gradientDual p0 F)
        (covarianceDual p0 F theta) theta := by
  exact ⟨
    hasGradientAt_logPartition p0 hp0 F theta,
    hasFDerivAt_gradientDual_covariance p0 hp0 F theta⟩

end

end UEOT.V3.ExponentialFamilyCalculus
