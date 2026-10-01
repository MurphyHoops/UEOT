import UEOT.V3.Compression.TopologyChangingGoaDobrushinL1Bridge
import UEOT.V3.Compression.TopologyChangingGoaResidualInverseStability

/-!
# Strict separation between Dobrushin mixing and residual isolation

The preceding Track-S bridge proved that strict Dobrushin contraction implies a
positive direct-L1 residual certificate.  This module proves that the converse
fails, using the already merged deterministic two-state flip witness.

For that stochastic kernel the global Dobrushin coefficient is exactly one, so
no strict one-step Dobrushin contraction is available.  Nevertheless every
zero-total-mass signed vector has residual exactly `-2v`.  Hence `kappa = 2`
is a valid direct-L1 isolation certificate, the canonical residual conorm is
strictly positive, and the canonical stationary-law tracking theorem remains
available.

This is a separation theorem only.  It does not claim that every nonmixing
kernel has positive residual conorm, nor that the lower bound proved here is a
classification of all such kernels.
-/

namespace UEOT.V3.Compression.TopologyChangingGoaDobrushinSeparation

open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open UEOT.V3.Compression.TopologyChangingGoaSpectralIsolation
open UEOT.V3.Compression.TopologyChangingGoaRestrictedResidualAdapter
open UEOT.V3.Compression.TopologyChangingGoaL1ResidualAdapter
open UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm
open UEOT.V3.Compression.TopologyChangingGoaResidualInverseStability

noncomputable section

local instance separationDecidableEq : DecidableEq (Fin 2) :=
  Classical.decEq (Fin 2)

local instance separationMeasurableSpace : MeasurableSpace (Fin 2) := ⊤

/-- The two deterministic flip rows are maximally separated in total variation. -/
theorem residualWitness_rowTV_zero_one :
    rowTV residualWitnessKernel residualWitnessKernel_stochastic 0 1 = 1 := by
  unfold rowTV UEOT.V3.FiniteDiscountedControl.FiniteProbabilityRow.tvDist
  rw [UEOT.V3.FiniteRecurrentDecompositionStability.pmf_tv_eq_half_sum_abs]
  simp_rw [rowPMF_toReal]
  rw [Fin.sum_univ_two]
  norm_num [residualWitnessKernel]

/-- Every finite stochastic-kernel row distance is at most one. -/
theorem residualWitness_dobrushinAlpha_le_one :
    dobrushinAlpha residualWitnessKernel residualWitnessKernel_stochastic ≤ 1 := by
  unfold dobrushinAlpha
  apply Finset.sup'_le
  intro z hz
  unfold rowTV UEOT.V3.FiniteDiscountedControl.FiniteProbabilityRow.tvDist
  exact UEOT.V3.TotalVariation.tvDist_le_one _ _

/-- The deterministic flip is exactly noncontractive in global Dobrushin TV. -/
theorem residualWitness_dobrushinAlpha_eq_one :
    dobrushinAlpha residualWitnessKernel residualWitnessKernel_stochastic = 1 := by
  apply le_antisymm residualWitness_dobrushinAlpha_le_one
  have h := rowTV_le_dobrushinAlpha
    residualWitnessKernel residualWitnessKernel_stochastic
      (0 : Fin 2) (1 : Fin 2)
  rw [residualWitness_rowTV_zero_one] at h
  exact h

lemma residualWitness_vecMul_coords (v : Fin 2 → ℝ) :
    Matrix.vecMul v residualWitnessKernel 0 = v 1 ∧
      Matrix.vecMul v residualWitnessKernel 1 = v 0 := by
  constructor <;> rw [Matrix.vecMul_apply_eq_sum, Fin.sum_univ_two] <;>
    norm_num [residualWitnessKernel]

/-- On the zero-total-mass signed space, the flip residual is exactly `-2I`. -/
theorem residualWitness_signedResidual_eq_neg_two
    (v : Fin 2 → ℝ) (hv : (∑ s, v s) = 0) :
    signedResidual residualWitnessKernel v = fun s => -2 * v s := by
  rw [Fin.sum_univ_two] at hv
  rcases residualWitness_vecMul_coords v with ⟨h0, h1⟩
  funext s
  unfold signedResidual
  fin_cases s
  · change Matrix.vecMul v residualWitnessKernel 0 - v 0 = -2 * v 0
    rw [h0]
    linarith
  · change Matrix.vecMul v residualWitnessKernel 1 - v 1 = -2 * v 1
    rw [h1]
    linarith

/-- Consequently the signed-L1 residual gain is exactly two. -/
theorem residualWitness_signedL1_residual_eq_two
    (v : Fin 2 → ℝ) (hv : (∑ s, v s) = 0) :
    signedL1 (signedResidual residualWitnessKernel v) = 2 * signedL1 v := by
  rw [residualWitness_signedResidual_eq_neg_two v hv]
  unfold signedL1
  calc
    (∑ s, |-2 * v s|) = ∑ s, 2 * |v s| := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [abs_mul]
      norm_num
    _ = 2 * ∑ s, |v s| := by
      rw [Finset.mul_sum]

/-- The deterministic flip has the positive direct-L1 isolation certificate
`kappa = 2`, despite having no strict Dobrushin contraction margin. -/
theorem residualWitness_l1Isolation_two :
    ZeroSumL1Isolation residualWitnessKernel 2 := by
  refine ⟨by norm_num, ?_⟩
  intro v hv
  rw [residualWitness_signedL1_residual_eq_two v hv]

/-- The canonical direct-L1 conorm retains at least the exact witness gain two. -/
theorem residualWitness_two_le_l1ResidualConorm :
    (2 : ℝ) ≤ l1ResidualConorm residualWitnessKernel := by
  exact l1Isolation_le_l1ResidualConorm
    residualWitnessKernel (by norm_num) 2 residualWitness_l1Isolation_two

theorem residualWitness_l1ResidualConorm_pos :
    0 < l1ResidualConorm residualWitnessKernel := by
  have h := residualWitness_two_le_l1ResidualConorm
  linarith

theorem residualWitness_not_dobrushin_contractive :
    ¬ dobrushinAlpha residualWitnessKernel residualWitnessKernel_stochastic < 1 := by
  rw [residualWitness_dobrushinAlpha_eq_one]
  exact lt_irrefl 1

/-- Main separation: strict Dobrushin mixing is sufficient but not necessary for
positive canonical direct-L1 residual isolation. -/
theorem positive_l1ResidualConorm_without_strict_dobrushin :
    (¬ dobrushinAlpha residualWitnessKernel residualWitnessKernel_stochastic < 1) ∧
      0 < l1ResidualConorm residualWitnessKernel := by
  exact ⟨residualWitness_not_dobrushin_contractive,
    residualWitness_l1ResidualConorm_pos⟩

/-- Even at Dobrushin coefficient one, the canonical residual-conorm route still
provides stationary-law perturbation tracking around the flip's selected
stationary branch. -/
theorem residualWitness_canonical_l1_stationary_tracking
    (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (hQ : Q ∈ Matrix.rowStochastic ℝ (Fin 2))
    (epsilon : ℝ)
    (hrow : ∀ x, crossRowTV
      residualWitnessKernel residualWitnessKernel_stochastic Q hQ x ≤ epsilon) :
    ∃ muhat : stdSimplex ℝ (Fin 2),
      muhat ∈ invariantLawSet Q hQ ∧
      lawTV residualWitnessLaw muhat ≤
        epsilon / l1ResidualConorm residualWitnessKernel := by
  have hiso := residualWitness_l1Isolation_two
  have hinj1 : Function.Injective
      (zeroSumResidualL1Linear residualWitnessKernel) :=
    l1_restricted_injective_of_l1Isolation residualWitnessKernel 2 hiso
  have hinj : Function.Injective
      (zeroSumResidualLinear residualWitnessKernel) :=
    l2_restricted_injective_of_l1_restricted_injective
      residualWitnessKernel hinj1
  exact canonical_l1_stationary_tracking
    residualWitnessKernel residualWitnessKernel_stochastic
    Q hQ residualWitnessLaw residualWitnessLaw_invariant
    epsilon (by norm_num) hinj hrow

end

end UEOT.V3.Compression.TopologyChangingGoaDobrushinSeparation
