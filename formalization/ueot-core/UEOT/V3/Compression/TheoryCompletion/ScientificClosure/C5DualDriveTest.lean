import UEOT.V3.CommonBottleneckRank
import UEOT.V3.SingularValueEffectiveDimension
import Mathlib.Tactic.Linarith

/-!
# Scientific Closure C5 — falsifiable common-two-drive test

Core P-DDH-04 already proves the exact necessary rank condition for one common
2D bottleneck at one budget point.  P-DDH-05 already proves singular-value
stability under genuine operator-norm perturbation.  This file adds the missing
three-way scientific decision layer; low effective dimension is only
*compatible* with the necessary condition, never sufficient to identify Π/Φ.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure

open UEOT.V3.CommonBottleneckRank
open UEOT.V3.SingularValueEffectiveDimension
open scoped Matrix.Norms.L2Operator

universe uRow

/-- C5 output vocabulary.  `compatible` means only “not rejected by this
necessary spectral condition”. -/
inductive DualDriveVerdict
  | compatible
  | rejected
  | ambiguous
  deriving DecidableEq, Repr

open DualDriveVerdict

/-- Three-way decision from an estimated third singular value and a registered
operator-norm error radius.  `tau0` is an explicitly registered practical-zero
tolerance. -/
noncomputable def dualDriveDecision
    (sigma3Hat eta tau0 : ℝ) : DualDriveVerdict :=
  if eta < sigma3Hat then rejected
  else if sigma3Hat + eta ≤ tau0 then compatible
  else ambiguous

/-- Matrix singular values inherit the canonical operator-norm perturbation
bound already proved in P-DDH-05 infrastructure. -/
theorem matrixSingularValue_perturbation
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (S Shat : Matrix m n ℝ) (eta : ℝ)
    (hpert : ‖Shat - S‖ ≤ eta) (i : ℕ) :
    |matrixSingularValue Shat i - matrixSingularValue S i| ≤ eta := by
  have hclm := matrixPerturb_to_clmBound Shat S eta hpert
  exact singularValues_lipschitz_of_opNorm_le
    (rectangularLin Shat) (rectangularLin S) eta hclm i

/-- Rejection is sound on the perturbation event: the reference third singular
value is strictly positive. -/
theorem dualDrive_rejected_sound
    (sigma3Hat sigma3True eta tau0 : ℝ)
    (hgood : |sigma3Hat - sigma3True| ≤ eta)
    (h : dualDriveDecision sigma3Hat eta tau0 = rejected) :
    0 < sigma3True := by
  unfold dualDriveDecision at h
  split at h <;> rename_i hrej
  · have hup := (abs_le.mp hgood).2
    linarith
  · split at h <;> simp_all

/-- Compatibility is only a tolerance statement about the true third singular
value.  It does not identify the physical latent variables. -/
theorem dualDrive_compatible_sound
    (sigma3Hat sigma3True eta tau0 : ℝ)
    (hgood : |sigma3Hat - sigma3True| ≤ eta)
    (h : dualDriveDecision sigma3Hat eta tau0 = compatible) :
    sigma3True ≤ tau0 := by
  unfold dualDriveDecision at h
  split at h <;> rename_i hrej
  · simp at h
  · split at h <;> rename_i hcomp
    · have hlo := (abs_le.mp hgood).1
      linarith
    · simp at h

/-- Ambiguous means neither positive-third-singular rejection nor the declared
practical-zero compatibility condition is certified. -/
theorem dualDrive_ambiguous_iff
    (sigma3Hat eta tau0 : ℝ) :
    dualDriveDecision sigma3Hat eta tau0 = ambiguous ↔
      ¬ eta < sigma3Hat ∧ ¬ sigma3Hat + eta ≤ tau0 := by
  unfold dualDriveDecision
  by_cases hrej : eta < sigma3Hat
  · simp [hrej]
  · by_cases hcomp : sigma3Hat + eta ≤ tau0
    · simp [hrej, hcomp]
    · simp [hrej, hcomp]

/-- Direct Scientific-Closure exposure of Core P-DDH-04: one common
2-dimensional differentiable bottleneck at the same budget point imposes rank
at most two on the stacked Jacobian. -/
theorem commonTwoDrive_rankNecessary
    {Row : Type uRow} {k : ℕ}
    (m : Row → Budget k → ℝ)
    (z : Budget k → Latent)
    (g : Row → Latent → ℝ)
    (B : Budget k)
    (hm : ∀ r x, m r x = g r (z x))
    (hz : DifferentiableAt ℝ z B)
    (hg : ∀ r, DifferentiableAt ℝ (g r) (z B)) :
    (stackedJacobian m B).rank ≤ 2 :=
  p_ddh_04 m z g B hm hz hg

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure
