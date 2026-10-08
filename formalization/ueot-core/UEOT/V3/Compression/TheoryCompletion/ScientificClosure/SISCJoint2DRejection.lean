import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.C5DualDriveTest
import Mathlib.Tactic.Linarith

/-!
# SISC C5: exact common-two-dimensional rejection and practical-null separation

The first theorem connects the **same** stacked Jacobian of the Core DDH-04
mechanism to the DDH-05 indexed singular-value perturbation theorem. The
registered-budget coordinates and row normalization cannot be changed between
the rank theorem and spectral measurement. The exact-zero null is distinct
from a separately registered practical tolerance null.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

open UEOT.V3.CommonBottleneckRank
open UEOT.V3.SingularValueEffectiveDimension
open scoped Matrix.Norms.L2Operator

noncomputable section

universe uRow

/-- The 3rd (zero-index 2) singular value of a finite matrix vanishes whenever
the matrix has rank at most two. This is a bridge from *matrix rank* to the
Euclidean response operator used by the perturbation theorem. -/
theorem third_singular_zero_of_rank_le_two
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (S : Matrix m n ℝ) (hRank : S.rank ≤ 2) :
    matrixSingularValue S 2 = 0 := by
  have hRankEq :
      S.rank = Module.finrank ℝ (LinearMap.range (rectangularLin S)) := by
    change S.rank = Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin S))
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    exact Matrix.rank_eq_finrank_range_toLin S
      (EuclideanSpace.basisFun m ℝ).toBasis
      (EuclideanSpace.basisFun n ℝ).toBasis
  have hr : Module.finrank ℝ (LinearMap.range (rectangularLin S)) ≤ 2 := by
    simpa only [← hRankEq] using hRank
  change (rectangularLin S).singularValues 2 = 0
  exact ((rectangularLin S).singularValues_eq_zero_iff_le_finrank_range).2 hr

/-- A *strict* estimated 3rd singular value above the certified operator-norm
error rejects the existence of any common differentiable 2D bottleneck for
this fixed budget and response stack. This is a one-way null rejection. -/
theorem reject_exact_common_twoD_from_same_jacobian
    {Row : Type uRow} [Fintype Row] {k : ℕ}
    (m : Row → Budget k → ℝ) (B : Budget k)
    (Jhat : Matrix Row (Fin k) ℝ) (eta : ℝ)
    (hpert : ‖Jhat - stackedJacobian m B‖ ≤ eta)
    (hreject : eta < matrixSingularValue Jhat 2) :
    ¬ ∃ (z : Budget k → Latent) (g : Row → Latent → ℝ),
        (∀ r x, m r x = g r (z x)) ∧
        DifferentiableAt ℝ z B ∧
        (∀ r, DifferentiableAt ℝ (g r) (z B)) := by
  rintro ⟨z, g, hm, hz, hg⟩
  have hRank := commonTwoDrive_rankNecessary m z g B hm hz hg
  have hzero := third_singular_zero_of_rank_le_two
    (stackedJacobian m B) hRank
  have hsvp := matrixSingularValue_perturbation
    (stackedJacobian m B) Jhat eta hpert 2
  rw [hzero] at hsvp
  have hup := (abs_le.mp hsvp).2
  linarith

/-- Practical spectral null, intentionally weaker than exact 2D mechanism. -/
def PracticalTwoD {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (J : Matrix m n ℝ) (tau0 : ℝ) : Prop :=
  matrixSingularValue J 2 ≤ tau0

/-- Rejection of a declared practical tolerance requires the stronger
`sigmaHat - eta > tau0`, not merely `sigmaHat > eta`. -/
theorem reject_practical_twoD
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (J Jhat : Matrix m n ℝ) (eta tau0 : ℝ)
    (hpert : ‖Jhat - J‖ ≤ eta)
    (hreject : tau0 + eta < matrixSingularValue Jhat 2) :
    ¬ PracticalTwoD J tau0 := by
  intro hnull
  have hsvp := matrixSingularValue_perturbation J Jhat eta hpert 2
  have hu := (abs_le.mp hsvp).2
  dsimp [PracticalTwoD] at hnull
  linarith

end

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
