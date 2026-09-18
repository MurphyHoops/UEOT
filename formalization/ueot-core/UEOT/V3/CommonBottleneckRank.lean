import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-!
# P-DDH-04 — common two-dimensional bottleneck

Frozen UEOT Core v3 §23.4 assumes that, in fixed budget coordinates and across
all environments being compared, the responses factor through one common
differentiable two-dimensional bottleneck

`m_e(B) = g_e(z(B))`, with `z(B) ∈ ℝ²`.

At one fixed budget point `B`, the chain rule therefore factors every response
Jacobian through the *same* derivative `Dz(B)`.  After all response coordinates
are stacked vertically, the whole Jacobian still factors as

`J_stack(B) = A(B) * Dz(B)`,

where `A(B)` has exactly two columns.  Hence its genuine matrix rank is at most
two.  The theorem below deliberately concerns one budget point only: derivatives
at different budget points may have different two-dimensional tangent
subspaces, exactly as warned in the frozen source.

The type `Row` indexes all scalar response coordinates in the vertical stack. A
finite collection of vector-valued environments can therefore be represented by
flattening `(environment, output-coordinate)` into `Row`; the proof itself does
not need finiteness of the row index because the common factor has only two
columns.
-/

namespace UEOT.V3.CommonBottleneckRank

noncomputable section

variable {Row : Type*}
variable {k : ℕ}

/-- Fixed budget-coordinate space with `k` real coordinates. -/
abbrev Budget (k : ℕ) := Fin k → ℝ

/-- The common two-dimensional latent/bottleneck space from H-DDH. -/
abbrev Latent := Fin 2 → ℝ

/-- Stack all scalar response coordinates into one vector-valued response. -/
def stackedResponse (m : Row → Budget k → ℝ) : Budget k → Row → ℝ :=
  fun B r => m r B

/-- A response stack generated through one common two-dimensional bottleneck. -/
def bottleneckResponse
    (z : Budget k → Latent) (g : Row → Latent → ℝ) : Budget k → Row → ℝ :=
  fun B r => g r (z B)

/-- The vertically stacked Jacobian, represented in the standard coordinate
bases.  Its rows are all response coordinates and its columns are the budget
coordinates. -/
def stackedJacobian (m : Row → Budget k → ℝ) (B : Budget k) :
    Matrix Row (Fin k) ℝ :=
  LinearMap.toMatrix' (fderiv ℝ (stackedResponse m) B).toLinearMap

/-- The derivative of all outer response maps `g_r`, stacked as one continuous
linear map out of the shared two-dimensional latent space. -/
def outerDerivative (g : Row → Latent → ℝ) (zB : Latent) :
    Latent →L[ℝ] (Row → ℝ) :=
  ContinuousLinearMap.pi fun r => fderiv ℝ (g r) zB

/-- Chain-rule factorization before choosing matrix coordinates.  Crucially,
every row uses the same right factor `fderiv ℝ z B`. -/
theorem fderiv_bottleneckResponse
    (z : Budget k → Latent) (g : Row → Latent → ℝ) (B : Budget k)
    (hz : DifferentiableAt ℝ z B)
    (hg : ∀ r, DifferentiableAt ℝ (g r) (z B)) :
    fderiv ℝ (bottleneckResponse z g) B =
      (outerDerivative g (z B)).comp (fderiv ℝ z B) := by
  have hstack : HasFDerivAt (bottleneckResponse z g)
      (ContinuousLinearMap.pi fun r =>
        (fderiv ℝ (g r) (z B)).comp (fderiv ℝ z B)) B := by
    apply hasFDerivAt_pi.mpr
    intro r
    simpa [bottleneckResponse, Function.comp_def] using
      (hg r).hasFDerivAt.comp B hz.hasFDerivAt
  have hfactor :
      (ContinuousLinearMap.pi fun r =>
          (fderiv ℝ (g r) (z B)).comp (fderiv ℝ z B)) =
        (outerDerivative g (z B)).comp (fderiv ℝ z B) := by
    ext v r
    rfl
  rw [← hfactor]
  exact hstack.fderiv

/-- Matrix form of the common-bottleneck chain rule:
`J_stack = A * Dz`, where `A` has two columns. -/
theorem bottleneckJacobian_factorization
    (z : Budget k → Latent) (g : Row → Latent → ℝ) (B : Budget k)
    (hz : DifferentiableAt ℝ z B)
    (hg : ∀ r, DifferentiableAt ℝ (g r) (z B)) :
    LinearMap.toMatrix'
        (fderiv ℝ (bottleneckResponse z g) B).toLinearMap =
      LinearMap.toMatrix' (outerDerivative g (z B)).toLinearMap *
        LinearMap.toMatrix' (fderiv ℝ z B).toLinearMap := by
  rw [fderiv_bottleneckResponse z g B hz hg]
  rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.toMatrix'_comp]

/-- Source-facing P-DDH-04.

If all stacked response coordinates factor through the same differentiable
`ℝ²` bottleneck in the fixed budget coordinates, then at the same budget point
the vertically stacked response Jacobian has matrix rank at most two.

No conclusion is made about stacking derivatives from different budget points,
and no assumption that merely gives each environment its own rank-two
factorization is accepted here: the common `z` is explicit in the hypotheses. -/
theorem p_ddh_04
    (m : Row → Budget k → ℝ)
    (z : Budget k → Latent)
    (g : Row → Latent → ℝ)
    (B : Budget k)
    (hm : ∀ r x, m r x = g r (z x))
    (hz : DifferentiableAt ℝ z B)
    (hg : ∀ r, DifferentiableAt ℝ (g r) (z B)) :
    (stackedJacobian m B).rank ≤ 2 := by
  have hresponse : stackedResponse m = bottleneckResponse z g := by
    funext x r
    exact hm r x
  unfold stackedJacobian
  rw [hresponse]
  rw [bottleneckJacobian_factorization z g B hz hg]
  have houter :
      (LinearMap.toMatrix' (outerDerivative g (z B)).toLinearMap).rank ≤
        Fintype.card (Fin 2) :=
    Matrix.rank_le_card_width _
  exact (Matrix.rank_mul_le_left _ _).trans (by simpa using houter)

end

end UEOT.V3.CommonBottleneckRank
