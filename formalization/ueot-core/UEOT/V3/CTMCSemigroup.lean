import UEOT.V3.CTMCLumpability
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# P-DYN-02 analytic bridge — generator intertwining to CTMC semigroup intertwining

The algebraic foundation proves `L^n F = F Lbar^n`.  This file passes that
identity through the matrix exponential.  A Frobenius norm is opened only
locally so that the heterogeneous left/right multiplication maps are continuous
and hence commute with convergent `tsum`s.  The theorem statement is purely
algebraic and does not depend on that norm choice.
-/

namespace UEOT.V3.CTMCSemigroup

noncomputable section

open Matrix
open NormedSpace
open UEOT.V3.CTMCLumpability
open scoped Nat Matrix.Norms.Frobenius

universe uX uB

variable {X : Type uX} {B : Type uB}
variable [Fintype X] [Fintype B]

local instance : DecidableEq X := Classical.decEq X
local instance : DecidableEq B := Classical.decEq B

/-- Right multiplication by the rectangular partition indicator, bundled as
a continuous linear map on the finite-dimensional real matrix space. -/
noncomputable def rightMulIndicatorCLM (block : X → B) :
    Matrix X X ℝ →L[ℝ] Matrix X B ℝ :=
  LinearMap.toContinuousLinearMap
    (mulRightLinearMap X ℝ (blockIndicator block))

/-- Left multiplication by the rectangular partition indicator. -/
noncomputable def leftMulIndicatorCLM (block : X → B) :
    Matrix B B ℝ →L[ℝ] Matrix X B ℝ :=
  LinearMap.toContinuousLinearMap
    (mulLeftLinearMap B ℝ (blockIndicator block))

@[simp] theorem rightMulIndicatorCLM_apply
    (block : X → B) (A : Matrix X X ℝ) :
    rightMulIndicatorCLM block A = A * blockIndicator block := rfl

@[simp] theorem leftMulIndicatorCLM_apply
    (block : X → B) (A : Matrix B B ℝ) :
    leftMulIndicatorCLM block A = blockIndicator block * A := rfl

/-- Generator intertwining propagates through the full matrix exponential. -/
theorem exp_intertwines
    (L : Matrix X X ℝ) (Lbar : Matrix B B ℝ) (block : X → B)
    (h : L * blockIndicator block = blockIndicator block * Lbar) :
    NormedSpace.exp L * blockIndicator block =
      blockIndicator block * NormedSpace.exp Lbar := by
  let R := rightMulIndicatorCLM block
  let S := leftMulIndicatorCLM block
  have hsumL :
      Summable (fun n : ℕ => (n.factorial⁻¹ : ℝ) • L ^ n) :=
    NormedSpace.expSeries_summable' (𝕂 := ℝ) L
  have hsumB :
      Summable (fun n : ℕ => (n.factorial⁻¹ : ℝ) • Lbar ^ n) :=
    NormedSpace.expSeries_summable' (𝕂 := ℝ) Lbar
  have hexpL :
      NormedSpace.exp L = ∑' n : ℕ, (n.factorial⁻¹ : ℝ) • L ^ n := by
    exact congrFun (NormedSpace.exp_eq_tsum ℝ) L
  have hexpB :
      NormedSpace.exp Lbar = ∑' n : ℕ, (n.factorial⁻¹ : ℝ) • Lbar ^ n := by
    exact congrFun (NormedSpace.exp_eq_tsum ℝ) Lbar
  change R (NormedSpace.exp L) = S (NormedSpace.exp Lbar)
  rw [hexpL, hexpB, R.map_tsum hsumL, S.map_tsum hsumB]
  apply tsum_congr
  intro n
  change
    ((n.factorial⁻¹ : ℝ) • L ^ n) * blockIndicator block =
      blockIndicator block * ((n.factorial⁻¹ : ℝ) • Lbar ^ n)
  rw [Matrix.smul_mul, Matrix.mul_smul,
    CTMCLumpability.pow_intertwines L Lbar block h n]

/-- Time-scaled generator intertwining. -/
theorem smul_generator_intertwines
    (L : Matrix X X ℝ) (Lbar : Matrix B B ℝ) (block : X → B)
    (h : L * blockIndicator block = blockIndicator block * Lbar)
    (t : ℝ) :
    (t • L) * blockIndicator block =
      blockIndicator block * (t • Lbar) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, h]

/-- Source-facing reverse implication of P-DYN-02: the block-sum/generator
criterion gives the exact finite CTMC semigroup quotient at every time. -/
theorem semigroup_intertwines_of_generator
    (L : Matrix X X ℝ) (Lbar : Matrix B B ℝ) (block : X → B)
    (h : L * blockIndicator block = blockIndicator block * Lbar) :
    ∀ t : ℝ,
      NormedSpace.exp (t • L) * blockIndicator block =
        blockIndicator block * NormedSpace.exp (t • Lbar) := by
  intro t
  exact exp_intertwines (t • L) (t • Lbar) block
    (smul_generator_intertwines L Lbar block h t)

end

end UEOT.V3.CTMCSemigroup
