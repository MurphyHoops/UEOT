import UEOT.V3.CTMCLumpability
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Exponential
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

/-- Scalar matrix-entry readout of right multiplication.  Using a real-valued
codomain avoids exposing the norm/topology instance chosen for the rectangular
matrix space in derivative uniqueness. -/
noncomputable def rightMulEntryCLM
    (block : X → B) (x : X) (b : B) : Matrix X X ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => (A * blockIndicator block) x b
      map_add' := by
        intro A C
        rw [Matrix.add_mul]
        rfl
      map_smul' := by
        intro c A
        rw [Matrix.smul_mul]
        rfl }

/-- Scalar matrix-entry readout of left multiplication. -/
noncomputable def leftMulEntryCLM
    (block : X → B) (x : X) (b : B) : Matrix B B ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => (blockIndicator block * A) x b
      map_add' := by
        intro A C
        rw [Matrix.mul_add]
        rfl
      map_smul' := by
        intro c A
        rw [Matrix.mul_smul]
        rfl }

@[simp] theorem rightMulEntryCLM_apply
    (block : X → B) (x : X) (b : B) (A : Matrix X X ℝ) :
    rightMulEntryCLM block x b A = (A * blockIndicator block) x b := rfl

@[simp] theorem leftMulEntryCLM_apply
    (block : X → B) (x : X) (b : B) (A : Matrix B B ℝ) :
    leftMulEntryCLM block x b A = (blockIndicator block * A) x b := rfl

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

/-- Algebraic forward implication: an exact exponential intertwining for all
real times forces generator intertwining.  The proof differentiates each
matrix coordinate as an `ℝ`-valued function, so derivative uniqueness is
independent of the auxiliary norm instance on rectangular matrices. -/
theorem generator_intertwines_of_semigroup
    (L : Matrix X X ℝ) (Lbar : Matrix B B ℝ) (block : X → B)
    (hsem : ∀ t : ℝ,
      NormedSpace.exp (t • L) * blockIndicator block =
        blockIndicator block * NormedSpace.exp (t • Lbar)) :
    L * blockIndicator block =
      blockIndicator block * Lbar := by
  ext x b
  have hL := hasDerivAt_exp_smul_const L (0 : ℝ)
  have hR := hasDerivAt_exp_smul_const Lbar (0 : ℝ)
  have hleftD :=
    (rightMulEntryCLM block x b).hasFDerivAt.comp_hasDerivAt 0 hL
  have hrightD :=
    (leftMulEntryCLM block x b).hasFDerivAt.comp_hasDerivAt 0 hR
  have hfun :
      ((rightMulEntryCLM block x b) ∘
          fun t : ℝ => NormedSpace.exp (t • L)) =
        ((leftMulEntryCLM block x b) ∘
          fun t : ℝ => NormedSpace.exp (t • Lbar)) := by
    funext t
    exact congrArg (fun A : Matrix X B ℝ => A x b) (hsem t)
  have heq :
      ((leftMulEntryCLM block x b) ∘
          fun t : ℝ => NormedSpace.exp (t • Lbar)) =ᶠ[nhds 0]
        ((rightMulEntryCLM block x b) ∘
          fun t : ℝ => NormedSpace.exp (t • L)) :=
    Filter.Eventually.of_forall fun t => (congrFun hfun t).symm
  have hleftAsRight := hleftD.congr_of_eventuallyEq heq
  have hderivEq := hleftAsRight.unique hrightD
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at hderivEq
  unfold rightMulEntryCLM leftMulEntryCLM at hderivEq
  change (L * blockIndicator block) x b =
    (blockIndicator block * Lbar) x b at hderivEq
  exact hderivEq

/-- Exact all-real exponential quotient is equivalent to generator
intertwining.  This algebraic helper is stronger in its time-domain hypothesis
than the probabilistic CTMC semigroup statement in Core v3. -/
theorem semigroup_intertwines_iff_generator
    (L : Matrix X X ℝ) (Lbar : Matrix B B ℝ) (block : X → B) :
    (∀ t : ℝ,
      NormedSpace.exp (t • L) * blockIndicator block =
        blockIndicator block * NormedSpace.exp (t • Lbar)) ↔
      L * blockIndicator block = blockIndicator block * Lbar :=
  ⟨generator_intertwines_of_semigroup L Lbar block,
    semigroup_intertwines_of_generator L Lbar block⟩

/-- Algebraic all-real block-sum criterion.  A separate source-facing wrapper
must use nonnegative CTMC semigroup time before P-DYN-02 is promoted. -/
theorem p_dyn_02_semigroup_iff_blockSum
    (L : Matrix X X ℝ) (Lbar : Matrix B B ℝ) (block : X → B) :
    (∀ t : ℝ,
      NormedSpace.exp (t • L) * blockIndicator block =
        blockIndicator block * NormedSpace.exp (t • Lbar)) ↔
      ∀ x b, blockSum L block x b = Lbar (block x) b :=
  (semigroup_intertwines_iff_generator L Lbar block).trans
    (CTMCLumpability.generator_intertwines_iff_blockSum L Lbar block)

end

end UEOT.V3.CTMCSemigroup
