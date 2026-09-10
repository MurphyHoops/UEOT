import UEOT.V3.CTMCSemigroup
import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
# P-DYN-02 source-facing nonnegative-time CTMC semigroup criterion

A CTMC is a one-sided semigroup in probabilistic time.  This module removes the
stronger all-real-time hypothesis used by the algebraic helper and formalizes
the manuscript's zero-time argument as uniqueness of the right derivative on
`Ici 0`.
-/

namespace UEOT.V3.CTMCSemigroupNonnegative

noncomputable section

open Matrix NormedSpace Set Filter
open UEOT.V3.CTMCLumpability
open UEOT.V3.CTMCSemigroup
open scoped Matrix.Norms.Frobenius

universe uX uB

variable {X : Type uX} {B : Type uB}
variable [Fintype X] [Fintype B]

local instance : DecidableEq X := Classical.decEq X
local instance : DecidableEq B := Classical.decEq B

/-- A nonnegative-time semigroup intertwining already determines the generator.
This is the literal right-derivative version of the source proof. -/
theorem generator_intertwines_of_semigroup_nonneg
    (L : Matrix X X ℝ) (Lbar : Matrix B B ℝ) (block : X → B)
    (hsem : ∀ t : ℝ, 0 ≤ t →
      NormedSpace.exp (t • L) * blockIndicator block =
        blockIndicator block * NormedSpace.exp (t • Lbar)) :
    L * blockIndicator block = blockIndicator block * Lbar := by
  let R := rightMulIndicatorCLM block
  let S := leftMulIndicatorCLM block
  have hL := hasDerivAt_exp_smul_const L (0 : ℝ)
  have hR := hasDerivAt_exp_smul_const Lbar (0 : ℝ)
  have hleftD :
      HasDerivWithinAt
        (R ∘ fun t : ℝ => NormedSpace.exp (t • L))
        (R L) (Ici 0) 0 :=
    (R.hasFDerivAt.comp_hasDerivAt 0 hL).hasDerivWithinAt
  have hrightD :
      HasDerivWithinAt
        (S ∘ fun t : ℝ => NormedSpace.exp (t • Lbar))
        (S Lbar) (Ici 0) 0 :=
    (S.hasFDerivAt.comp_hasDerivAt 0 hR).hasDerivWithinAt
  have hEqOn :
      Set.EqOn
        (S ∘ fun t : ℝ => NormedSpace.exp (t • Lbar))
        (R ∘ fun t : ℝ => NormedSpace.exp (t • L))
        (Ici 0) := by
    intro t ht
    simpa [R, S] using (hsem t ht).symm
  have heq :
      (S ∘ fun t : ℝ => NormedSpace.exp (t • Lbar)) =ᶠ[nhdsWithin 0 (Ici 0)]
        (R ∘ fun t : ℝ => NormedSpace.exp (t • L)) :=
    hEqOn.eventuallyEq_of_mem self_mem_nhdsWithin
  have hleftAsRight :=
    hleftD.congr_of_eventuallyEq_of_mem heq Set.self_mem_Ici
  have hderivEq : S Lbar = R L :=
    (uniqueDiffOn_Ici (0 : ℝ) 0 Set.self_mem_Ici).eq_deriv
      (Ici 0) hleftAsRight hrightD
  dsimp [R, S] at hderivEq
  exact hderivEq.symm

/-- Exact finite-CTMC semigroup quotient for nonnegative times is equivalent
to generator intertwining. -/
theorem semigroup_nonneg_intertwines_iff_generator
    (L : Matrix X X ℝ) (Lbar : Matrix B B ℝ) (block : X → B) :
    (∀ t : ℝ, 0 ≤ t →
      NormedSpace.exp (t • L) * blockIndicator block =
        blockIndicator block * NormedSpace.exp (t • Lbar)) ↔
      L * blockIndicator block = blockIndicator block * Lbar := by
  constructor
  · exact generator_intertwines_of_semigroup_nonneg L Lbar block
  · intro h t ht
    exact semigroup_intertwines_of_generator L Lbar block h t

/-- Literal block-sum criterion of P-DYN-02 at CTMC time `t ≥ 0`. -/
theorem p_dyn_02_nonnegative_semigroup_iff_blockSum
    (L : Matrix X X ℝ) (Lbar : Matrix B B ℝ) (block : X → B) :
    (∀ t : ℝ, 0 ≤ t →
      NormedSpace.exp (t • L) * blockIndicator block =
        blockIndicator block * NormedSpace.exp (t • Lbar)) ↔
      ∀ x b, blockSum L block x b = Lbar (block x) b :=
  (semigroup_nonneg_intertwines_iff_generator L Lbar block).trans
    (generator_intertwines_iff_blockSum L Lbar block)

/-- Full existence direction in the source: fiber-constant block sums of a
microscopic CTMC generator define a genuine macroscopic CTMC generator whose
nonnegative-time semigroup is the exact quotient. -/
theorem exists_macro_ctmc_semigroup_of_blockSum_constant
    (L : Matrix X X ℝ) (block : X → B)
    (hsurj : Function.Surjective block)
    (hgen : IsCTMCGenerator L)
    (hconst : ∀ {x x'}, block x = block x' →
      ∀ b, blockSum L block x b = blockSum L block x' b) :
    ∃ Lbar : Matrix B B ℝ,
      IsCTMCGenerator Lbar ∧
      ∀ t : ℝ, 0 ≤ t →
        NormedSpace.exp (t • L) * blockIndicator block =
          blockIndicator block * NormedSpace.exp (t • Lbar) := by
  obtain ⟨Lbar, hinter, hbar⟩ :=
    exists_macro_ctmcGenerator_of_blockSum_constant L block hsurj hgen hconst
  refine ⟨Lbar, hbar, ?_⟩
  intro t ht
  exact semigroup_intertwines_of_generator L Lbar block hinter t

end

end UEOT.V3.CTMCSemigroupNonnegative
