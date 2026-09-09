import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

/-!
# P-DYN-02 foundation — finite CTMC block-generator quotient

For a finite state space X and finite block space B, a partition map
`block : X → B` determines the indicator matrix F.  The source block-sum
criterion is exactly the matrix intertwining equation

  L * F = F * Lbar.

This module proves that finite algebraic equivalence and constructs the macro
matrix from fiber-constant block sums.  The matrix-exponential/semigroup bridge
is the next layer and is not claimed here.
-/

namespace UEOT.V3.CTMCLumpability

open Matrix

universe uX uB

variable {X : Type uX} {B : Type uB}
variable [Fintype X] [Fintype B] [DecidableEq B]

/-- Partition indicator matrix. -/
def blockIndicator (block : X → B) : Matrix X B ℝ :=
  fun x b => if block x = b then 1 else 0

/-- Total generator rate from microscopic state x into macro block b. -/
def blockSum (L : Matrix X X ℝ) (block : X → B) (x : X) (b : B) : ℝ :=
  ∑ y : X, if block y = b then L x y else 0

theorem mul_blockIndicator_apply
    (L : Matrix X X ℝ) (block : X → B) (x : X) (b : B) :
    (L * blockIndicator block) x b = blockSum L block x b := by
  classical
  simp [Matrix.mul_apply, blockIndicator, blockSum]

theorem blockIndicator_mul_apply
    (block : X → B) (Lbar : Matrix B B ℝ) (x : X) (b : B) :
    (blockIndicator block * Lbar) x b = Lbar (block x) b := by
  classical
  simp [Matrix.mul_apply, blockIndicator]

/-- The source block-sum criterion is exactly generator intertwining by the
partition indicator matrix. -/
theorem generator_intertwines_iff_blockSum
    (L : Matrix X X ℝ) (Lbar : Matrix B B ℝ) (block : X → B) :
    L * blockIndicator block = blockIndicator block * Lbar ↔
      ∀ x b, blockSum L block x b = Lbar (block x) b := by
  constructor
  · intro h x b
    have hx := congrFun (congrFun h x) b
    simpa [mul_blockIndicator_apply, blockIndicator_mul_apply] using hx
  · intro h
    ext x b
    rw [mul_blockIndicator_apply, blockIndicator_mul_apply]
    exact h x b

/-- Intertwining forces every block sum to be constant along each microscopic
fiber of the partition. -/
theorem blockSum_constant_on_fibers
    (L : Matrix X X ℝ) (Lbar : Matrix B B ℝ) (block : X → B)
    (h : L * blockIndicator block = blockIndicator block * Lbar) :
    ∀ {x x'}, block x = block x' →
      ∀ b, blockSum L block x b = blockSum L block x' b := by
  intro x x' hxx b
  have hs := (generator_intertwines_iff_blockSum L Lbar block).1 h
  rw [hs x b, hs x' b, hxx]

/-- Conversely, if every block sum is constant on partition fibers and the
partition is surjective, those common values define a macro matrix that
intertwines the generator exactly. -/
theorem exists_macro_of_blockSum_constant
    (L : Matrix X X ℝ) (block : X → B)
    (hsurj : Function.Surjective block)
    (hconst : ∀ {x x'}, block x = block x' →
      ∀ b, blockSum L block x b = blockSum L block x' b) :
    ∃ Lbar : Matrix B B ℝ,
      L * blockIndicator block = blockIndicator block * Lbar := by
  classical
  choose rep hrep using hsurj
  let Lbar : Matrix B B ℝ := fun bi bj => blockSum L block (rep bi) bj
  refine ⟨Lbar, (generator_intertwines_iff_blockSum L Lbar block).2 ?_⟩
  intro x b
  unfold Lbar
  exact hconst (hrep (block x)).symm b

/-- The macro matrix satisfying generator intertwining is unique on a
surjective partition. -/
theorem macro_unique
    (L : Matrix X X ℝ) (block : X → B)
    (hsurj : Function.Surjective block)
    {Lbar₁ Lbar₂ : Matrix B B ℝ}
    (h₁ : L * blockIndicator block = blockIndicator block * Lbar₁)
    (h₂ : L * blockIndicator block = blockIndicator block * Lbar₂) :
    Lbar₁ = Lbar₂ := by
  ext bi bj
  obtain ⟨x, hx⟩ := hsurj bi
  have hs₁ := (generator_intertwines_iff_blockSum L Lbar₁ block).1 h₁ x bj
  have hs₂ := (generator_intertwines_iff_blockSum L Lbar₂ block).1 h₂ x bj
  simpa [hx] using hs₁.symm.trans hs₂


/-- Generator intertwining propagates to every matrix power.  This is the
finite-dimensional algebraic induction used in the reverse half of P-DYN-02. -/
theorem pow_intertwines
    (L : Matrix X X ℝ) (Lbar : Matrix B B ℝ) (block : X → B)
    (h : L * blockIndicator block = blockIndicator block * Lbar) :
    ∀ n : ℕ,
      L ^ n * blockIndicator block =
        blockIndicator block * Lbar ^ n := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      calc
        (L ^ n * L) * blockIndicator block =
            L ^ n * (L * blockIndicator block) := by
              rw [Matrix.mul_assoc]
        _ = L ^ n * (blockIndicator block * Lbar) := by
              rw [h]
        _ = (L ^ n * blockIndicator block) * Lbar := by
              rw [Matrix.mul_assoc]
        _ = (blockIndicator block * Lbar ^ n) * Lbar := by
              rw [ih]
        _ = blockIndicator block * (Lbar ^ n * Lbar) := by
              rw [Matrix.mul_assoc]

end UEOT.V3.CTMCLumpability
