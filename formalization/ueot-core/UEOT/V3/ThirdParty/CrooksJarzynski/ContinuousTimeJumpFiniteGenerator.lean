/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
Modified for UEOT Core v3 integration in 2026: module import paths and omission
of the upstream standalone `ThreeStateBranching` example namespace.  The general
finite-generator definitions and theorem statements used here are unchanged.
-/
import UEOT.V3.ThirdParty.CrooksJarzynski.ContinuousTimeJumpSimplex
import Mathlib.Data.Matrix.Basic
import Mathlib.MeasureTheory.Measure.Count

/-!
# Finite-state continuous-time jump generators

A `FiniteJumpGenerator` stores nonnegative finite-state jump rates with a zero
diagonal. The escape rates and conservative real generator are derived from
those rates. Counting measure on finite state sequences, combined with the
fixed-horizon simplex construction, gives a canonical reference that supports
branching. A symmetric three-state Y chain is included as an example.
-/

open MeasureTheory
open scoped ENNReal BigOperators Matrix unitInterval

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump

universe u

/-- Nonnegative off-diagonal jump rates on a finite state space. -/
structure FiniteJumpGenerator (Ω : Type u) [Fintype Ω] where
  jumpRate : Ω → Ω → NNReal
  jumpRate_self : ∀ x, jumpRate x x = 0

namespace FiniteJumpGenerator

variable {Ω : Type u} [Fintype Ω]

@[simp]
theorem jumpRate_self_apply (G : FiniteJumpGenerator Ω) (x : Ω) :
    G.jumpRate x x = 0 :=
  G.jumpRate_self x

/-- The total rate of leaving a state. -/
def escapeRate (G : FiniteJumpGenerator Ω) (x : Ω) : NNReal :=
  ∑ y, G.jumpRate x y

/-! ### Scaling every rate

Multiplying all jump rates by a common factor multiplies the generator by that
factor, so it is exactly a reparametrization of time.  This is what lets a
statement about a residual *fraction* of a fixed horizon be read as a statement
about elapsed time for a rescaled chain. -/

/-- All jump rates scaled by a common nonnegative factor. -/
def scale (G : FiniteJumpGenerator Ω) (K : NNReal) : FiniteJumpGenerator Ω where
  jumpRate x z := K * G.jumpRate x z
  jumpRate_self x := by simp

@[simp]
theorem scale_jumpRate (G : FiniteJumpGenerator Ω) (K : NNReal) (x z : Ω) :
    (G.scale K).jumpRate x z = K * G.jumpRate x z :=
  rfl

@[simp]
theorem scale_escapeRate (G : FiniteJumpGenerator Ω) (K : NNReal) (x : Ω) :
    (G.scale K).escapeRate x = K * G.escapeRate x := by
  simp [escapeRate, Finset.mul_sum]

variable [DecidableEq Ω]

/-- The real conservative generator associated with the jump rates. -/
def generator (G : FiniteJumpGenerator Ω) : Matrix Ω Ω ℝ :=
  fun x y => if y = x then -(G.escapeRate x : ℝ) else G.jumpRate x y

@[simp]
theorem generator_apply_self (G : FiniteJumpGenerator Ω) (x : Ω) :
    G.generator x x = -(G.escapeRate x : ℝ) := by
  simp [generator]

@[simp]
theorem generator_apply_of_ne (G : FiniteJumpGenerator Ω) {x y : Ω}
    (h : y ≠ x) :
    G.generator x y = (G.jumpRate x y : ℝ) := by
  simp [generator, h]

/-- Every off-diagonal generator entry is nonnegative. -/
theorem generator_offDiagonal_nonneg (G : FiniteJumpGenerator Ω)
    {x y : Ω} (h : y ≠ x) :
    0 ≤ G.generator x y := by
  rw [G.generator_apply_of_ne h]
  positivity

/-- Off-diagonal nonnegativity together with zero row sums. -/
def IsConservative (Q : Matrix Ω Ω ℝ) : Prop :=
  (∀ x y, y ≠ x → 0 ≤ Q x y) ∧
    ∀ x, ∑ y, Q x y = 0

/-- Every row of the associated real generator sums to zero. -/
theorem generator_row_sum (G : FiniteJumpGenerator Ω) (x : Ω) :
    ∑ y, G.generator x y = 0 := by
  classical
  rw [← Finset.sum_erase_add Finset.univ
    (fun y => G.generator x y) (Finset.mem_univ x)]
  rw [G.generator_apply_self]
  have hoff :
      (∑ y ∈ Finset.univ.erase x, G.generator x y) =
        ∑ y ∈ Finset.univ.erase x, (G.jumpRate x y : ℝ) := by
    apply Finset.sum_congr rfl
    intro y hy
    exact G.generator_apply_of_ne (Finset.ne_of_mem_erase hy)
  rw [hoff]
  have hsum :
      (∑ y ∈ Finset.univ.erase x, (G.jumpRate x y : ℝ)) =
        ∑ y, (G.jumpRate x y : ℝ) := by
    rw [← Finset.sum_erase_add Finset.univ
      (fun y => (G.jumpRate x y : ℝ)) (Finset.mem_univ x)]
    simp
  rw [hsum]
  simp [escapeRate]

/-- Scaling every jump rate scales the generator. -/
theorem scale_generator (G : FiniteJumpGenerator Ω) (K : NNReal) :
    (G.scale K).generator = (K : ℝ) • G.generator := by
  ext x y
  rcases eq_or_ne y x with h | h
  · subst h
    simp [Matrix.smul_apply]
  · simp [G.generator_apply_of_ne h, (G.scale K).generator_apply_of_ne h,
      Matrix.smul_apply]

/-- The derived matrix is conservative. -/
theorem generator_isConservative (G : FiniteJumpGenerator Ω) :
    IsConservative G.generator := by
  refine ⟨?_, G.generator_row_sum⟩
  intro x y h
  exact G.generator_offDiagonal_nonneg h

/-- The time-homogeneous escape-rate family for path densities. -/
def pathEscapeRate (G : FiniteJumpGenerator Ω) {n : ℕ} :
    Fin (n + 1) → Ω → NNReal :=
  fun _ x => G.escapeRate x

/-- The time-homogeneous jump-rate family for path densities. -/
def pathJumpRate (G : FiniteJumpGenerator Ω) {n : ℕ} :
    Fin n → Ω → Ω → NNReal :=
  fun _ x y => G.jumpRate x y

variable [MeasurableSpace Ω]

/-- Counting measure on all finite state sequences in one jump-count sector. -/
noncomputable def stateSequenceCountingReference
    (_G : FiniteJumpGenerator Ω) (n : ℕ) :
    Measure (Fin (n + 1) → Ω) :=
  Measure.count

/-- The physical `n`-jump holding-time volume `T^n / n!`, expressed through
the free-coordinate simplex volume. -/
noncomputable def simplexSectorMass (T : NNReal) (n : ℕ) : ℝ≥0∞ :=
  (T : ℝ≥0∞) ^ n *
    (volume : Measure (Fin n → I)) (Simplex.freeSimplexSet n)

/-- The physical sector mass evaluates to `T^n / n!`. -/
theorem simplexSectorMass_eq (T : NNReal) (n : ℕ) :
    simplexSectorMass T n =
      (T : ℝ≥0∞) ^ n * ENNReal.ofReal (1 / (n.factorial : ℝ)) := by
  unfold simplexSectorMass
  rw [Simplex.volume_freeSimplexSet]

/-- Counting state sequences combined with the fixed-horizon simplex law,
scaled by the physical holding-time volume `T^n / n!` of the sector. -/
noncomputable def countingReference
    (G : FiniteJumpGenerator Ω) (T : NNReal) (n : ℕ) :
    Measure (JumpPath Ω n) :=
  Simplex.reference T (G.stateSequenceCountingReference n)
    (simplexSectorMass T n)

omit [DecidableEq Ω] in
/-- The counting reference is invariant under path reversal. -/
theorem map_countingReference_reverse
    (G : FiniteJumpGenerator Ω) (T : NNReal) (n : ℕ) :
    (G.countingReference T n).map JumpPath.reverse =
      G.countingReference T n := by
  exact Simplex.map_reference_reverse T
    (G.stateSequenceCountingReference n) (simplexSectorMass T n)

omit [DecidableEq Ω] in
/-- The counting reference is supported on paths of duration `T`. -/
theorem countingReference_ae_horizon
    (G : FiniteJumpGenerator Ω) (T : NNReal) (n : ℕ) :
    ∀ᵐ γ ∂G.countingReference T n,
      γ ∈ JumpPath.horizonSet (Ω := Ω) (n := n) T := by
  exact Simplex.reference_ae_horizon T
    (G.stateSequenceCountingReference n) (simplexSectorMass T n)

variable [MeasurableSingletonClass Ω]

omit [DecidableEq Ω] in
/-- Every state sequence has unit counting mass. -/
@[simp]
theorem stateSequenceCountingReference_singleton
    (G : FiniteJumpGenerator Ω) (n : ℕ)
    (states : Fin (n + 1) → Ω) :
    G.stateSequenceCountingReference n {states} = 1 := by
  exact Measure.count_singleton states

end FiniteJumpGenerator
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
