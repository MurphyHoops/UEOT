import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-!
# P-ALI-02 — child updates and parent value

The frozen Core 3 statement lives on a finite real Hilbert direct sum.  The
parent value `J_P` and each child value `J_i` are differentiable; the parent
partial-gradient components are `g_i`, the child deviations are
`e_i = ∇J_i - g_i`, and the update velocity is
`dot a_i = alpha_i ∇J_i` with `alpha_i > 0`.

The source-facing theorem below uses a genuinely heterogeneous finite family of
real Hilbert spaces `H i`, represented by `PiLp 2 H`.  It uses real
`HasGradientAt` certificates for `J_P` and the child objectives and an actual
`HasDerivAt` trajectory certificate.  The chain rule therefore produces the
derivative `dJ_P/dt`; the component expansion and Cauchy--Schwarz then give
exactly P-ALI-02.
-/

namespace UEOT.V3.AlignmentParentValue

open scoped BigOperators

universe uI uH

variable {I : Type uI} {H : I → Type uH}
variable [Fintype I]
variable [∀ i, NormedAddCommGroup (H i)]
variable [∀ i, InnerProductSpace ℝ (H i)]
variable [∀ i, CompleteSpace (H i)]

/-- Algebraic core of P-ALI-02 after the chain rule has produced the parent
value derivative. -/
theorem p_ali_02_core
    (alpha : I → ℝ) (g e : ∀ i, H i)
    (halpha : ∀ i, 0 < alpha i) :
    (∑ i, alpha i * inner ℝ (g i) (g i + e i)) =
        ∑ i, alpha i * (‖g i‖ ^ 2 + inner ℝ (g i) (e i)) ∧
    (∑ i, alpha i * (‖g i‖ ^ 2 + inner ℝ (g i) (e i))) ≥
        ∑ i, alpha i * ‖g i‖ * (‖g i‖ - ‖e i‖) := by
  constructor
  · apply Finset.sum_congr rfl
    intro i hi
    rw [inner_add_right, real_inner_self_eq_norm_sq]
  · apply Finset.sum_le_sum
    intro i hi
    have hcs : -(‖g i‖ * ‖e i‖) ≤ inner ℝ (g i) (e i) := by
      have habs := abs_real_inner_le_norm (g i) (e i)
      exact (neg_le_neg habs).trans (neg_abs_le (inner ℝ (g i) (e i)))
    have hmul :
        alpha i * (-(‖g i‖ * ‖e i‖)) ≤
          alpha i * inner ℝ (g i) (e i) :=
      mul_le_mul_of_nonneg_left hcs (le_of_lt (halpha i))
    calc
      alpha i * ‖g i‖ * (‖g i‖ - ‖e i‖)
          = alpha i * (‖g i‖ ^ 2 - ‖g i‖ * ‖e i‖) := by ring
      _ ≤ alpha i * (‖g i‖ ^ 2 + inner ℝ (g i) (e i)) := by
        linarith

/-- **P-ALI-02.**  On a finite real Hilbert direct sum, child gradient updates
give the exact parent-value derivative decomposition and the frozen
Cauchy--Schwarz lower bound.

`hJP` identifies `g_i` as the components of `∇J_P`; `hJi` identifies
`childGrad i` with `∇J_i`; and `ha` is the actual update trajectory
`dot a_i = alpha_i ∇J_i`.  Thus the first conclusion is genuinely a
`HasDerivAt` statement for `J_P ∘ a`, not an assumed scalar identity. -/
theorem p_ali_02
    (alpha : I → ℝ)
    (JP : PiLp 2 H → ℝ)
    (Ji : ∀ i, H i → ℝ)
    (a : ℝ → PiLp 2 H)
    (t : ℝ) (g childGrad : ∀ i, H i)
    (halpha : ∀ i, 0 < alpha i)
    (hJP : HasGradientAt JP (WithLp.toLp 2 g) (a t))
    (hJi : ∀ i, HasGradientAt (Ji i) (childGrad i) (a t i))
    (ha : HasDerivAt a
      (WithLp.toLp 2 (fun i => alpha i • childGrad i)) t) :
    HasDerivAt (JP ∘ a)
        (∑ i, alpha i *
          (‖g i‖ ^ 2 + inner ℝ (g i) (childGrad i - g i))) t ∧
    (∑ i, alpha i *
        (‖g i‖ ^ 2 + inner ℝ (g i) (childGrad i - g i))) ≥
      ∑ i, alpha i * ‖g i‖ * (‖g i‖ - ‖childGrad i - g i‖) := by
  have _hchildGradient :
      ∀ i, gradient (Ji i) (a t i) = childGrad i :=
    fun i => (hJi i).gradient
  have hchain := hJP.hasFDerivAt.comp_hasDerivAt t ha
  have hinner :
      inner ℝ (WithLp.toLp 2 g)
          (WithLp.toLp 2 (fun i => alpha i • childGrad i)) =
        ∑ i, alpha i *
          (‖g i‖ ^ 2 + inner ℝ (g i) (childGrad i - g i)) := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i hi
    change inner ℝ (g i) (alpha i • childGrad i) =
      alpha i * (‖g i‖ ^ 2 + inner ℝ (g i) (childGrad i - g i))
    rw [real_inner_smul_right, inner_sub_right, real_inner_self_eq_norm_sq]
    ring
  have hderiv :
      HasDerivAt (JP ∘ a)
        (inner ℝ (WithLp.toLp 2 g)
          (WithLp.toLp 2 (fun i => alpha i • childGrad i))) t := by
    simpa only [InnerProductSpace.toDual_apply_apply] using hchain
  constructor
  · rw [hinner] at hderiv
    exact hderiv
  · exact (p_ali_02_core alpha g (fun i => childGrad i - g i) halpha).2

end UEOT.V3.AlignmentParentValue
