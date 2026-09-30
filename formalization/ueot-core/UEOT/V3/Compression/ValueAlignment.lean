import UEOT.V3.AlignmentParentValue
import UEOT.V3.AlignmentThreshold

/-!
# Experimental M-VA — parent directional-value alignment calculus

This module tests a compression between P-ALI-02 and P-ALI-03 while keeping
P-ALI-01 outside the candidate.  The common object is the first-order parent
directional score

`S_g(v) = <g,v>`.

P-ALI-02 supplies robustness of this score when a child direction is the ideal
parent direction plus an error.  P-ALI-03 supplies the exact zero-crossing
threshold when interpolating between a misaligned direction and a target
direction.

The module also proves an out-of-sample robust coordination theorem in which
the target direction itself is imperfect (`g + e`).
-/

namespace UEOT.V3.Compression.ValueAlignment

open scoped BigOperators

universe uI uH

/-- First-order parent-value score of a candidate direction. -/
def directionalScore
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (g v : H) : ℝ :=
  inner ℝ g v

/-- Score of the ideal parent-gradient direction. -/
def idealScore
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (g : H) : ℝ :=
  ‖g‖ ^ 2

@[simp] theorem directionalScore_self
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (g : H) :
    directionalScore g g = idealScore g := by
  simp [directionalScore, idealScore, real_inner_self_eq_norm_sq]

/-- Exact score decomposition for an imperfect ideal direction `g + e`. -/
theorem directionalScore_self_add
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (g e : H) :
    directionalScore g (g + e) =
      idealScore g + inner ℝ g e := by
  simp [directionalScore, idealScore, inner_add_right,
    real_inner_self_eq_norm_sq]

/-- Cauchy--Schwarz robustness margin for the parent directional score. -/
theorem directionalScore_self_add_lower
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (g e : H) :
    ‖g‖ * (‖g‖ - ‖e‖) ≤ directionalScore g (g + e) := by
  have habs := abs_real_inner_le_norm g e
  have hinner : -(‖g‖ * ‖e‖) ≤ inner ℝ g e :=
    (neg_le_neg habs).trans (neg_abs_le (inner ℝ g e))
  rw [directionalScore_self_add]
  unfold idealScore
  nlinarith [sq_nonneg ‖g‖]

/-- Scalar score produced by interpolating from `base` to `target`. -/
def interpolatedScore (base target eta : ℝ) : ℝ :=
  (1 - eta) * base + eta * target

/-- Exact coordination threshold for a negative baseline score and a
nonnegative target score. -/
noncomputable def scoreThreshold (base target : ℝ) : ℝ :=
  -base / (target - base)

theorem positive_interpolatedScore_iff_threshold
    (base target eta : ℝ)
    (hbase : base < 0)
    (htarget : 0 ≤ target) :
    0 < interpolatedScore base target eta ↔
      scoreThreshold base target < eta := by
  have hden : 0 < target - base := by linarith
  constructor
  · intro hpos
    apply (div_lt_iff₀ hden).2
    unfold interpolatedScore at hpos
    linarith
  · intro hthr
    unfold scoreThreshold at hthr
    have hmul : -base < eta * (target - base) :=
      (div_lt_iff₀ hden).1 hthr
    unfold interpolatedScore
    linarith

/-- Inner-product score of a vector interpolation is exactly the interpolation
of the endpoint scores. -/
theorem directionalScore_interpolate
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (g G T : H) (eta : ℝ) :
    directionalScore g ((1 - eta) • G + eta • T) =
      interpolatedScore (directionalScore g G) (directionalScore g T) eta := by
  simp [directionalScore, interpolatedScore, inner_add_right,
    real_inner_smul_right]

/-! ## P-ALI-02 adapter -/

section ParentSum

variable {I : Type uI} {H : I → Type uH}
variable [Fintype I]
variable [∀ i, NormedAddCommGroup (H i)]
variable [∀ i, InnerProductSpace ℝ (H i)]
variable [∀ i, CompleteSpace (H i)]

/-- The algebraic P-ALI-02 certificate through the directional-score core. -/
theorem p_ali_02_core_via_mva
    (alpha : I → ℝ) (g e : ∀ i, H i)
    (halpha : ∀ i, 0 < alpha i) :
    (∑ i, alpha i * inner ℝ (g i) (g i + e i)) =
        ∑ i, alpha i * (‖g i‖ ^ 2 + inner ℝ (g i) (e i)) ∧
    (∑ i, alpha i * (‖g i‖ ^ 2 + inner ℝ (g i) (e i))) ≥
        ∑ i, alpha i * ‖g i‖ * (‖g i‖ - ‖e i‖) := by
  constructor
  · apply Finset.sum_congr rfl
    intro i _
    have hi := directionalScore_self_add (g i) (e i)
    change inner ℝ (g i) (g i + e i) =
      ‖g i‖ ^ 2 + inner ℝ (g i) (e i) at hi
    rw [hi]
  · apply Finset.sum_le_sum
    intro i _
    have hscore := directionalScore_self_add_lower (g i) (e i)
    have hmul := mul_le_mul_of_nonneg_left hscore (le_of_lt (halpha i))
    rw [directionalScore_self_add] at hmul
    change
      alpha i * (‖g i‖ * (‖g i‖ - ‖e i‖)) ≤
        alpha i * (‖g i‖ ^ 2 + inner ℝ (g i) (e i)) at hmul
    simpa [mul_assoc] using hmul

/-- Exact source-facing P-ALI-02 rederivation.  The chain rule remains a
Hilbert/calculus adapter; the robust directional lower bound is supplied by
the common M-VA core. -/
theorem p_ali_02_via_mva
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
    intro i _
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
  · exact (p_ali_02_core_via_mva
      alpha g (fun i => childGrad i - g i) halpha).2

end ParentSum

/-! ## P-ALI-03 adapter -/

/-- Exact source-facing P-ALI-03 rederivation through the generic score
interpolation threshold. -/
theorem p_ali_03_via_mva
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (g G : H) (eta : ℝ)
    (halign : inner ℝ g G < 0)
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    0 < inner ℝ g ((1 - eta) • G + eta • g) ↔
      -inner ℝ g G / (‖g‖ ^ 2 - inner ℝ g G) < eta := by
  have h := positive_interpolatedScore_iff_threshold
    (directionalScore g G) (idealScore g) eta
    (by simpa [directionalScore] using halign)
    (by simp [idealScore])
  have _ := heta0
  have _ := heta1
  have hinterp :
      directionalScore g ((1 - eta) • G + eta • g) =
        interpolatedScore (directionalScore g G) (idealScore g) eta := by
    simpa using directionalScore_interpolate g G g eta
  rw [← hinterp] at h
  simpa [directionalScore, idealScore, scoreThreshold] using h

/-! ## Out-of-sample robust coordination -/

/-- Robust margin associated with an imperfect target `g + e`. -/
def robustIdealMargin
    {H : Type uH} [NormedAddCommGroup H]
    (g e : H) : ℝ :=
  ‖g‖ * (‖g‖ - ‖e‖)

/-- If the target direction is only `g + e`, with error smaller than the parent
gradient norm, then coordinating above the threshold computed from the
Cauchy--Schwarz lower margin is sufficient to make the actual parent
directional score positive.

This combines the robust-direction content of P-ALI-02 with the threshold
content of P-ALI-03 and is not a frozen source endpoint. -/
theorem robust_coordination_positive
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (g G e : H) (eta : ℝ)
    (halign : directionalScore g G < 0)
    (herr : ‖e‖ < ‖g‖)
    (heta0 : 0 ≤ eta)
    (hthreshold :
      scoreThreshold (directionalScore g G) (robustIdealMargin g e) < eta) :
    0 < directionalScore g ((1 - eta) • G + eta • (g + e)) := by
  have hgpos : 0 < ‖g‖ := by
    exact lt_of_le_of_lt (norm_nonneg e) herr
  have hmpos : 0 < robustIdealMargin g e := by
    unfold robustIdealMargin
    exact mul_pos hgpos (sub_pos.mpr herr)
  have hmargin :
      robustIdealMargin g e ≤ directionalScore g (g + e) := by
    exact directionalScore_self_add_lower g e
  have hscalar :
      0 < interpolatedScore
        (directionalScore g G) (robustIdealMargin g e) eta :=
    (positive_interpolatedScore_iff_threshold
      (directionalScore g G) (robustIdealMargin g e) eta
      halign hmpos.le).2 hthreshold
  have hmono :
      interpolatedScore
          (directionalScore g G) (robustIdealMargin g e) eta ≤
        interpolatedScore
          (directionalScore g G) (directionalScore g (g + e)) eta := by
    unfold interpolatedScore
    exact add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hmargin heta0)
  rw [← directionalScore_interpolate g G (g + e) eta] at hmono
  exact lt_of_lt_of_le hscalar hmono

end UEOT.V3.Compression.ValueAlignment
