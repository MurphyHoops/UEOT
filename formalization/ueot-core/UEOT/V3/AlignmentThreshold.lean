import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# P-ALI-03 — coordination threshold

In the frozen Core 3 source, the coordinated field is
`G_eta = (1-eta) G + eta g`.  For the parent gradient `g`, its instantaneous
parent-value derivative along that field is

`inner g G_eta = (1-eta) * inner g G + eta * ‖g‖^2`.

When the uncoordinated field is misaligned (`inner g G < 0`), this derivative
is positive exactly above the stated coordination threshold.  The source's
`0 ≤ eta ≤ 1` domain is retained explicitly.
-/

namespace UEOT.V3.AlignmentThreshold

/-- Threshold after abbreviating `alignment = inner g G` and
`parentSq = ‖g‖²`. -/
noncomputable def coordinationThreshold (alignment parentSq : ℝ) : ℝ :=
  -alignment / (parentSq - alignment)

/-- Scalar normal form of the parent-value derivative. -/
def coordinatedDerivative (alignment parentSq eta : ℝ) : ℝ :=
  (1 - eta) * alignment + eta * parentSq

/-- Algebraic core of P-ALI-03. -/
theorem p_ali_03_scalar
    (alignment parentSq eta : ℝ)
    (halign : alignment < 0)
    (hparent : 0 ≤ parentSq)
    (_heta0 : 0 ≤ eta) (_heta1 : eta ≤ 1) :
    0 < coordinatedDerivative alignment parentSq eta ↔
      coordinationThreshold alignment parentSq < eta := by
  have hden : 0 < parentSq - alignment := by
    linarith
  constructor
  · intro hpos
    apply (div_lt_iff₀ hden).2
    unfold coordinatedDerivative at hpos
    linarith
  · intro hthr
    have hmul : -alignment < eta * (parentSq - alignment) :=
      (div_lt_iff₀ hden).1 hthr
    unfold coordinatedDerivative
    linarith

/-- Source-facing P-ALI-03 in the frozen Hilbert-space variables.

For `G_eta=(1-eta)G+eta g`, misalignment `inner g G < 0` implies that the
parent-value instantaneous derivative along `G_eta` is positive exactly when
`eta` exceeds the source threshold. -/
theorem p_ali_03
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (g G : H) (eta : ℝ)
    (halign : inner ℝ g G < 0)
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    0 < inner ℝ g ((1 - eta) • G + eta • g) ↔
      -inner ℝ g G / (‖g‖ ^ 2 - inner ℝ g G) < eta := by
  have h := p_ali_03_scalar
    (inner ℝ g G) (‖g‖ ^ 2) eta halign (sq_nonneg ‖g‖) heta0 heta1
  simpa [coordinatedDerivative, coordinationThreshold,
    inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq] using h

end UEOT.V3.AlignmentThreshold
