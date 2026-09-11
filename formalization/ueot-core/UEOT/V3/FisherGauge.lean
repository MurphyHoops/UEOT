import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# P-INV-02 foundation — Fisher gauge zero directions

The frozen P-INV-02 states that a tangent direction to a smooth likelihood-
invariant group orbit lies in the kernel of Fisher information.  This module
formalizes the second implication in that proof: once the directional score is
zero almost everywhere, the Fisher action on that tangent is exactly zero.

The separate smooth-orbit-invariance -> directional-score-zero bridge remains
an explicit source-level obligation before P-INV-02 can be promoted.
-/

namespace UEOT.V3.FisherGauge

open MeasureTheory

universe uΩ

variable {Ω : Type uΩ} [MeasurableSpace Ω]

/-- Directional score `vᵀ s(ω)` in finite coordinates. -/
def directionalScore {d : ℕ}
    (score : Ω → Fin d → ℝ) (v : Fin d → ℝ) (ω : Ω) : ℝ :=
  ∑ j, score ω j * v j

/-- Fisher information acting on `v`, written directly as
`E[s (sᵀv)]`.  This is the action of the source matrix `I = E[s sᵀ]`
without choosing a separate matrix representation. -/
noncomputable def fisherAction {d : ℕ}
    (μ : Measure Ω) (score : Ω → Fin d → ℝ) (v : Fin d → ℝ) : Fin d → ℝ :=
  fun i => ∫ ω, score ω i * directionalScore score v ω ∂μ

/-- The differentiated likelihood-invariance condition at a group-orbit
tangent: the score has zero component along `v` almost everywhere. -/
def OrbitTangentScoreZero {d : ℕ}
    (μ : Measure Ω) (score : Ω → Fin d → ℝ) (v : Fin d → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, directionalScore score v ω = 0

/-- Kernel core for P-INV-02: a zero directional score implies that the Fisher
operator annihilates the tangent exactly. -/
theorem fisherAction_eq_zero_of_orbitTangentScoreZero {d : ℕ}
    (μ : Measure Ω) (score : Ω → Fin d → ℝ) (v : Fin d → ℝ)
    (hzero : OrbitTangentScoreZero μ score v) :
    fisherAction μ score v = 0 := by
  funext i
  unfold fisherAction
  apply integral_congr_ae
  filter_upwards [hzero] with ω hω
  simp [directionalScore, hω]

end UEOT.V3.FisherGauge
