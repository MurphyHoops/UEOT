import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# P-INV-02 — Fisher gauge zero directions

The frozen P-INV-02 states that a tangent direction to a smooth likelihood-
invariant group orbit lies in the kernel of Fisher information. We represent a
smooth orbit locally by a real parameter `t`, use the regular-model chain rule
to identify the derivative of log likelihood at `t = 0` with `vᵀ s`, and then
use orbit invariance to force that derivative to zero.
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
`E[s (sᵀv)]`. This is the action of the source matrix `I = E[s sᵀ]`
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

/-- A likelihood-invariant smooth orbit has zero score in its tangent
direction. `logLik t ω` is the log likelihood along the orbit, and `hderiv`
is the regular-model chain-rule identification of its derivative with `vᵀs`. -/
theorem orbitTangentScoreZero_of_invariant_logLikelihood {d : ℕ}
    (μ : Measure Ω) (score : Ω → Fin d → ℝ) (v : Fin d → ℝ)
    (logLik : ℝ → Ω → ℝ)
    (hinv : ∀ ω t, logLik t ω = logLik 0 ω)
    (hderiv : ∀ᵐ ω ∂μ,
      HasDerivAt (fun t : ℝ => logLik t ω) (directionalScore score v ω) 0) :
    OrbitTangentScoreZero μ score v := by
  filter_upwards [hderiv] with ω hω
  have hEq : (fun t : ℝ => logLik t ω) = (fun _ : ℝ => logLik 0 ω) := by
    funext t
    exact hinv ω t
  rw [hEq] at hω
  exact hω.unique (hasDerivAt_const 0 (logLik 0 ω))

/-- **P-INV-02.** Along a smooth likelihood-invariant orbit, if the derivative
of log likelihood in the orbit parameter is the directional score `vᵀs`, then
the orbit tangent is a Fisher zero direction: `I v = 0`. -/
theorem p_inv_02 {d : ℕ}
    (μ : Measure Ω) (score : Ω → Fin d → ℝ) (v : Fin d → ℝ)
    (logLik : ℝ → Ω → ℝ)
    (hinv : ∀ ω t, logLik t ω = logLik 0 ω)
    (hderiv : ∀ᵐ ω ∂μ,
      HasDerivAt (fun t : ℝ => logLik t ω) (directionalScore score v ω) 0) :
    fisherAction μ score v = 0 := by
  apply fisherAction_eq_zero_of_orbitTangentScoreZero
  exact orbitTangentScoreZero_of_invariant_logLikelihood μ score v logLik hinv hderiv

end UEOT.V3.FisherGauge
