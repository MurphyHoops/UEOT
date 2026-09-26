import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# P-KL-05 — Girsanov full-space KL and observed-path data processing

The frozen Core v3 §22.5 theorem distinguishes two probability spaces.

* On the full noise/probability space, Girsanov's exponential density gives the
  exact relative-entropy cost `(1/2) E_Q ∫ ‖u_t‖² dt`.
* Observing only the state trajectory is a measurable coarse-graining, so its
  KL divergence is bounded above by that full-space cost.

The stochastic-calculus setup in the source already assumes that the
exponential is a true martingale and that, after the measure change, the shifted
noise is Brownian and the controlled drift is `b⁰ + σu`. The proof of P-KL-05
then uses the terminal exponential-density identity, the Girsanov
stochastic-integral shift, and the fact that the controlled stochastic integral
has mean zero. `TerminalGirsanovData` records exactly those terminal
consequences; it does not assume either KL conclusion.

The control energy below is the literal clock-time integral from the source.
-/

namespace UEOT.V3.GirsanovPathKL

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

universe uΩ uΓ uE

variable {Ω : Type uΩ} [MeasurableSpace Ω]
variable {Γ : Type uΓ} [MeasurableSpace Γ]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Literal finite-horizon control energy `∫₀ᵀ ‖u_t‖² dt`. -/
noncomputable def controlEnergy
    (T : ℝ≥0) (u : ℝ → Ω → E) (ω : Ω) : ℝ :=
  ∫ t : ℝ in (0 : ℝ)..(T : ℝ), ‖u t ω‖ ^ 2

/-- Terminal identities supplied by the frozen Girsanov setup.

`baselineIntegral` is `∫ u dW⁰` and `controlledIntegral` is
`∫ u dWᵘ`. The field `integral_shift` is the terminal form of
`dW⁰ = dWᵘ + u dt`; `controlledIntegral_mean_zero` is the standard
square-integrable martingale consequence used explicitly in the source proof.
Neither field contains a KL statement. -/
structure TerminalGirsanovData
    (P0 Q : Measure Ω) (T : ℝ≥0) (u : ℝ → Ω → E) where
  density : Ω → ℝ≥0∞
  baselineIntegral : Ω → ℝ
  controlledIntegral : Ω → ℝ
  measurable_density : Measurable density
  changeOfMeasure : Q = P0.withDensity density
  density_eq_exp : ∀ᵐ ω ∂P0,
    density ω =
      ENNReal.ofReal
        (Real.exp
          (baselineIntegral ω - (2 : ℝ)⁻¹ * controlEnergy T u ω))
  integral_shift : ∀ᵐ ω ∂Q,
    baselineIntegral ω =
      controlledIntegral ω + controlEnergy T u ω
  controlledIntegral_integrable : Integrable controlledIntegral Q
  controlledIntegral_mean_zero : ∫ ω, controlledIntegral ω ∂Q = 0
  energy_integrable : Integrable (controlEnergy T u) Q

namespace TerminalGirsanovData

variable {P0 Q : Measure Ω} {T : ℝ≥0} {u : ℝ → Ω → E}

/-- The Girsanov-controlled law is absolutely continuous with respect to the
baseline law because it is obtained by a density change. -/
theorem absolutelyContinuous
    (h : TerminalGirsanovData P0 Q T u) :
    Q ≪ P0 := by
  rw [h.changeOfMeasure]
  exact MeasureTheory.withDensity_absolutelyContinuous _ _

/-- The actual Radon--Nikodym derivative equals the exponential Girsanov
density, now stated under the controlled law. -/
theorem rnDeriv_eq_density
    (h : TerminalGirsanovData P0 Q T u) :
    Q.rnDeriv P0 =ᵐ[Q] h.density := by
  have h0 : Q.rnDeriv P0 =ᵐ[P0] h.density := by
    rw [h.changeOfMeasure]
    exact Measure.rnDeriv_withDensity P0 h.measurable_density
  exact h.absolutelyContinuous.ae_le h0

/-- Substitution of `dW⁰ = dWᵘ + u dt` into the exponential density gives
the source log-likelihood decomposition
`log(dQ/dP⁰) = ∫u dWᵘ + (1/2)∫‖u‖²dt`. -/
theorem llr_eq_controlledIntegral_add_halfEnergy
    (h : TerminalGirsanovData P0 Q T u) :
    llr Q P0 =ᵐ[Q]
      fun ω =>
        h.controlledIntegral ω + (2 : ℝ)⁻¹ * controlEnergy T u ω := by
  have hrn := h.rnDeriv_eq_density
  have hexp : ∀ᵐ ω ∂Q,
      h.density ω =
        ENNReal.ofReal
          (Real.exp
            (h.baselineIntegral ω - (2 : ℝ)⁻¹ * controlEnergy T u ω)) :=
    h.absolutelyContinuous.ae_le h.density_eq_exp
  filter_upwards [hrn, hexp, h.integral_shift] with ω hrnω hexpω hshiftω
  rw [llr_def, hrnω, hexpω,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, Real.log_exp, hshiftω]
  ring

/-- The source log-likelihood is integrable under the controlled law when the
controlled stochastic integral and the energy are integrable. -/
theorem integrable_llr
    (h : TerminalGirsanovData P0 Q T u) :
    Integrable (llr Q P0) Q := by
  have hhalf :
      Integrable (fun ω => (2 : ℝ)⁻¹ * controlEnergy T u ω) Q :=
    h.energy_integrable.const_mul _
  exact (h.controlledIntegral_integrable.add hhalf).congr
    h.llr_eq_controlledIntegral_add_halfEnergy.symm

/-- Frozen P-KL-05 full-space equality. -/
theorem fullSpaceKL_eq_halfEnergy
    [IsProbabilityMeasure P0] [IsProbabilityMeasure Q]
    (h : TerminalGirsanovData P0 Q T u) :
    klDiv Q P0 =
      ENNReal.ofReal
        ((2 : ℝ)⁻¹ * ∫ ω, controlEnergy T u ω ∂Q) := by
  rw [klDiv_of_ac_of_integrable h.absolutelyContinuous h.integrable_llr]
  rw [integral_congr_ae h.llr_eq_controlledIntegral_add_halfEnergy]
  rw [integral_add h.controlledIntegral_integrable
    (h.energy_integrable.const_mul _)]
  rw [integral_const_mul, h.controlledIntegral_mean_zero]
  simp

/-- Frozen P-KL-05 observed-state-path inequality. This is deliberately a
pushforward inequality, not an equality: hidden noise directions can carry
relative entropy that is invisible in the state trajectory. -/
theorem statePathKL_le_halfEnergy
    [IsProbabilityMeasure P0] [IsProbabilityMeasure Q]
    (h : TerminalGirsanovData P0 Q T u)
    (statePath : Ω → Γ) (hstate : Measurable statePath) :
    klDiv (Q.map statePath) (P0.map statePath) ≤
      ENNReal.ofReal
        ((2 : ℝ)⁻¹ * ∫ ω, controlEnergy T u ω ∂Q) := by
  rw [← h.fullSpaceKL_eq_halfEnergy]
  exact klDiv_map_le Q P0 hstate

/-- **P-KL-05.** Full-space Girsanov entropy is exactly half the expected
control energy, while every measurable observed state path obeys only the
data-processing upper bound. -/
theorem p_kl_05
    [IsProbabilityMeasure P0] [IsProbabilityMeasure Q]
    (h : TerminalGirsanovData P0 Q T u)
    (statePath : Ω → Γ) (hstate : Measurable statePath) :
    klDiv Q P0 =
        ENNReal.ofReal
          ((2 : ℝ)⁻¹ * ∫ ω, controlEnergy T u ω ∂Q) ∧
      klDiv (Q.map statePath) (P0.map statePath) ≤
        ENNReal.ofReal
          ((2 : ℝ)⁻¹ * ∫ ω, controlEnergy T u ω ∂Q) :=
  ⟨h.fullSpaceKL_eq_halfEnergy,
    h.statePathKL_le_halfEnergy statePath hstate⟩

end TerminalGirsanovData

end

end UEOT.V3.GirsanovPathKL
