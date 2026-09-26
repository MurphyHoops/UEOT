import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic

/-!
# P-CTL-03 — continuous-time diffusion HJB verification

Frozen Core v3 §19.4 assumes a feasible controlled diffusion, a bounded `C²`
function `V`, the classical HJB equation

`rho * V x = sup_a (reward x a + L^a V x)`,

a measurable maximizing selector whose closed-loop SDE is well-defined, and
all localization/integrability/stochastic-integral hypotheses needed by Itô's
formula. Appendix C explicitly licenses Itô/Dynkin as standard mathematics
provided those conditions are retained.

Pinned Mathlib does not currently contain a full controlled-SDE Itô stack.
Following UEOT's existing `RecoveryDynkin` pattern, `ItoRun` records exactly
the finite-horizon expectation output supplied by a valid process-specific
Itô/localization theorem. Its `occupation` measure is the discounted
occupation measure of the admissible diffusion run, and `terminalLaw` is the
terminal state law. No value bound or optimality conclusion is stored in the
certificate.

The rest is proved here: the HJB residual is nonpositive for every admissible
action, zero for the maximizing selector, boundedness of `V` kills the terminal
term, and the finite-horizon inequalities pass to the infinite discounted
reward. Hence every admissible policy is dominated by `V`, while the selector
attains `V`.
-/

namespace UEOT.V3.DiffusionHJBVerification

set_option linter.style.haveILetI false


noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

universe uX uA

variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X]
variable {A : Type uA} [MeasurableSpace A]

structure Model (X : Type uX) (A : Type uA)
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace A] where
  rho : ℝ
  rho_pos : 0 < rho
  V : X → ℝ
  V_C2 : ContDiff ℝ 2 V
  VBound : ℝ
  VBound_nonneg : 0 ≤ VBound
  V_bounded : ∀ x, |V x| ≤ VBound
  reward : X → A → ℝ
  generatorV : X → A → ℝ
  selector : X → A
  selector_measurable : Measurable selector
  hjb_upper : ∀ x a, reward x a + generatorV x a ≤ rho * V x
  hjb_selector : ∀ x,
    reward x (selector x) + generatorV x (selector x) = rho * V x

namespace Model

variable (M : Model X A)

/-- HJB residual `r + L^a V - rho V`.  The HJB equation makes it nonpositive
for every action and zero on the maximizing selector. -/
def residual (M : Model X A) (z : X × A) : ℝ :=
  M.reward z.1 z.2 + M.generatorV z.1 z.2 - M.rho * M.V z.1

/-- Discounted occupation output of a process-specific Itô/localization theorem.
The occupation measure already includes the factor exp(-rho t) dt. -/
structure ItoRun (x0 : X) where
  occupation : NNReal → Measure (X × A)
  terminalLaw : NNReal → Measure X
  terminal_prob : ∀ T : NNReal, IsProbabilityMeasure (terminalLaw T)
  reward_integrable : ∀ T : NNReal,
    Integrable (fun z : X × A => M.reward z.1 z.2) (occupation T)
  drift_integrable : ∀ T : NNReal,
    Integrable
      (fun z : X × A => M.generatorV z.1 z.2 - M.rho * M.V z.1)
      (occupation T)
  ito_expectation : ∀ T : NNReal,
    Real.exp (-M.rho * (T : ℝ)) * (∫ x, M.V x ∂terminalLaw T) =
      M.V x0 +
        ∫ z : X × A,
          (M.generatorV z.1 z.2 - M.rho * M.V z.1) ∂occupation T
  infiniteReward : ℝ
  reward_tendsto : Tendsto
    (fun n : ℕ =>
      ∫ z : X × A, M.reward z.1 z.2 ∂occupation (n : NNReal))
    atTop (𝓝 infiniteReward)

namespace ItoRun

variable {M : Model X A} {x0 : X}

def terminalMean (R : M.ItoRun x0) (T : NNReal) : ℝ :=
  Real.exp (-M.rho * (T : ℝ)) * ∫ x, M.V x ∂R.terminalLaw T

lemma V_integrable_terminal (R : M.ItoRun x0) (T : NNReal) :
    Integrable M.V (R.terminalLaw T) := by
  letI : IsProbabilityMeasure (R.terminalLaw T) := R.terminal_prob T
  apply Integrable.of_bound M.V_C2.continuous.aestronglyMeasurable M.VBound
  filter_upwards with x
  simpa [Real.norm_eq_abs] using M.V_bounded x

lemma abs_integral_V_le (R : M.ItoRun x0) (T : NNReal) :
    |∫ x, M.V x ∂R.terminalLaw T| ≤ M.VBound := by
  letI : IsProbabilityMeasure (R.terminalLaw T) := R.terminal_prob T
  have h := norm_integral_le_of_norm_le_const
    (μ := R.terminalLaw T)
    (f := M.V)
    (C := M.VBound)
    (Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using M.V_bounded x)
  simpa [Real.norm_eq_abs, probReal_univ] using h

lemma abs_terminalMean_le (R : M.ItoRun x0) (T : NNReal) :
    |R.terminalMean T| ≤
      Real.exp (-M.rho * (T : ℝ)) * M.VBound := by
  rw [terminalMean, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (R.abs_integral_V_le T) (Real.exp_pos _).le

lemma terminalMean_tendsto_zero (R : M.ItoRun x0) :
    Tendsto (fun n : ℕ => R.terminalMean (n : NNReal)) atTop (𝓝 0) := by
  have hcoe : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hmul : Tendsto (fun n : ℕ => M.rho * (n : ℝ)) atTop atTop :=
    hcoe.const_mul_atTop M.rho_pos
  have hexp :
      Tendsto (fun n : ℕ => Real.exp (-(M.rho * (n : ℝ)))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hmul
  have hbound :
      Tendsto
        (fun n : ℕ => Real.exp (-(M.rho * (n : ℝ))) * M.VBound)
        atTop (𝓝 0) := by
    simpa using hexp.mul_const M.VBound
  rw [tendsto_zero_iff_abs_tendsto_zero]
  exact squeeze_zero
    (fun n => abs_nonneg (R.terminalMean (n : NNReal)))
    (fun n => by
      simpa [neg_mul] using R.abs_terminalMean_le (n : NNReal))
    hbound

def residual (M : Model X A) (z : X × A) : ℝ :=
  M.reward z.1 z.2 + M.generatorV z.1 z.2 - M.rho * M.V z.1

lemma residual_integrable (R : M.ItoRun x0) (T : NNReal) :
    Integrable (fun z : X × A => M.residual z) (R.occupation T) := by
  have h := (R.reward_integrable T).add (R.drift_integrable T)
  exact h.congr (Filter.Eventually.of_forall fun z => by
    simp [Model.residual]
    ring)

lemma residual_integral_nonpos (R : M.ItoRun x0) (T : NNReal) :
    (∫ z : X × A, M.residual z ∂R.occupation T) ≤ 0 := by
  exact integral_nonpos_of_ae
    (Filter.Eventually.of_forall fun z => by
      dsimp [Model.residual]
      linarith [M.hjb_upper z.1 z.2])

lemma finite_horizon_upper (R : M.ItoRun x0) (T : NNReal) :
    (∫ z : X × A, M.reward z.1 z.2 ∂R.occupation T) +
      R.terminalMean T ≤ M.V x0 := by
  have hadd :
      (∫ z : X × A, M.reward z.1 z.2 ∂R.occupation T) +
        (∫ z : X × A,
          (M.generatorV z.1 z.2 - M.rho * M.V z.1) ∂R.occupation T) =
      ∫ z : X × A, M.residual z ∂R.occupation T := by
    rw [← integral_add (R.reward_integrable T) (R.drift_integrable T)]
    apply integral_congr_ae
    filter_upwards with z
    simp [Model.residual]
    ring
  rw [terminalMean, R.ito_expectation T]
  calc
    (∫ z : X × A, M.reward z.1 z.2 ∂R.occupation T) +
          (M.V x0 + ∫ z : X × A,
            (M.generatorV z.1 z.2 - M.rho * M.V z.1) ∂R.occupation T)
        = M.V x0 + (∫ z : X × A, M.residual z ∂R.occupation T) := by
            rw [← hadd]
            ring
    _ ≤ M.V x0 := by linarith [R.residual_integral_nonpos T]

lemma infiniteReward_le_value (R : M.ItoRun x0) :
    R.infiniteReward ≤ M.V x0 := by
  have hlim :
      Tendsto
        (fun n : ℕ =>
          (∫ z : X × A, M.reward z.1 z.2 ∂R.occupation (n : NNReal)) +
            R.terminalMean (n : NNReal))
        atTop (𝓝 R.infiniteReward) := by
    simpa using R.reward_tendsto.add R.terminalMean_tendsto_zero
  exact le_of_tendsto' hlim (fun n => R.finite_horizon_upper (n : NNReal))

end ItoRun

/-- A closed-loop run of the measurable HJB maximizer. -/
structure SelectorRun (x0 : X) extends M.ItoRun x0 where
  selector_ae : ∀ T,
    ∀ᵐ z : X × A ∂toItoRun.occupation T, z.2 = M.selector z.1

namespace SelectorRun

variable {M : Model X A} {x0 : X}

lemma residual_ae_zero (R : M.SelectorRun x0) (T : NNReal) :
    (fun z : X × A => M.residual z) =ᵐ[R.toItoRun.occupation T] 0 := by
  filter_upwards [R.selector_ae T] with z hz
  dsimp [Model.residual]
  rw [hz, M.hjb_selector z.1]
  ring

lemma residual_integral_eq_zero (R : M.SelectorRun x0) (T : NNReal) :
    (∫ z : X × A, M.residual z ∂R.toItoRun.occupation T) = 0 := by
  rw [integral_congr_ae (R.residual_ae_zero T)]
  simp

lemma finite_horizon_eq (R : M.SelectorRun x0) (T : NNReal) :
    (∫ z : X × A, M.reward z.1 z.2 ∂R.toItoRun.occupation T) +
      R.toItoRun.terminalMean T = M.V x0 := by
  have hadd :
      (∫ z : X × A, M.reward z.1 z.2 ∂R.toItoRun.occupation T) +
        (∫ z : X × A,
          (M.generatorV z.1 z.2 - M.rho * M.V z.1)
          ∂R.toItoRun.occupation T) =
      ∫ z : X × A, M.residual z ∂R.toItoRun.occupation T := by
    rw [← integral_add
      (R.toItoRun.reward_integrable T) (R.toItoRun.drift_integrable T)]
    apply integral_congr_ae
    filter_upwards with z
    simp [Model.residual]
    ring
  rw [ItoRun.terminalMean, R.toItoRun.ito_expectation T]
  calc
    (∫ z : X × A, M.reward z.1 z.2 ∂R.toItoRun.occupation T) +
          (M.V x0 + ∫ z : X × A,
            (M.generatorV z.1 z.2 - M.rho * M.V z.1)
              ∂R.toItoRun.occupation T)
        = M.V x0 + (∫ z : X × A, M.residual z ∂R.toItoRun.occupation T) := by
            rw [← hadd]
            ring
    _ = M.V x0 := by rw [R.residual_integral_eq_zero T]; ring

lemma infiniteReward_eq_value (R : M.SelectorRun x0) :
    R.toItoRun.infiniteReward = M.V x0 := by
  have hlim :
      Tendsto
        (fun n : ℕ =>
          (∫ z : X × A, M.reward z.1 z.2
            ∂R.toItoRun.occupation (n : NNReal)) +
            R.toItoRun.terminalMean (n : NNReal))
        atTop (𝓝 R.toItoRun.infiniteReward) := by
    simpa using
      R.toItoRun.reward_tendsto.add R.toItoRun.terminalMean_tendsto_zero
  have hconst :
      Tendsto
        (fun n : ℕ =>
          (∫ z : X × A, M.reward z.1 z.2
            ∂R.toItoRun.occupation (n : NNReal)) +
            R.toItoRun.terminalMean (n : NNReal))
        atTop (𝓝 (M.V x0)) := by
    simpa only [R.finite_horizon_eq] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => M.V x0) atTop (𝓝 (M.V x0)))
  exact (tendsto_nhds_unique hlim hconst)

end SelectorRun

/-- Family of all admissible controls together with the distinguished
measurable HJB selector's well-defined closed-loop diffusion run. -/
structure ControlFamily (Policy : Type*) where
  run : Policy → (x0 : X) → M.ItoRun x0
  selectorPolicy : Policy
  selectorRun : (x0 : X) → M.SelectorRun x0
  selectorRun_eq : ∀ x0,
    (selectorRun x0).toItoRun = run selectorPolicy x0

namespace ControlFamily

variable {M : Model X A} {Policy : Type*}

def IsOptimalValue (F : M.ControlFamily Policy) : Prop :=
  ∀ x0,
    (∀ π, (F.run π x0).infiniteReward ≤ M.V x0) ∧
    (F.run F.selectorPolicy x0).infiniteReward = M.V x0

theorem p_ctl_03 (F : M.ControlFamily Policy) : F.IsOptimalValue := by
  intro x0
  constructor
  · intro π
    exact (F.run π x0).infiniteReward_le_value
  · rw [← F.selectorRun_eq x0]
    exact (F.selectorRun x0).infiniteReward_eq_value

end ControlFamily
end Model

/-- **P-CTL-03.** Classical continuous-time HJB verification: the bounded
`C²` HJB candidate dominates every admissible diffusion control and is attained
by the measurable maximizing selector whose closed-loop Itô run exists. -/
theorem p_ctl_03
    (M : Model X A) {Policy : Type*} (F : M.ControlFamily Policy) :
    F.IsOptimalValue :=
  Model.ControlFamily.p_ctl_03 F

end
end UEOT.V3.DiffusionHJBVerification
