import UEOT.V3.RepresentationCovariance
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# P-FAC-01 finite feedback value bridge

`RepresentationCovariance.causalLaw_transport_equiv` already proves finite
causal path-law naturality from the primitive step-kernel transport condition.
This file converts that PMF equality into measure transport and then into
finite-horizon reward/value covariance.  Thus the value statement is derived
from transported dynamics rather than assuming path-law equality as an
independent hypothesis.
-/

namespace UEOT.V3.RepresentationCovariance

open MeasureTheory
open UEOT.V3.PathError

universe uHist uPol

variable {H₀ H₀' Z Z' : Type uHist}
variable [Fintype H₀] [Fintype H₀'] [Fintype Z] [Fintype Z']
variable [MeasurableSpace H₀] [MeasurableSpace H₀']
variable [MeasurableSpace Z] [MeasurableSpace Z']
variable [MeasurableSingletonClass H₀] [MeasurableSingletonClass H₀']
variable [MeasurableSingletonClass Z] [MeasurableSingletonClass Z']

/-- The recursively induced finite-history equivalence is bimeasurable on
finite measurable-singleton state spaces. -/
def causalHistoryMeasurableEquiv
    (e₀ : H₀ ≃ H₀') (eZ : Z ≃ Z') (n : ℕ) :
    CausalHistory H₀ Z n ≃ᵐ CausalHistory H₀' Z' n where
  toEquiv := causalHistoryEquiv e₀ eZ n
  measurable_toFun := measurable_of_countable _
  measurable_invFun := measurable_of_countable _

@[simp] theorem causalHistoryMeasurableEquiv_apply
    (e₀ : H₀ ≃ H₀') (eZ : Z ≃ Z') (n : ℕ)
    (h : CausalHistory H₀ Z n) :
    causalHistoryMeasurableEquiv e₀ eZ n h =
      causalHistoryEquiv e₀ eZ n h := rfl

/-- Measure-level form of finite causal path-law covariance.  The equality is
not assumed: it follows from the transported one-step extension kernels. -/
theorem causalLaw_toMeasure_transport_equiv
    (p₀ : PMF H₀)
    (K : ∀ n, CausalHistory H₀ Z n → PMF Z)
    (K' : ∀ n, CausalHistory H₀' Z' n → PMF Z')
    (e₀ : H₀ ≃ H₀') (eZ : Z ≃ Z')
    (hK : ∀ n h,
      K' n (causalHistoryEquiv e₀ eZ n h) = (K n h).map eZ)
    (n : ℕ) :
    (causalLaw p₀ K n).toMeasure.map
        (causalHistoryMeasurableEquiv e₀ eZ n) =
      (causalLaw (p₀.map e₀) K' n).toMeasure := by
  rw [PMF.toMeasure_map (causalHistoryMeasurableEquiv e₀ eZ n).measurable]
  exact congrArg PMF.toMeasure (by
    simpa [causalHistoryMeasurableEquiv] using
      causalLaw_transport_equiv p₀ K K' e₀ eZ hK n)

/-- Finite-horizon expected reward is invariant under the same primitive
causal-kernel transport assumptions. -/
theorem causalLaw_expectedReward_transport
    (p₀ : PMF H₀)
    (K : ∀ n, CausalHistory H₀ Z n → PMF Z)
    (K' : ∀ n, CausalHistory H₀' Z' n → PMF Z')
    (e₀ : H₀ ≃ H₀') (eZ : Z ≃ Z')
    (hK : ∀ n h,
      K' n (causalHistoryEquiv e₀ eZ n h) = (K n h).map eZ)
    (n : ℕ) (reward : CausalHistory H₀ Z n → ℝ) :
    (∫ h', reward ((causalHistoryMeasurableEquiv e₀ eZ n).symm h')
        ∂(causalLaw (p₀.map e₀) K' n).toMeasure) =
      ∫ h, reward h ∂(causalLaw p₀ K n).toMeasure := by
  rw [← causalLaw_toMeasure_transport_equiv p₀ K K' e₀ eZ hK n]
  simpa [causalHistoryMeasurableEquiv] using MeasureTheory.integral_map_equiv
    (μ := (causalLaw p₀ K n).toMeasure)
    (causalHistoryMeasurableEquiv e₀ eZ n)
    (fun h' => reward ((causalHistoryMeasurableEquiv e₀ eZ n).symm h'))

/-- Source-facing finite-feedback control clause of P-FAC-01.  For every
policy, the transported extension kernels are derived from the original ones;
therefore policy values and their supremum are preserved. -/
theorem causalPolicyValue_transport_bundle
    {Pol : Type uPol}
    (p₀ : PMF H₀)
    (K : Pol → ∀ n, CausalHistory H₀ Z n → PMF Z)
    (K' : Pol → ∀ n, CausalHistory H₀' Z' n → PMF Z')
    (e₀ : H₀ ≃ H₀') (eZ : Z ≃ Z')
    (hK : ∀ π n h,
      K' π n (causalHistoryEquiv e₀ eZ n h) = (K π n h).map eZ)
    (n : ℕ) (reward : CausalHistory H₀ Z n → ℝ) :
    (∀ π,
      policyExpectedValue
          (fun π => (causalLaw (p₀.map e₀) (K' π) n).toMeasure)
          (reward ∘ (causalHistoryMeasurableEquiv e₀ eZ n).symm) π =
        policyExpectedValue
          (fun π => (causalLaw p₀ (K π) n).toMeasure)
          reward π) ∧
      optimalExpectedValue
          (fun π => (causalLaw (p₀.map e₀) (K' π) n).toMeasure)
          (reward ∘ (causalHistoryMeasurableEquiv e₀ eZ n).symm) =
        optimalExpectedValue
          (fun π => (causalLaw p₀ (K π) n).toMeasure)
          reward := by
  apply controlValue_transport_bundle
    (law := fun π => (causalLaw p₀ (K π) n).toMeasure)
    (law' := fun π => (causalLaw (p₀.map e₀) (K' π) n).toMeasure)
    (T := causalHistoryMeasurableEquiv e₀ eZ n)
    (reward := reward)
  intro π
  exact (causalLaw_toMeasure_transport_equiv
    p₀ (K π) (K' π) e₀ eZ (hK π) n).symm

end UEOT.V3.RepresentationCovariance
